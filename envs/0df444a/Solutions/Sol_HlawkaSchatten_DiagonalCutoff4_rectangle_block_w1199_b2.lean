-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1199_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T16:02:56.31581+00:00
-- url     : https://prove2.me/submissions/b3518d3d-82ab-4e57-ac03-069aa2615538

import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_rectangle_majorant
import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.MeanInequalities
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FinCases
import Definitions.Def_HlawkaSchatten_GapComparison
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Basic
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Normalization
import Definitions.Def_HlawkaSchatten_DiagonalCutoff6_Localization
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff6_signed_majorant
/- Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa,
bwdaugherty and Yuxuan Xu. All new numerical implications are checked below. -/
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalConstruction

variable {ι E : Type*} [Fintype ι] [NormedAddCommGroup E]

/-- The coordinate `p`-norm is nonnegative. -/
theorem lpNorm_nonneg (p : ℝ) (x : ι → E) : 0 ≤ lpNorm p x :=
  Real.rpow_nonneg (Finset.sum_nonneg fun _ _ ↦ Real.rpow_nonneg (norm_nonneg _) _) _

/-- The coordinate `p`-norm agrees with the `PiLp` norm. -/
theorem lpNorm_eq_piLp {p : ℝ} (hp : 0 < p) (x : ι → E) :
    lpNorm p x = ‖WithLp.toLp (ENNReal.ofReal p) x‖ := by
  rw [PiLp.norm_eq_sum (by simpa only [ENNReal.toReal_ofReal hp.le] using hp)]
  simp [lpNorm, ENNReal.toReal_ofReal hp.le]

/-- The `p`-norm of zero is zero. -/
@[simp]
theorem lpNorm_zero {p : ℝ} (hp : 0 < p) : lpNorm p (0 : ι → E) = 0 := by
  simp [lpNorm, hp.ne']

/-- The `p`-norm is invariant under negation. -/
@[simp]
theorem lpNorm_neg (p : ℝ) (x : ι → E) : lpNorm p (-x) = lpNorm p x := by
  simp [lpNorm]

/-- Minkowski's inequality for the coordinate `p`-norm. -/
theorem lpNorm_add {p : ℝ} (hp : 1 ≤ p) (x y : ι → E) :
    lpNorm p (x + y) ≤ lpNorm p x + lpNorm p y := by
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  let : Fact (1 ≤ ENNReal.ofReal p) := ⟨ENNReal.one_le_ofReal.mpr hp⟩
  simpa only [lpNorm_eq_piLp hp0, ← WithLp.toLp_add] using
    norm_add_le (WithLp.toLp (ENNReal.ofReal p) x) (WithLp.toLp (ENNReal.ofReal p) y)

/-- Each coordinate norm is at most the `p`-norm. -/
theorem norm_apply_le_lpNorm {p : ℝ} (hp : 1 ≤ p) (x : ι → E) (i : ι) :
    ‖x i‖ ≤ lpNorm p x := by
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  let : Fact (1 ≤ ENNReal.ofReal p) := ⟨ENNReal.one_le_ofReal.mpr hp⟩
  rw [lpNorm_eq_piLp hp0]
  exact PiLp.norm_apply_le (WithLp.toLp (ENNReal.ofReal p) x) i

/-- Raising the `p`-norm to the `p`-th power recovers the sum of `p`-th powers. -/
theorem lpNorm_rpow {p : ℝ} (hp : 0 < p) (x : ι → E) :
    lpNorm p x ^ p = ∑ i, ‖x i‖ ^ p := by
  unfold lpNorm
  rw [← Real.rpow_mul (Finset.sum_nonneg fun i _ ↦ Real.rpow_nonneg (norm_nonneg _) _)]
  rw [one_div_mul_cancel hp.ne', Real.rpow_one]

/-- The `p`-norm vanishes iff the vector is zero. -/
theorem lpNorm_eq_zero_iff {p : ℝ} (hp : 0 < p) (x : ι → E) :
    lpNorm p x = 0 ↔ x = 0 := by
  constructor
  · intro h
    have hs : (∑ i, ‖x i‖ ^ p) = 0 := by
      rw [← lpNorm_rpow hp x, h, Real.zero_rpow hp.ne']
    have hi := (Finset.sum_eq_zero_iff_of_nonneg
      (fun i (_ : i ∈ Finset.univ) ↦ Real.rpow_nonneg (norm_nonneg (x i)) p)).mp hs
    funext i
    exact norm_eq_zero.mp ((Real.rpow_eq_zero (norm_nonneg (x i)) hp.ne').mp
      (hi i (Finset.mem_univ i)))
  · rintro rfl
    exact lpNorm_zero hp

/-- A nonzero vector has strictly positive `p`-norm. -/
theorem lpNorm_pos {p : ℝ} (hp : 0 < p) {x : ι → E} (hx : x ≠ 0) :
    0 < lpNorm p x :=
  lt_of_le_of_ne (lpNorm_nonneg p x) (Ne.symm ((lpNorm_eq_zero_iff hp x).not.mpr hx))

/-- The `p`-norm of a constant vector. -/
theorem lpNorm_const {p : ℝ} (hp : 0 < p) (x : E) :
    lpNorm p (fun _ : ι ↦ x) = (Fintype.card ι : ℝ) ^ (1 / p) * ‖x‖ := by
  unfold lpNorm
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [Real.mul_rpow (Nat.cast_nonneg _) (Real.rpow_nonneg (norm_nonneg _) _),
    ← Real.rpow_mul (norm_nonneg x), mul_one_div_cancel hp.ne', Real.rpow_one]

/-- The `p`-norm scales homogeneously. -/
theorem lpNorm_smul [NormedSpace ℝ E] {p : ℝ} (hp : 0 < p)
    (c : ℝ) (x : ι → E) : lpNorm p (c • x) = |c| * lpNorm p x := by
  unfold lpNorm
  simp only [Pi.smul_apply, norm_smul, Real.norm_eq_abs,
    Real.mul_rpow (abs_nonneg c) (norm_nonneg _), ← Finset.mul_sum]
  rw [Real.mul_rpow (Real.rpow_nonneg (abs_nonneg c) _)
    (Finset.sum_nonneg fun i _ ↦ Real.rpow_nonneg (norm_nonneg (x i)) _),
    ← Real.rpow_mul (abs_nonneg c), mul_one_div_cancel hp.ne', Real.rpow_one]

/-- The coordinate `p`-norm is convex for `p ≥ 1`. -/
theorem convexOn_lpNorm [NormedSpace ℝ E] {p : ℝ} (hp : 1 ≤ p) :
    ConvexOn ℝ Set.univ (lpNorm p : (ι → E) → ℝ) := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a b ha hb _
  have hp0 := zero_lt_one.trans_le hp
  simpa only [lpNorm_smul hp0, abs_of_nonneg ha, abs_of_nonneg hb, smul_eq_mul]
    using lpNorm_add hp (a • x) (b • y)

/-- The coordinate `p`-norm is continuous. -/
theorem continuous_lpNorm {p : ℝ} (hp : 0 < p) :
    Continuous (lpNorm p : (ι → E) → ℝ) := by
  exact (continuous_finsetSum _ fun i _ ↦
    (continuous_apply i).norm.rpow_const (fun _ ↦ Or.inr hp.le)).rpow_const
      (fun _ ↦ Or.inr (one_div_nonneg.mpr hp.le))

/-- The `p`-norm is at most `n^(1/p) * M` when each coordinate norm is at most `M`. -/
theorem lpNorm_le_card_root_mul {p M : ℝ} (hp : 0 < p) (hM : 0 ≤ M)
    (x : ι → E) (hx : ∀ i, ‖x i‖ ≤ M) :
    lpNorm p x ≤ (Fintype.card ι : ℝ) ^ (1 / p) * M := by
  have hsum : (∑ i, ‖x i‖ ^ p) ≤ (Fintype.card ι : ℝ) * M ^ p := by
    calc
      _ ≤ ∑ _ : ι, M ^ p :=
        Finset.sum_le_sum fun i _ ↦ Real.rpow_le_rpow (norm_nonneg _) (hx i) hp.le
      _ = _ := by simp
  have h := Real.rpow_le_rpow
    (Finset.sum_nonneg fun i _ ↦ Real.rpow_nonneg (norm_nonneg (x i)) p)
    hsum (one_div_nonneg.mpr hp.le)
  rw [Real.mul_rpow (Nat.cast_nonneg _) (Real.rpow_nonneg hM _),
    ← Real.rpow_mul hM, mul_one_div_cancel hp.ne', Real.rpow_one] at h
  exact h

/-- The `p`-norm of real coordinates equals the `p`-norm of their complex embeddings. -/
theorem lpNorm_ofReal (p : ℝ) (x : ι → ℝ) :
    lpNorm p (fun i ↦ (x i : ℂ)) = lpNorm p x := by
  simp [lpNorm]

/-- Appending zero coordinates does not change the `p`-norm. -/
theorem lpNorm_fin_append_zero {p : ℝ} (hp : 0 < p) {n : ℕ}
    (x : Fin n → E) (m : ℕ) :
    lpNorm p (Fin.append x (0 : Fin m → E)) = lpNorm p x := by
  simp [lpNorm, Fin.sum_univ_add, hp.ne']

/-- A Hlawka constant in dimension `n` is also admissible in every lower dimension. -/
theorem hasHlawkaConstant_fin_of_le {p C : ℝ} (hp : 0 < p)
    {m n : ℕ} (hn : m ≤ n)
    (hC : HasHlawkaConstant (lpNorm p : (Fin n → E) → ℝ) C) :
    HasHlawkaConstant (lpNorm p : (Fin m → E) → ℝ) C := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  intro x y z
  have h := hC (Fin.append x (0 : Fin k → E))
    (Fin.append y (0 : Fin k → E)) (Fin.append z (0 : Fin k → E))
  have hadd (u v : Fin m → E) :
      Fin.append u (0 : Fin k → E) + Fin.append v (0 : Fin k → E) =
        Fin.append (u + v) (0 : Fin k → E) := by
    ext i
    refine Fin.addCases (fun j ↦ ?_) (fun j ↦ ?_) i <;> simp
  simpa only [tripleGap, pairGapSum, pairGap, hadd, lpNorm_fin_append_zero hp] using h

/-- A Hlawka constant in dimension `n ≥ 3` is admissible in dimension 3. -/
theorem hasHlawkaConstant_fin_three_of_ge {p C : ℝ} (hp : 0 < p)
    {n : ℕ} (hn : 3 ≤ n)
    (hC : HasHlawkaConstant (lpNorm p : (Fin n → E) → ℝ) C) :
    HasHlawkaConstant (lpNorm p : (Fin 3 → E) → ℝ) C :=
  hasHlawkaConstant_fin_of_le hp hn hC

/-- The `p`-norm is invariant under coordinate permutation. -/
theorem lpNorm_comp_equiv {κ : Type*} [Fintype κ]
    (p : ℝ) (x : κ → E) (e : ι ≃ κ) : lpNorm p (x ∘ e) = lpNorm p x := by
  unfold lpNorm
  congr 1
  exact e.sum_comp (fun i ↦ ‖x i‖ ^ p)

/-- The `p`-norm restricted to a subtype equals the full norm when unsupported entries vanish. -/
theorem lpNorm_subtype {p : ℝ} (hp : 0 < p) (x : ι → E)
    (P : ι → Prop) [DecidablePred P] (hx : ∀ i, ¬P i → x i = 0) :
    lpNorm p (fun i : Subtype P ↦ x i.1) = lpNorm p x := by
  unfold lpNorm
  congr 1
  have hzero : (∑ i : {i : ι // ¬P i}, ‖x i.1‖ ^ p) = 0 := by
    exact Finset.sum_eq_zero fun i _ ↦ by simp [hx i.1 i.2, hp.ne']
  rw [← Fintype.sum_subtype_add_sum_subtype P (fun i ↦ ‖x i‖ ^ p), hzero, add_zero]

/-- A Hlawka constant in dimension 3 lifts to any index type of cardinality at most 3. -/
theorem hasHlawkaConstant_of_card_le_three {p C : ℝ} (hp : 0 < p)
    (hcard : Fintype.card ι ≤ 3)
    (hC : HasHlawkaConstant (lpNorm p : (Fin 3 → E) → ℝ) C) :
    HasHlawkaConstant (lpNorm p : (ι → E) → ℝ) C := by
  let e := (Fintype.equivFin ι).symm
  have hf := hasHlawkaConstant_fin_of_le hp hcard hC
  intro x y z
  have h := hf (x ∘ e) (y ∘ e) (z ∘ e)
  have hadd (u v : ι → E) : u ∘ e + v ∘ e = (u + v) ∘ e := rfl
  simpa only [tripleGap, pairGapSum, pairGap, hadd, lpNorm_comp_equiv] using h

/-- The pair deficit is nonneg for `p ≥ 1` by Minkowski. -/
theorem pairGap_nonneg {p : ℝ} (hp : 1 ≤ p) (x y : ι → E) :
    0 ≤ pairGap (lpNorm p) x y := sub_nonneg.mpr (lpNorm_add hp x y)

/-- The sum of pair deficits is nonneg for `p ≥ 1`. -/
theorem pairGapSum_nonneg {p : ℝ} (hp : 1 ≤ p) (x y z : ι → E) :
    0 ≤ pairGapSum (lpNorm p) x y z :=
  add_nonneg (add_nonneg (pairGap_nonneg hp x y) (pairGap_nonneg hp x z))
    (pairGap_nonneg hp y z)

end HlawkaSchatten.DiagonalConstruction
namespace HlawkaSchatten.DiagonalRealBundle
theorem sum3 (f : Fin 3 → ℝ) {i j k : Fin 3} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    ∑ l, f l = f i + f j + f k := by
  rw [Fin.sum_univ_three]
  fin_cases i <;> fin_cases j <;> fin_cases k <;> simp_all <;> ring
theorem lpNorm_eq3 (p : ℝ) (x : Fin 3 → ℝ) {i j k : Fin 3} (hij : i ≠ j) (hik : i ≠ k)
    (hjk : j ≠ k) : lpNorm p x = (|x i| ^ p + |x j| ^ p + |x k| ^ p) ^ (1/p) := by
  unfold lpNorm
  rw [sum3 (fun l ↦ ‖x l‖ ^ p) hij hik hjk]
  simp [Real.norm_eq_abs]
end HlawkaSchatten.DiagonalRealBundle
namespace HlawkaSchatten.DiagonalRealBundle
theorem le_rpow_of_pow_le {x X : ℝ} (hx : 0 ≤ x) (m k : ℕ) (hk : 0 < k)
    (h : X ^ k ≤ x ^ m) : X ≤ x ^ ((m : ℝ) / k) := by
  rcases le_or_gt X 0 with hX | hX
  · exact hX.trans (Real.rpow_nonneg hx _)
  · have e : x ^ ((m : ℝ) / k) = (x ^ m) ^ ((k : ℝ)⁻¹) := by
      rw [div_eq_mul_inv, Real.rpow_mul hx, Real.rpow_natCast]
    rw [e]
    calc X = (X ^ k) ^ ((k : ℝ)⁻¹) := (Real.pow_rpow_inv_natCast hX.le hk.ne').symm
      _ ≤ (x ^ m) ^ ((k : ℝ)⁻¹) := Real.rpow_le_rpow (by positivity) h (by positivity)
theorem rpow_le_of_pow_le {x X : ℝ} (hx : 0 ≤ x) (hX : 0 ≤ X) (m k : ℕ) (hk : 0 < k)
    (h : x ^ m ≤ X ^ k) : x ^ ((m : ℝ) / k) ≤ X := by
  have e : x ^ ((m : ℝ) / k) = (x ^ m) ^ ((k : ℝ)⁻¹) := by
    rw [div_eq_mul_inv, Real.rpow_mul hx, Real.rpow_natCast]
  rw [e]
  calc (x ^ m) ^ ((k : ℝ)⁻¹) ≤ (X ^ k) ^ ((k : ℝ)⁻¹) :=
        Real.rpow_le_rpow (by positivity) h (by positivity)
    _ = X := Real.pow_rpow_inv_natCast hX hk.ne'
end HlawkaSchatten.DiagonalRealBundle

set_option autoImplicit false
namespace HlawkaSchatten.DiagonalCutoff12
open HlawkaSchatten.DiagonalConstruction
open scoped BigOperators

theorem norm_support {ι : Type*} [Fintype ι] {p q : ℝ}
    (hpq : p.HolderConjugate q) (w x : ι → ℝ)
    (hw : (∑ i, |w i| ^ q) ≤ 1) :
    (∑ i, w i*x i) ≤ lpNorm p x := by
  have h := Real.inner_le_Lp_mul_Lq Finset.univ w x hpq.symm
  have hq : 0 ≤ 1/q := hpq.symm.one_div_nonneg
  have hr := Real.rpow_le_rpow
    (Finset.sum_nonneg fun i _ => Real.rpow_nonneg (abs_nonneg (w i)) q) hw hq
  rw [Real.one_rpow] at hr
  have hn := lpNorm_nonneg p x
  have hm := mul_le_mul_of_nonneg_right hr hn
  simpa only [lpNorm, Real.norm_eq_abs, one_mul] using h.trans hm

theorem power12over11_upper {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y)
    (h : x^12 ≤ y^11) : x^(12/11 : ℝ) ≤ y := by
  have hr := Real.rpow_le_rpow (pow_nonneg hx 12) h (by norm_num : (0 : ℝ) ≤ 1/11)
  rw [← Real.rpow_natCast x 12, ← Real.rpow_natCast y 11,
    ← Real.rpow_mul hx, ← Real.rpow_mul hy] at hr
  norm_num at hr ⊢
  exact hr

theorem norm_support12 (w v x : Fin 3 → ℝ)
    (hv : ∀ i, 0 ≤ v i) (hp : ∀ i, |w i|^12 ≤ (v i)^11)
    (hs : (∑ i, v i) ≤ 1) : (∑ i, w i*x i) ≤ lpNorm 12 x := by
  apply norm_support (q := 12/11)
    (Real.holderConjugate_iff.mpr (by norm_num))
  exact (Finset.sum_le_sum fun i _ => power12over11_upper (abs_nonneg _) (hv i) (hp i)).trans hs

theorem power_ratio_upper {x y : ℝ} (m n : ℕ) (hn : 0 < n)
    (hx : 0 ≤ x) (hy : 0 ≤ y) (h : x^m ≤ y^n) :
    x^((m : ℝ)/(n : ℝ)) ≤ y := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hr := Real.rpow_le_rpow (pow_nonneg hx m) h (one_div_nonneg.mpr hn0.le)
  rw [← Real.rpow_natCast x m, ← Real.rpow_natCast y n,
    ← Real.rpow_mul hx, ← Real.rpow_mul hy,
    mul_one_div_cancel hn0.ne', Real.rpow_one] at hr
  simpa only [div_eq_mul_inv, one_div, one_mul] using hr

theorem norm_support_interval {p b : ℝ} (hp : 1 < p) (hb : 1 < b)
    (hpb : p ≤ b) (w x : Fin 3 → ℝ)
    (hw1 : ∀ i, |w i| ≤ 1)
    (hw : (∑ i, |w i|^(b/(b-1))) ≤ 1) :
    (∑ i, w i*x i) ≤ lpNorm p x := by
  have hqp : b/(b-1) ≤ p/(p-1) := by
    apply (div_le_div_iff₀ (by linarith) (by linarith)).mpr
    nlinarith
  have hq0 : 0 ≤ b/(b-1) := div_nonneg (by linarith) (by linarith)
  apply norm_support (q := p/(p-1))
    ((Real.holderConjugate_iff_eq_conjExponent hp).mpr rfl)
  apply le_trans _ hw
  exact Finset.sum_le_sum fun i _ => Real.rpow_le_rpow_of_exponent_ge'
    (abs_nonneg _) (hw1 i) hq0 hqp

theorem norm_support_interval_cert {p b : ℝ} (m n : ℕ) (hn : 0 < n)
    (hp : 1 < p) (hb : 1 < b) (hpb : p ≤ b)
    (hconj : b/(b-1) = (m : ℝ)/(n : ℝ))
    (w v x : Fin 3 → ℝ) (hw1 : ∀ i, |w i| ≤ 1) (hv : ∀ i, 0 ≤ v i)
    (hpowers : ∀ i, |w i|^m ≤ (v i)^n) (hs : (∑ i, v i) ≤ 1) :
    (∑ i, w i*x i) ≤ lpNorm p x := by
  apply norm_support_interval hp hb hpb w x hw1
  rw [hconj]
  exact (Finset.sum_le_sum fun i _ =>
    power_ratio_upper m n hn (abs_nonneg _) (hv i) (hpowers i)).trans hs

end HlawkaSchatten.DiagonalCutoff12


set_option autoImplicit false
set_option maxHeartbeats 4000000
open HlawkaSchatten.DiagonalConstruction
open scoped BigOperators
namespace HlawkaSchatten.DiagonalCutoff6




theorem total_eq (X : Fin 3 → Fin 3 → ℝ) : total X = X 0+X 1+X 2 := by
  simp [total,Fin.sum_univ_three]
theorem pair0 (X : Fin 3 → Fin 3 → ℝ) : pair X 0 = X 1+X 2 := by
  rw [pair,total_eq];abel
theorem pair1 (X : Fin 3 → Fin 3 → ℝ) : pair X 1 = X 0+X 2 := by
  rw [pair,total_eq];abel
theorem pair2 (X : Fin 3 → Fin 3 → ℝ) : pair X 2 = X 0+X 1 := by
  rw [pair,total_eq];abel


theorem oriented_frame {p q k d : ℝ} {X : Fin 3 → Fin 3 → ℝ}
    (h : RelativeOrientedData p q k d X) : Frame p k (3*q) d X := by
  constructor
  · simpa [Fin.sum_univ_three] using h.sum
  · simpa [total_eq] using h.norm_le_total
  · simpa [total_eq] using h.total_one
  · simpa [total_eq] using h.total_cap.le
  · intro i;fin_cases i
    · simpa [pair0] using h.main0
    · simpa [pair1] using h.main1
    · simpa [pair2] using h.main2
  · intro i h';fin_cases i
    · simpa [pair0] using h.max0 h'
    · simpa [pair1] using h.max1 h'
    · simpa [pair2] using h.max2 h'
  · simpa [total_eq,Fin.sum_univ_three,pair0,pair1,pair2] using h.linear_failure

theorem total_relabel (e : Equiv.Perm (Fin 3)) (X : Fin 3 → Fin 3 → ℝ) :
    total (relabel e X) = total X ∘ e := by
  ext h
  simp only [total,Finset.sum_apply,relabel,Function.comp_apply]
  exact Equiv.sum_comp e (fun j => X j (e h))

theorem pair_relabel (e : Equiv.Perm (Fin 3)) (X : Fin 3 → Fin 3 → ℝ) (i : Fin 3) :
    pair (relabel e X) i = pair X (e i) ∘ e := by
  ext h
  simp [pair,total_relabel,relabel]

theorem frame_relabel {p k A d : ℝ} {X : Fin 3 → Fin 3 → ℝ}
    (h : Frame p k A d X) (e : Equiv.Perm (Fin 3)) : Frame p k A d (relabel e X) := by
  have hr (j : Fin 3) : lpNorm p (relabel e X j) = lpNorm p (X (e j)) :=
    lpNorm_comp_equiv p (X (e j)) e
  have ht : lpNorm p (total (relabel e X)) = lpNorm p (total X) := by
    rw [total_relabel,lpNorm_comp_equiv]
  have hp (i : Fin 3) : lpNorm p (pair (relabel e X) i) = lpNorm p (pair X (e i)) := by
    rw [pair_relabel,lpNorm_comp_equiv]
  constructor
  · simp_rw [hr];rw [Equiv.sum_comp e (fun j => lpNorm p (X j))];exact h.sum
  · intro j;rw [hr,ht];exact h.row_total (e j)
  · rw [ht];exact h.total_one
  · rw [ht];exact h.total_cap
  · intro i;rw [hp,pair_relabel];exact h.main (e i)
  · intro i j;rw [pair_relabel];exact h.maximal (e i) (e j)
  · simp_rw [ht,hp];rw [Equiv.sum_comp e (fun i => lpNorm p (pair X i))];exact h.linear_failure

theorem frame_box_of_base {p k A d ell u v w rho : ℝ}
    (base : ∀ X : Fin 3 → Fin 3 → ℝ, Frame p k A d X →
      (∀ i h, i ≠ h → 0 ≤ pair X i h) →
      (∀ i h, i ≠ h → |pair X i h| ≤ rho*pair X i i) →
      -u ≤ X 0 0 ∧ X 0 0 ≤ -ell ∧ v ≤ X 0 1 ∧ X 0 1 ≤ w)
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p k A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ rho*pair X i i) :
    ∀ j i, if j=i then -u ≤ X j i ∧ X j i ≤ -ell else v ≤ X j i ∧ X j i ≤ w := by
  have permuted (e : Equiv.Perm (Fin 3)) :
      -u ≤ X (e 0) (e 0) ∧ X (e 0) (e 0) ≤ -ell ∧
      v ≤ X (e 0) (e 1) ∧ X (e 0) (e 1) ≤ w := by
    apply base (relabel e X) (frame_relabel hX e)
    · intro i j hij
      rw [pair_relabel]
      exact hsign (e i) (e j) (e.injective.ne hij)
    · intro i j hij
      rw [pair_relabel]
      exact hratio (e i) (e j) (e.injective.ne hij)
  have h0 := permuted (Equiv.refl (Fin 3))
  have h01 := permuted (Equiv.swap (0 : Fin 3) 1)
  have h02 := permuted (Equiv.swap (0 : Fin 3) 2)
  have h12 := permuted (Equiv.swap (1 : Fin 3) 2)
  have h120 := permuted ((Equiv.swap (1 : Fin 3) 2).trans (Equiv.swap 0 1))
  have h201 := permuted ((Equiv.swap (0 : Fin 3) 1).trans (Equiv.swap 1 2))
  norm_num [Equiv.swap_apply_def] at h0 h01 h02 h12 h120 h201
  intro j i
  fin_cases j <;> fin_cases i <;> simp only [ite_true,ite_false]
  · exact ⟨h0.1,h0.2.1⟩
  · exact h0.2.2
  · exact h12.2.2
  · exact h01.2.2
  · exact ⟨h01.1,h01.2.1⟩
  · exact h120.2.2
  · exact h201.2.2
  · exact h02.2.2
  · exact ⟨h02.1,h02.2.1⟩

theorem frame_ratio_of_base {p k A d rho R : ℝ}
    (base : ∀ X : Fin 3 → Fin 3 → ℝ, Frame p k A d X →
      (∀ i h, i ≠ h → 0 ≤ pair X i h) →
      (∀ i h, i ≠ h → |pair X i h| ≤ rho*pair X i i) →
      pair X 0 1 ≤ R*pair X 0 0)
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p k A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ rho*pair X i i) :
    ∀ i h, i ≠ h → |pair X i h| ≤ R*pair X i i := by
  have permuted (e : Equiv.Perm (Fin 3)) :
      pair X (e 0) (e 1) ≤ R*pair X (e 0) (e 0) := by
    have hh := base (relabel e X) (frame_relabel hX e)
      (fun i j hij => by rw [pair_relabel];exact hsign (e i) (e j) (e.injective.ne hij))
      (fun i j hij => by rw [pair_relabel];exact hratio (e i) (e j) (e.injective.ne hij))
    simpa only [pair_relabel,Function.comp_apply] using hh
  have h0 := permuted (Equiv.refl (Fin 3))
  have h01 := permuted (Equiv.swap (0 : Fin 3) 1)
  have h02 := permuted (Equiv.swap (0 : Fin 3) 2)
  have h12 := permuted (Equiv.swap (1 : Fin 3) 2)
  have h120 := permuted ((Equiv.swap (1 : Fin 3) 2).trans (Equiv.swap 0 1))
  have h201 := permuted ((Equiv.swap (0 : Fin 3) 1).trans (Equiv.swap 1 2))
  norm_num [Equiv.swap_apply_def] at h0 h01 h02 h12 h120 h201
  intro i j hij
  rw [abs_of_nonneg (hsign i j hij)]
  fin_cases i <;> fin_cases j <;> try contradiction
  all_goals first | exact h0 | exact h01 | exact h02 | exact h12 | exact h120 | exact h201

end HlawkaSchatten.DiagonalCutoff6

set_option autoImplicit false
set_option maxHeartbeats 4000000
open HlawkaSchatten.DiagonalConstruction
open scoped BigOperators
namespace HlawkaSchatten.DiagonalCutoff6


theorem pair_eq_of_distinct (X : Fin 3 → Fin 3 → ℝ) (i j l : Fin 3)
    (hij : i ≠ j) (hil : i ≠ l) (hjl : j ≠ l) : pair X i = X j+X l := by
  fin_cases i <;> fin_cases j <;> fin_cases l <;> try contradiction
  all_goals first
    | exact pair0 X
    | exact (pair0 X).trans (add_comm _ _)
    | exact pair1 X
    | exact (pair1 X).trans (add_comm _ _)
    | exact pair2 X
    | exact (pair2 X).trans (add_comm _ _)

theorem frame_linear_data {p k A d : ℝ} (hp : 1 ≤ p) (X : Fin 3 → Fin 3 → ℝ)
    (h : Frame p k A d X) :
    LinearData k A d X (fun j => lpNorm p (X j))
      (fun i => lpNorm p (pair X i)) (lpNorm p (total X)) := by
  have hn (j : Fin 3) := lpNorm_nonneg p (X j)
  have hs : lpNorm p (X 0)+lpNorm p (X 1)+lpNorm p (X 2)=3 := by
    simpa [Fin.sum_univ_three] using h.sum
  constructor
  · exact hs
  · exact hn
  · exact h.row_total
  · exact h.total_one
  · exact h.total_cap
  · intro j i;exact abs_le.mp (norm_apply_le_lpNorm hp (X j) i)
  · intro i;simpa [total_eq] using abs_le.mp (norm_apply_le_lpNorm hp (total X) i)
  · intro i;exact lpNorm_nonneg p (pair X i)
  · intro i;fin_cases i
    · change lpNorm p (pair X 0) ≤ 3-lpNorm p (X 0)
      rw [pair0];linarith only [lpNorm_add hp (X 1) (X 2),hs]
    · change lpNorm p (pair X 1) ≤ 3-lpNorm p (X 1)
      rw [pair1];linarith only [lpNorm_add hp (X 0) (X 2),hs]
    · change lpNorm p (pair X 2) ≤ 3-lpNorm p (X 2)
      rw [pair2];linarith only [lpNorm_add hp (X 0) (X 1),hs]
  · exact h.main
  · exact h.maximal
  · intro i
    have hh := lpNorm_add hp (total X) (-X i)
    simpa [pair,sub_eq_add_neg] using hh
  · intro i
    have hh := lpNorm_add hp (pair X i) (X i)
    simpa [pair] using hh
  · intro i j l hij hil hjl
    rw [pair_eq_of_distinct X i j l hij hil hjl]
    have hh := lpNorm_add hp (X j+X l) (-X l)
    have he : X j+X l+-X l = X j := by abel
    rw [he,lpNorm_neg] at hh
    linarith
  · simpa [Fin.sum_univ_three] using h.linear_failure

theorem linear_data_bounds {k A d T : ℝ} {X : Fin 3 → Fin 3 → ℝ} {N P : Fin 3 → ℝ}
    (h : LinearData k A d X N P T) (hA : A ≤ 3) :
    (∀ j i, -3 ≤ X j i ∧ X j i ≤ 3) ∧
    (∀ j, -3 ≤ N j ∧ N j ≤ 3) ∧ (∀ i, -3 ≤ P i ∧ P i ≤ 3) ∧ (-3 ≤ T ∧ T ≤ 3) := by
  have hN (j : Fin 3) : 0 ≤ N j ∧ N j ≤ 3 := by
    refine ⟨h.Nnonneg j,?_⟩
    exact ((h.Ntotal j).trans h.Tcap).trans hA
  refine ⟨?_,?_,?_,?_⟩
  · intro j i;have hc := h.coord j i;have hn := hN j;constructor <;> linarith
  · intro j;have hn := hN j;constructor <;> linarith
  · intro i;have hn := hN i;have ht := h.Ptriangle i
    have hz := h.Pnonneg i;constructor <;> linarith
  · constructor <;> linarith only [h.Tone,h.Tcap,hA]

theorem positive_pair_majorant {p a rho alpha : ℝ}
    (hp : 1 ≤ p) (ha : 0 < a) (hap : a ≤ p)
    (hrho : 0 < rho) (hrho1 : rho ≤ 1) (halpha : 0 ≤ alpha)
    (hc1 : 1+rho^a ≤ (1+alpha*rho)^a)
    (hc2 : 1+2*rho^a ≤ (1+2*alpha*rho)^a)
    (X : Fin 3 → Fin 3 → ℝ)
    (hm : ∀ i, 0 ≤ pair X i i)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ rho*pair X i i)
    (i j l : Fin 3) (hij : i ≠ j) (hil : i ≠ l) (hjl : j ≠ l) :
    lpNorm p (pair X i) ≤ pair X i i+alpha*(pair X i j+pair X i l) := by
  rw [HlawkaSchatten.DiagonalRealBundle.lpNorm_eq3 p _ hij hil hjl]
  have hh := signed_majorant hp ha hap hrho hrho1 halpha hc1 hc2 (hm i)
    (hratio i j hij) (hratio i l hil)
  simpa only [abs_of_nonneg (hsign i j hij),abs_of_nonneg (hsign i l hil)] using hh

theorem frame_weaken {p k A d k' A' d' : ℝ} {X : Fin 3 → Fin 3 → ℝ}
    (hp : 1 ≤ p) (h : Frame p k A d X) (hk : k' ≤ k) (hA : A ≤ A') (hd : d' ≤ d) :
    Frame p k' A' d' X := by
  have f := frame_linear_data hp X h
  have hs : (∑ i, lpNorm p (pair X i)) ≤ 6 := by
    rw [Fin.sum_univ_three]
    have hh := f.sum
    linarith only [f.Ptriangle 0,f.Ptriangle 1,f.Ptriangle 2,hh]
  constructor
  · exact h.sum
  · exact h.row_total
  · exact h.total_one
  · exact h.total_cap.trans hA
  · intro i
    exact (mul_le_mul_of_nonneg_right hd (lpNorm_nonneg p (pair X i))).trans (h.main i)
  · exact h.maximal
  · have hh := mul_le_mul_of_nonneg_right hk (sub_nonneg.mpr hs)
    linarith only [hh,h.linear_failure]

end HlawkaSchatten.DiagonalCutoff6
set_option autoImplicit false
set_option maxHeartbeats 4000000
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
namespace HlawkaSchatten.DiagonalCutoff4
theorem frame_box_of_interval_base {p k A d ell u v w rho lo : ℝ}
    (base : ∀ X : Fin 3 → Fin 3 → ℝ, Frame p k A d X →
      (∀ i h, i ≠ h → 0 ≤ pair X i h) →
      (∀ i h, i ≠ h → |pair X i h| ≤ rho*pair X i i) →
      (∀ i h, i ≠ h → lo*pair X i i ≤ pair X i h) →
      -u ≤ X 0 0 ∧ X 0 0 ≤ -ell ∧ v ≤ X 0 1 ∧ X 0 1 ≤ w)
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p k A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ rho*pair X i i)
    (hlower : ∀ i h, i ≠ h → lo*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -u ≤ X j i ∧ X j i ≤ -ell else v ≤ X j i ∧ X j i ≤ w := by
  have permuted (e : Equiv.Perm (Fin 3)) :
      -u ≤ X (e 0) (e 0) ∧ X (e 0) (e 0) ≤ -ell ∧
      v ≤ X (e 0) (e 1) ∧ X (e 0) (e 1) ≤ w := by
    apply base (relabel e X) (frame_relabel hX e)
    · intro i j hij
      rw [pair_relabel]
      exact hsign (e i) (e j) (e.injective.ne hij)
    · intro i j hij
      rw [pair_relabel]
      exact hratio (e i) (e j) (e.injective.ne hij)
    · intro i j hij
      rw [pair_relabel]
      exact hlower (e i) (e j) (e.injective.ne hij)
  have h0 := permuted (Equiv.refl (Fin 3))
  have h01 := permuted (Equiv.swap (0 : Fin 3) 1)
  have h02 := permuted (Equiv.swap (0 : Fin 3) 2)
  have h12 := permuted (Equiv.swap (1 : Fin 3) 2)
  have h120 := permuted ((Equiv.swap (1 : Fin 3) 2).trans (Equiv.swap 0 1))
  have h201 := permuted ((Equiv.swap (0 : Fin 3) 1).trans (Equiv.swap 1 2))
  norm_num [Equiv.swap_apply_def] at h0 h01 h02 h12 h120 h201
  intro j i
  fin_cases j <;> fin_cases i <;> simp only [ite_true,ite_false]
  · exact ⟨h0.1,h0.2.1⟩
  · exact h0.2.2
  · exact h12.2.2
  · exact h01.2.2
  · exact ⟨h01.1,h01.2.1⟩
  · exact h120.2.2
  · exact h201.2.2
  · exact h02.2.2
  · exact ⟨h02.1,h02.2.1⟩

theorem frame_interval_of_base {p k A d rho lo R L : ℝ}
    (base : ∀ X : Fin 3 → Fin 3 → ℝ, Frame p k A d X →
      (∀ i h, i ≠ h → 0 ≤ pair X i h) →
      (∀ i h, i ≠ h → |pair X i h| ≤ rho*pair X i i) →
      (∀ i h, i ≠ h → lo*pair X i i ≤ pair X i h) →
      L*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ R*pair X 0 0)
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p k A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ rho*pair X i i)
    (hlower : ∀ i h, i ≠ h → lo*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → L*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ R*pair X i i := by
  have permuted (e : Equiv.Perm (Fin 3)) :
      L*pair X (e 0) (e 0) ≤ pair X (e 0) (e 1) ∧
        pair X (e 0) (e 1) ≤ R*pair X (e 0) (e 0) := by
    have hh := base (relabel e X) (frame_relabel hX e)
      (fun i j hij => by rw [pair_relabel];exact hsign (e i) (e j) (e.injective.ne hij))
      (fun i j hij => by rw [pair_relabel];exact hratio (e i) (e j) (e.injective.ne hij))
      (fun i j hij => by rw [pair_relabel];exact hlower (e i) (e j) (e.injective.ne hij))
    simpa only [pair_relabel,Function.comp_apply] using hh
  have h0 := permuted (Equiv.refl (Fin 3))
  have h01 := permuted (Equiv.swap (0 : Fin 3) 1)
  have h02 := permuted (Equiv.swap (0 : Fin 3) 2)
  have h12 := permuted (Equiv.swap (1 : Fin 3) 2)
  have h120 := permuted ((Equiv.swap (1 : Fin 3) 2).trans (Equiv.swap 0 1))
  have h201 := permuted ((Equiv.swap (0 : Fin 3) 1).trans (Equiv.swap 1 2))
  norm_num [Equiv.swap_apply_def] at h0 h01 h02 h12 h120 h201
  intro i j hij
  rw [abs_of_nonneg (hsign i j hij)]
  fin_cases i <;> fin_cases j <;> try contradiction
  all_goals first | exact h0 | exact h01 | exact h02 | exact h12 | exact h120 | exact h201


theorem rectangle_pair_majorant {p a lo hi c alpha : ℝ}
    (hp : 1 ≤ p) (ha : 0 < a) (hap : a ≤ p)
    (hlo : 0 ≤ lo) (hlohi : lo < hi) (hhi : hi ≤ 1) (halpha : 0 ≤ alpha)
    (hc : 1 ≤ c+2*alpha*lo)
    (hcorner00 : 1+2*lo^a ≤ (c+2*alpha*lo)^a)
    (hcorner10 : 1+hi^a+lo^a ≤ (c+alpha*(hi+lo))^a)
    (hcorner11 : 1+2*hi^a ≤ (c+2*alpha*hi)^a)
    (X : Fin 3 → Fin 3 → ℝ)
    (hmain : ∀ i, 0 ≤ pair X i i)
    (hlower : ∀ i h, i ≠ h → lo*pair X i i ≤ pair X i h)
    (hupper : ∀ i h, i ≠ h → |pair X i h| ≤ hi*pair X i i)
    (i j l : Fin 3) (hij : i ≠ j) (hil : i ≠ l) (hjl : j ≠ l) :
    lpNorm p (pair X i) ≤ c*pair X i i+alpha*(pair X i j+pair X i l) := by
  have hh := rectangle_majorant hp ha hap hlo hlohi hhi halpha hc hcorner00 hcorner10 hcorner11
    (hmain i) (hlower i j hij) ((le_abs_self _).trans (hupper i j hij))
    (hlower i l hil) ((le_abs_self _).trans (hupper i l hil))
  have he : lpNorm p (pair X i) =
      (|pair X i i|^p+|pair X i j|^p+|pair X i l|^p)^(1/p) := by
    simp only [lpNorm,Real.norm_eq_abs]
    congr 1
    fin_cases i <;> fin_cases j <;> fin_cases l <;> try contradiction
    all_goals simp [Fin.sum_univ_three] <;> ring
  rw [he]
  exact hh

end HlawkaSchatten.DiagonalCutoff4

set_option autoImplicit false
namespace HlawkaSchatten.DiagonalCutoff4

theorem rational_powers_le (a b c d m n : ℕ) (hb : 0 < b) (hd : 0 < d)
    (h : a^m*d^n ≤ c^n*b^m) :
    ((a : ℝ)/b)^m ≤ ((c : ℝ)/d)^n := by
  rw [div_pow,div_pow]
  have hb' : (0 : ℝ) < b := by exact_mod_cast hb
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  apply (div_le_div_iff₀ (pow_pos hb' m) (pow_pos hd' n)).mpr
  exact_mod_cast h

theorem rectangle_budgets {a lo hi c alpha pl ph : ℝ}
    (hl : lo^a ≤ pl) (hh : hi^a ≤ ph)
    (h00 : 1+2*pl ≤ (c+2*alpha*lo)^a)
    (h10 : 1+ph+pl ≤ (c+alpha*(hi+lo))^a)
    (h11 : 1+2*ph ≤ (c+2*alpha*hi)^a) :
    1+2*lo^a ≤ (c+2*alpha*lo)^a ∧
    1+hi^a+lo^a ≤ (c+alpha*(hi+lo))^a ∧
    1+2*hi^a ≤ (c+2*alpha*hi)^a := by
  constructor
  · linarith only [hl,h00]
  constructor
  · linarith only [hl,hh,h10]
  · linarith only [hh,h11]

theorem sum_two_bounds {x y X Y z : ℝ} (hx : x ≤ X) (hy : y ≤ Y)
    (hz : X+2*Y ≤ z) : x+2*y ≤ z := by
  linarith only [hx,hy,hz]

theorem three_bounds {x X : ℝ} (hx : x ≤ X) (hX : 3*X ≤ 1) : x+x+x ≤ 1 := by
  linarith only [hx,hX]

end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1199_s6_0 (p : ℝ) (hpa : (8391/2048 : ℝ) ≤ p) (hpb : p ≤ (1049/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-2139901429/10000000000 : ℝ)*x 0 + (539224273/1000000000 : ℝ)*x 1 + (5266379247/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2139901429/10000000000 : ℝ)^1049 ≤ (1300853312391/10000000000000 : ℝ)^793 := by
    have hnat : (2139901429 : ℕ)^1049*10000000000000^793 ≤ 1300853312391^793*10000000000^1049 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2139901429 10000000000 1300853312391 10000000000000 1049 793 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (539224273/1000000000 : ℝ)^1049 ≤ (44175144327367/100000000000000 : ℝ)^793 := by
    have hnat : (539224273 : ℕ)^1049*100000000000000^793 ≤ 44175144327367^793*1000000000^1049 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      539224273 1000000000 44175144327367 100000000000000 1049 793 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5266379247/10000000000 : ℝ)^1049 ≤ (42816322533413/100000000000000 : ℝ)^793 := by
    have hnat : (5266379247 : ℕ)^1049*100000000000000^793 ≤ 42816322533413^793*10000000000^1049 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266379247 10000000000 42816322533413 100000000000000 1049 793 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1049/256 : ℝ)) 1049 793 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2139901429/10000000000 : ℝ), (539224273/1000000000 : ℝ), (5266379247/10000000000 : ℝ)] ![(1300853312391/10000000000000 : ℝ), (44175144327367/100000000000000 : ℝ), (42816322533413/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2139901429/10000000000 : ℝ)|^1049 ≤ (1300853312391/10000000000000 : ℝ)^793
        have hw : |(-2139901429/10000000000 : ℝ)|=(2139901429/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(539224273/1000000000 : ℝ)|^1049 ≤ (44175144327367/100000000000000 : ℝ)^793
        have hw : |(539224273/1000000000 : ℝ)|=(539224273/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5266379247/10000000000 : ℝ)|^1049 ≤ (42816322533413/100000000000000 : ℝ)^793
        have hw : |(5266379247/10000000000 : ℝ)|=(5266379247/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1199_s6_1 (p : ℝ) (hpa : (8391/2048 : ℝ) ≤ p) (hpb : p ≤ (1049/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5344584007/10000000000 : ℝ)*x 0 + (-550932777/2500000000 : ℝ)*x 1 + (1053275857/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344584007/10000000000 : ℝ)^1049 ≤ (43659402938231/100000000000000 : ℝ)^793 := by
    have hnat : (5344584007 : ℕ)^1049*100000000000000^793 ≤ 43659402938231^793*10000000000^1049 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344584007 10000000000 43659402938231 100000000000000 1049 793 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (550932777/2500000000 : ℝ)^1049 ≤ (6762137053467/50000000000000 : ℝ)^793 := by
    have hnat : (550932777 : ℕ)^1049*50000000000000^793 ≤ 6762137053467^793*2500000000^1049 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      550932777 2500000000 6762137053467 50000000000000 1049 793 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1053275857/2000000000 : ℝ)^1049 ≤ (42816322942093/100000000000000 : ℝ)^793 := by
    have hnat : (1053275857 : ℕ)^1049*100000000000000^793 ≤ 42816322942093^793*2000000000^1049 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1053275857 2000000000 42816322942093 100000000000000 1049 793 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1049/256 : ℝ)) 1049 793 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344584007/10000000000 : ℝ), (-550932777/2500000000 : ℝ), (1053275857/2000000000 : ℝ)] ![(43659402938231/100000000000000 : ℝ), (6762137053467/50000000000000 : ℝ), (42816322942093/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344584007/10000000000 : ℝ)|^1049 ≤ (43659402938231/100000000000000 : ℝ)^793
        have hw : |(5344584007/10000000000 : ℝ)|=(5344584007/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-550932777/2500000000 : ℝ)|^1049 ≤ (6762137053467/50000000000000 : ℝ)^793
        have hw : |(-550932777/2500000000 : ℝ)|=(550932777/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1053275857/2000000000 : ℝ)|^1049 ≤ (42816322942093/100000000000000 : ℝ)^793
        have hw : |(1053275857/2000000000 : ℝ)|=(1053275857/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1199_s6_2 (p : ℝ) (hpa : (8391/2048 : ℝ) ≤ p) (hpb : p ≤ (1049/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5344584073/10000000000 : ℝ)*x 0 + (2633189579/5000000000 : ℝ)*x 1 + (-2203731189/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344584073/10000000000 : ℝ)^1049 ≤ (43659403651429/100000000000000 : ℝ)^793 := by
    have hnat : (5344584073 : ℕ)^1049*100000000000000^793 ≤ 43659403651429^793*10000000000^1049 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344584073 10000000000 43659403651429 100000000000000 1049 793 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2633189579/5000000000 : ℝ)^1049 ≤ (21408160788121/50000000000000 : ℝ)^793 := by
    have hnat : (2633189579 : ℕ)^1049*50000000000000^793 ≤ 21408160788121^793*5000000000^1049 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633189579 5000000000 21408160788121 50000000000000 1049 793 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2203731189/10000000000 : ℝ)^1049 ≤ (2704854952901/20000000000000 : ℝ)^793 := by
    have hnat : (2203731189 : ℕ)^1049*20000000000000^793 ≤ 2704854952901^793*10000000000^1049 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2203731189 10000000000 2704854952901 20000000000000 1049 793 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1049/256 : ℝ)) 1049 793 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344584073/10000000000 : ℝ), (2633189579/5000000000 : ℝ), (-2203731189/10000000000 : ℝ)] ![(43659403651429/100000000000000 : ℝ), (21408160788121/50000000000000 : ℝ), (2704854952901/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344584073/10000000000 : ℝ)|^1049 ≤ (43659403651429/100000000000000 : ℝ)^793
        have hw : |(5344584073/10000000000 : ℝ)|=(5344584073/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2633189579/5000000000 : ℝ)|^1049 ≤ (21408160788121/50000000000000 : ℝ)^793
        have hw : |(2633189579/5000000000 : ℝ)|=(2633189579/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2203731189/10000000000 : ℝ)|^1049 ≤ (2704854952901/20000000000000 : ℝ)^793
        have hw : |(-2203731189/10000000000 : ℝ)|=(2203731189/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1199_s6_3 (p : ℝ) (hpa : (8391/2048 : ℝ) ≤ p) (hpb : p ≤ (1049/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2178346169/5000000000 : ℝ)*x 0 + (66123373/156250000 : ℝ)*x 1 + (4485101007/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2178346169/5000000000 : ℝ)^1049 ≤ (33317147990297/100000000000000 : ℝ)^793 := by
    have hnat : (2178346169 : ℕ)^1049*100000000000000^793 ≤ 33317147990297^793*5000000000^1049 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2178346169 5000000000 33317147990297 100000000000000 1049 793 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (66123373/156250000 : ℝ)^1049 ≤ (32060569441553/100000000000000 : ℝ)^793 := by
    have hnat : (66123373 : ℕ)^1049*100000000000000^793 ≤ 32060569441553^793*156250000^1049 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      66123373 156250000 32060569441553 100000000000000 1049 793 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4485101007/10000000000 : ℝ)^1049 ≤ (34622282555473/100000000000000 : ℝ)^793 := by
    have hnat : (4485101007 : ℕ)^1049*100000000000000^793 ≤ 34622282555473^793*10000000000^1049 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4485101007 10000000000 34622282555473 100000000000000 1049 793 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1049/256 : ℝ)) 1049 793 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2178346169/5000000000 : ℝ), (66123373/156250000 : ℝ), (4485101007/10000000000 : ℝ)] ![(33317147990297/100000000000000 : ℝ), (32060569441553/100000000000000 : ℝ), (34622282555473/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2178346169/5000000000 : ℝ)|^1049 ≤ (33317147990297/100000000000000 : ℝ)^793
        have hw : |(2178346169/5000000000 : ℝ)|=(2178346169/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(66123373/156250000 : ℝ)|^1049 ≤ (32060569441553/100000000000000 : ℝ)^793
        have hw : |(66123373/156250000 : ℝ)|=(66123373/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4485101007/10000000000 : ℝ)|^1049 ≤ (34622282555473/100000000000000 : ℝ)^793
        have hw : |(4485101007/10000000000 : ℝ)|=(4485101007/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1199_s6_4 (p : ℝ) (hpa : (8391/2048 : ℝ) ≤ p) (hpb : p ≤ (1049/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-2139906289/10000000000 : ℝ)*x 0 + (5266697253/10000000000 : ℝ)*x 1 + (5391923527/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2139906289/10000000000 : ℝ)^1049 ≤ (3252143051399/25000000000000 : ℝ)^793 := by
    have hnat : (2139906289 : ℕ)^1049*25000000000000^793 ≤ 3252143051399^793*10000000000^1049 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2139906289 10000000000 3252143051399 25000000000000 1049 793 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5266697253/10000000000 : ℝ)^1049 ≤ (21409871317793/50000000000000 : ℝ)^793 := by
    have hnat : (5266697253 : ℕ)^1049*50000000000000^793 ≤ 21409871317793^793*10000000000^1049 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266697253 10000000000 21409871317793 50000000000000 1049 793 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5391923527/10000000000 : ℝ)^1049 ≤ (44171685143403/100000000000000 : ℝ)^793 := by
    have hnat : (5391923527 : ℕ)^1049*100000000000000^793 ≤ 44171685143403^793*10000000000^1049 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5391923527 10000000000 44171685143403 100000000000000 1049 793 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1049/256 : ℝ)) 1049 793 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2139906289/10000000000 : ℝ), (5266697253/10000000000 : ℝ), (5391923527/10000000000 : ℝ)] ![(3252143051399/25000000000000 : ℝ), (21409871317793/50000000000000 : ℝ), (44171685143403/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2139906289/10000000000 : ℝ)|^1049 ≤ (3252143051399/25000000000000 : ℝ)^793
        have hw : |(-2139906289/10000000000 : ℝ)|=(2139906289/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5266697253/10000000000 : ℝ)|^1049 ≤ (21409871317793/50000000000000 : ℝ)^793
        have hw : |(5266697253/10000000000 : ℝ)|=(5266697253/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5391923527/10000000000 : ℝ)|^1049 ≤ (44171685143403/100000000000000 : ℝ)^793
        have hw : |(5391923527/10000000000 : ℝ)|=(5391923527/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1199_s6_5 (p : ℝ) (hpa : (8391/2048 : ℝ) ≤ p) (hpb : p ≤ (1049/256 : ℝ)) (x : Fin 3 → ℝ) :
    (1328141123/2500000000 : ℝ)*x 0 + (-415637357/2000000000 : ℝ)*x 1 + (1078384709/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1328141123/2500000000 : ℝ)^1049 ≤ (43313734133389/100000000000000 : ℝ)^793 := by
    have hnat : (1328141123 : ℕ)^1049*100000000000000^793 ≤ 43313734133389^793*2500000000^1049 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1328141123 2500000000 43313734133389 100000000000000 1049 793 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (415637357/2000000000 : ℝ)^1049 ≤ (12514580510777/100000000000000 : ℝ)^793 := by
    have hnat : (415637357 : ℕ)^1049*100000000000000^793 ≤ 12514580510777^793*2000000000^1049 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      415637357 2000000000 12514580510777 100000000000000 1049 793 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1078384709/2000000000 : ℝ)^1049 ≤ (22085842669233/50000000000000 : ℝ)^793 := by
    have hnat : (1078384709 : ℕ)^1049*50000000000000^793 ≤ 22085842669233^793*2000000000^1049 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078384709 2000000000 22085842669233 50000000000000 1049 793 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1049/256 : ℝ)) 1049 793 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1328141123/2500000000 : ℝ), (-415637357/2000000000 : ℝ), (1078384709/2000000000 : ℝ)] ![(43313734133389/100000000000000 : ℝ), (12514580510777/100000000000000 : ℝ), (22085842669233/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1328141123/2500000000 : ℝ)|^1049 ≤ (43313734133389/100000000000000 : ℝ)^793
        have hw : |(1328141123/2500000000 : ℝ)|=(1328141123/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-415637357/2000000000 : ℝ)|^1049 ≤ (12514580510777/100000000000000 : ℝ)^793
        have hw : |(-415637357/2000000000 : ℝ)|=(415637357/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1078384709/2000000000 : ℝ)|^1049 ≤ (22085842669233/50000000000000 : ℝ)^793
        have hw : |(1078384709/2000000000 : ℝ)|=(1078384709/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1199_s6_6 (p : ℝ) (hpa : (8391/2048 : ℝ) ≤ p) (hpb : p ≤ (1049/256 : ℝ)) (x : Fin 3 → ℝ) :
    (132814113/250000000 : ℝ)*x 0 + (5391923499/10000000000 : ℝ)*x 1 + (-2078186809/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (132814113/250000000 : ℝ)^1049 ≤ (43313734435371/100000000000000 : ℝ)^793 := by
    have hnat : (132814113 : ℕ)^1049*100000000000000^793 ≤ 43313734435371^793*250000000^1049 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      132814113 250000000 43313734435371 100000000000000 1049 793 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5391923499/10000000000 : ℝ)^1049 ≤ (44171684839971/100000000000000 : ℝ)^793 := by
    have hnat : (5391923499 : ℕ)^1049*100000000000000^793 ≤ 44171684839971^793*10000000000^1049 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5391923499 10000000000 44171684839971 100000000000000 1049 793 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2078186809/10000000000 : ℝ)^1049 ≤ (6257290350979/50000000000000 : ℝ)^793 := by
    have hnat : (2078186809 : ℕ)^1049*50000000000000^793 ≤ 6257290350979^793*10000000000^1049 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2078186809 10000000000 6257290350979 50000000000000 1049 793 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1049/256 : ℝ)) 1049 793 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(132814113/250000000 : ℝ), (5391923499/10000000000 : ℝ), (-2078186809/10000000000 : ℝ)] ![(43313734435371/100000000000000 : ℝ), (44171684839971/100000000000000 : ℝ), (6257290350979/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(132814113/250000000 : ℝ)|^1049 ≤ (43313734435371/100000000000000 : ℝ)^793
        have hw : |(132814113/250000000 : ℝ)|=(132814113/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5391923499/10000000000 : ℝ)|^1049 ≤ (44171684839971/100000000000000 : ℝ)^793
        have hw : |(5391923499/10000000000 : ℝ)|=(5391923499/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2078186809/10000000000 : ℝ)|^1049 ≤ (6257290350979/50000000000000 : ℝ)^793
        have hw : |(-2078186809/10000000000 : ℝ)|=(2078186809/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1199_s6_7 (p : ℝ) (hpa : (8391/2048 : ℝ) ≤ p) (hpb : p ≤ (1049/256 : ℝ)) (x : Fin 3 → ℝ) :
    (1089175461/2500000000 : ℝ)*x 0 + (4484461089/10000000000 : ℝ)*x 1 + (4232538281/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1089175461/2500000000 : ℝ)^1049 ≤ (16658622077001/50000000000000 : ℝ)^793 := by
    have hnat : (1089175461 : ℕ)^1049*50000000000000^793 ≤ 16658622077001^793*2500000000^1049 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1089175461 2500000000 16658622077001 50000000000000 1049 793 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4484461089/10000000000 : ℝ)^1049 ≤ (3461574824007/10000000000000 : ℝ)^793 := by
    have hnat : (4484461089 : ℕ)^1049*10000000000000^793 ≤ 3461574824007^793*10000000000^1049 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4484461089 10000000000 3461574824007 10000000000000 1049 793 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4232538281/10000000000 : ℝ)^1049 ≤ (32067007587493/100000000000000 : ℝ)^793 := by
    have hnat : (4232538281 : ℕ)^1049*100000000000000^793 ≤ 32067007587493^793*10000000000^1049 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4232538281 10000000000 32067007587493 100000000000000 1049 793 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1049/256 : ℝ)) 1049 793 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1089175461/2500000000 : ℝ), (4484461089/10000000000 : ℝ), (4232538281/10000000000 : ℝ)] ![(16658622077001/50000000000000 : ℝ), (3461574824007/10000000000000 : ℝ), (32067007587493/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1089175461/2500000000 : ℝ)|^1049 ≤ (16658622077001/50000000000000 : ℝ)^793
        have hw : |(1089175461/2500000000 : ℝ)|=(1089175461/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4484461089/10000000000 : ℝ)|^1049 ≤ (3461574824007/10000000000000 : ℝ)^793
        have hw : |(4484461089/10000000000 : ℝ)|=(4484461089/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4232538281/10000000000 : ℝ)|^1049 ≤ (32067007587493/100000000000000 : ℝ)^793
        have hw : |(4232538281/10000000000 : ℝ)|=(4232538281/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1199_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8391/2048 : ℝ) ≤ p) (hpb : p ≤ (1049/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9411691/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (441/3125 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2849/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (11421/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14087/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (441/3125 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2849/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (441/3125 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2849/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (441/3125 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2849/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (441/3125 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2849/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (441/3125 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2849/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (441/3125 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2849/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hlower 2 1 (by decide)
  have fm0 := f.main 0
  simp only [pair0,pair1,pair2,Pi.add_apply] at fm0
  have fx01 := abs_le.mp (f.maximal 0 1)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx01
  have fx02 := abs_le.mp (f.maximal 0 2)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx02
  have fm1 := f.main 1
  simp only [pair0,pair1,pair2,Pi.add_apply] at fm1
  have fx10 := abs_le.mp (f.maximal 1 0)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx10
  have fx12 := abs_le.mp (f.maximal 1 2)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx12
  have fm2 := f.main 2
  simp only [pair0,pair1,pair2,Pi.add_apply] at fm2
  have fx20 := abs_le.mp (f.maximal 2 0)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx20
  have fx21 := abs_le.mp (f.maximal 2 1)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx21
  have base19 : ((1 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 2).2]
  have base23 : ((1 : ℝ)*X 2 1+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 1).2]
  have base65 : ((1 : ℝ)*X 0 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 0).2]
  have base66 : ((-1 : ℝ)*X 0 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 0).1]
  have base67 : ((1 : ℝ)*X 0 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 1).2]
  have base68 : ((-1 : ℝ)*X 0 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 1).1]
  have base69 : ((1 : ℝ)*X 0 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 2).2]
  have base70 : ((-1 : ℝ)*X 0 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 2).1]
  have base71 : ((1 : ℝ)*X 1 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 0).2]
  have base72 : ((-1 : ℝ)*X 1 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 0).1]
  have base73 : ((1 : ℝ)*X 1 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 1).2]
  have base74 : ((-1 : ℝ)*X 1 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 1).1]
  have base75 : ((1 : ℝ)*X 1 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 2).2]
  have base76 : ((-1 : ℝ)*X 1 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 2).1]
  have base77 : ((1 : ℝ)*X 2 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 0).2]
  have base78 : ((-1 : ℝ)*X 2 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 0).1]
  have base79 : ((1 : ℝ)*X 2 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 1).2]
  have base80 : ((-1 : ℝ)*X 2 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 1).1]
  have base81 : ((1 : ℝ)*X 2 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 2).2]
  have base82 : ((-1 : ℝ)*X 2 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 2).1]
  have base83 : ((1 : ℝ)*N 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 0).2]
  have base84 : ((-1 : ℝ)*N 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 0).1]
  have base85 : ((1 : ℝ)*N 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 1).2]
  have base86 : ((-1 : ℝ)*N 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 1).1]
  have base87 : ((1 : ℝ)*N 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 2).2]
  have base88 : ((-1 : ℝ)*N 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 2).1]
  have base89 : ((1 : ℝ)*P 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 0).2]
  have base90 : ((-1 : ℝ)*P 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 0).1]
  have base91 : ((1 : ℝ)*P 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 1).2]
  have base92 : ((-1 : ℝ)*P 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 1).1]
  have base93 : ((1 : ℝ)*P 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 2).2]
  have base94 : ((-1 : ℝ)*P 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 2).1]
  have base95 : ((1 : ℝ)*T) ≤ (3 : ℝ) := by
    linarith only [bounds.2.2.2.2]
  have base96 : ((-1 : ℝ)*T) ≤ (3 : ℝ) := by
    linarith only [bounds.2.2.2.1]
  have hpowlo : (2849/25000 : ℝ) ^ (8391/2048 : ℝ) ≤ (3414257888988493/25000000000000000000 : ℝ) := by
    have hpowers : (2849/25000 : ℝ)^8391 ≤ (3414257888988493/25000000000000000000 : ℝ)^2048 := by
      have hnat : (2849 : ℕ)^8391*25000000000000000000^2048 ≤ 3414257888988493^2048*25000^8391 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2849 25000 3414257888988493 25000000000000000000 8391 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2849/25000 : ℝ)) (X := (3414257888988493/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8391 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (441/3125 : ℝ) ^ (8391/2048 : ℝ) ≤ (32788497776678533/100000000000000000000 : ℝ) := by
    have hpowers : (441/3125 : ℝ)^8391 ≤ (32788497776678533/100000000000000000000 : ℝ)^2048 := by
      have hnat : (441 : ℕ)^8391*100000000000000000000^2048 ≤ 32788497776678533^2048*3125^8391 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        441 3125 32788497776678533 100000000000000000000 8391 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (441/3125 : ℝ)) (X := (32788497776678533/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8391 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (12503414257888988493/12500000000000000000 : ℝ) ≤ (10000666588334589/10000000000000000 : ℝ) ^ (8391/2048 : ℝ) := by
    have hpowers : (12503414257888988493/12500000000000000000 : ℝ)^2048 ≤ (10000666588334589/10000000000000000 : ℝ)^8391 := by
      have hnat : (12503414257888988493 : ℕ)^2048*10000000000000000^8391 ≤ 10000666588334589^8391*12500000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12503414257888988493 12500000000000000000 10000666588334589 10000000000000000 2048 8391 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000666588334589/10000000000000000 : ℝ)) (X := (12503414257888988493/12500000000000000000 : ℝ)) (by norm_num) 8391 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (20009289105866526501/20000000000000000000 : ℝ) ≤ (5000566700932219/5000000000000000 : ℝ) ^ (8391/2048 : ℝ) := by
    have hpowers : (20009289105866526501/20000000000000000000 : ℝ)^2048 ≤ (5000566700932219/5000000000000000 : ℝ)^8391 := by
      have hnat : (20009289105866526501 : ℕ)^2048*5000000000000000^8391 ≤ 5000566700932219^8391*20000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20009289105866526501 20000000000000000000 5000566700932219 5000000000000000 2048 8391 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000566700932219/5000000000000000 : ℝ)) (X := (20009289105866526501/20000000000000000000 : ℝ)) (by norm_num) 8391 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50032788497776678533/50000000000000000000 : ℝ) ≤ (10001600215394287/10000000000000000 : ℝ) ^ (8391/2048 : ℝ) := by
    have hpowers : (50032788497776678533/50000000000000000000 : ℝ)^2048 ≤ (10001600215394287/10000000000000000 : ℝ)^8391 := by
      have hnat : (50032788497776678533 : ℕ)^2048*10000000000000000^8391 ≤ 10001600215394287^8391*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50032788497776678533 50000000000000000000 10001600215394287 10000000000000000 2048 8391 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001600215394287/10000000000000000 : ℝ)) (X := (50032788497776678533/50000000000000000000 : ℝ)) (by norm_num) 8391 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(3414257888988493/25000000000000000000 : ℝ) ≤ ((9996749204692351/10000000000000000 : ℝ)+2*(4812510617/2800000000000 : ℝ)*(2849/25000 : ℝ))^(8391/2048 : ℝ) := by
    rw [show (9996749204692351/10000000000000000 : ℝ)+2*(4812510617/2800000000000 : ℝ)*(2849/25000 : ℝ)=(10000666588334589/10000000000000000 : ℝ) by norm_num, show 1+2*(3414257888988493/25000000000000000000 : ℝ)=(12503414257888988493/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(32788497776678533/100000000000000000000 : ℝ)+(3414257888988493/25000000000000000000 : ℝ) ≤ ((9996749204692351/10000000000000000 : ℝ)+(4812510617/2800000000000 : ℝ)*((441/3125 : ℝ)+(2849/25000 : ℝ)))^(8391/2048 : ℝ) := by
    rw [show (9996749204692351/10000000000000000 : ℝ)+(4812510617/2800000000000 : ℝ)*((441/3125 : ℝ)+(2849/25000 : ℝ))=(5000566700932219/5000000000000000 : ℝ) by norm_num, show 1+(32788497776678533/100000000000000000000 : ℝ)+(3414257888988493/25000000000000000000 : ℝ)=(20009289105866526501/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(32788497776678533/100000000000000000000 : ℝ) ≤ ((9996749204692351/10000000000000000 : ℝ)+2*(4812510617/2800000000000 : ℝ)*(441/3125 : ℝ))^(8391/2048 : ℝ) := by
    rw [show (9996749204692351/10000000000000000 : ℝ)+2*(4812510617/2800000000000 : ℝ)*(441/3125 : ℝ)=(10001600215394287/10000000000000000 : ℝ) by norm_num, show 1+2*(32788497776678533/100000000000000000000 : ℝ)=(50032788497776678533/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (9996749204692351/10000000000000000 : ℝ)*(X 1 0+X 2 0)+(4812510617/2800000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8391/2048 : ℝ)) (lo := (2849/25000 : ℝ)) (hi := (441/3125 : ℝ)) (c := (9996749204692351/10000000000000000 : ℝ)) (alpha := (4812510617/2800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (9996749204692351/10000000000000000 : ℝ)*(X 0 1+X 2 1)+(4812510617/2800000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8391/2048 : ℝ)) (lo := (2849/25000 : ℝ)) (hi := (441/3125 : ℝ)) (c := (9996749204692351/10000000000000000 : ℝ)) (alpha := (4812510617/2800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (9996749204692351/10000000000000000 : ℝ)*(X 0 2+X 1 2)+(4812510617/2800000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8391/2048 : ℝ)) (lo := (2849/25000 : ℝ)) (hi := (441/3125 : ℝ)) (c := (9996749204692351/10000000000000000 : ℝ)) (alpha := (4812510617/2800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2139901429/10000000000 : ℝ)*X 0 0+(539224273/1000000000 : ℝ)*X 0 1+(5266379247/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1199_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5344584007/10000000000 : ℝ)*X 1 0+(-550932777/2500000000 : ℝ)*X 1 1+(1053275857/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1199_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5344584073/10000000000 : ℝ)*X 2 0+(2633189579/5000000000 : ℝ)*X 2 1+(-2203731189/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1199_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2178346169/5000000000 : ℝ)*X 0 0+(66123373/156250000 : ℝ)*X 0 1+(4485101007/10000000000 : ℝ)*X 0 2+(2178346169/5000000000 : ℝ)*X 1 0+(66123373/156250000 : ℝ)*X 1 1+(4485101007/10000000000 : ℝ)*X 1 2+(2178346169/5000000000 : ℝ)*X 2 0+(66123373/156250000 : ℝ)*X 2 1+(4485101007/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1199_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2139906289/10000000000 : ℝ)*X 0 0+(5266697253/10000000000 : ℝ)*X 0 1+(5391923527/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1199_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1328141123/2500000000 : ℝ)*X 1 0+(-415637357/2000000000 : ℝ)*X 1 1+(1078384709/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1199_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((132814113/250000000 : ℝ)*X 2 0+(5391923499/10000000000 : ℝ)*X 2 1+(-2078186809/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1199_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1089175461/2500000000 : ℝ)*X 0 0+(4484461089/10000000000 : ℝ)*X 0 1+(4232538281/10000000000 : ℝ)*X 0 2+(1089175461/2500000000 : ℝ)*X 1 0+(4484461089/10000000000 : ℝ)*X 1 1+(4232538281/10000000000 : ℝ)*X 1 2+(1089175461/2500000000 : ℝ)*X 2 0+(4484461089/10000000000 : ℝ)*X 2 1+(4232538281/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1199_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (399310298897687429253/140000000000000000000000000 : ℝ) := by norm_num
    linear_combination (78098309/20000000000000 : ℝ)*(base19) + (459269263/100000000000000 : ℝ)*(base23) + (62610283/100000000000000 : ℝ)*(lower2) + (33694601/25000000000000 : ℝ)*(upper3) + (1466601/3125000000000 : ℝ)*(lower4) + (5947258215714979/100000000000000 : ℝ)*(major0) + (5947258215714979/100000000000000 : ℝ)*(major1) + (5947258215714979/100000000000000 : ℝ)*(major2) + (7945127856160387/100000000000000 : ℝ)*(sp0) + (7945133858392821/100000000000000 : ℝ)*(sp1) + (3972566894807551/50000000000000 : ℝ)*(sp2) + (7898745643319/200000000000 : ℝ)*(sp3) + (3196361989/50000000000000 : ℝ)*(sp4) + (9265812201/100000000000000 : ℝ)*(sp7) + (39493820874717/1000000000000 : ℝ)*(f.failure) + (1589026849776873/20000000000000 : ℝ)*(f.sum) + (537870774983/140000000000000000000000000 : ℝ)*base65 + (72636633352054403/7000000000000000000000000000000 : ℝ)*base67 + (10258918351054403/7000000000000000000000000000000 : ℝ)*base69 + (106464668446054403/7000000000000000000000000000000 : ℝ)*base71 + (20929701103/140000000000000000000000000 : ℝ)*base73 + (18522239578945597/7000000000000000000000000000000 : ℝ)*base76 + (55300128446945597/7000000000000000000000000000000 : ℝ)*base78 + (21025292851945597/7000000000000000000000000000000 : ℝ)*base80 + (233210093623/140000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (71053/6250000000000000000 : ℝ)*base90 + (71053/6250000000000000000 : ℝ)*base92 + (71053/6250000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2051829733654979710858491/250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1501685321/100000000000000 : ℝ)*(base19) + (405532871/25000000000000 : ℝ)*(base23) + (156726553/100000000000000 : ℝ)*(upper3) + (40590391/100000000000000 : ℝ)*(lower4) + (170547859/100000000000000 : ℝ)*(upper5) + (2988753560820953/50000000000000 : ℝ)*(major0) + (2988753560820953/50000000000000 : ℝ)*(major1) + (2988753560820953/50000000000000 : ℝ)*(major2) + (1751208713/4000000000000 : ℝ)*(sp1) + (8820861671/20000000000000 : ℝ)*(sp2) + (7985544560833867/100000000000000 : ℝ)*(sp4) + (3992749639465361/50000000000000 : ℝ)*(sp5) + (7985498834394029/100000000000000 : ℝ)*(sp6) + (992367352218159/25000000000000 : ℝ)*(sp7) + (992367352218159/25000000000000 : ℝ)*(f.failure) + (7985544560833867/100000000000000 : ℝ)*(f.sum) + (321408972531/70000000000000000000000000 : ℝ)*base65 + (16647381624938521/3500000000000000000000000000000 : ℝ)*base67 + (51526807220061479/3500000000000000000000000000000 : ℝ)*base70 + (28913968726938521/3500000000000000000000000000000 : ℝ)*base71 + (238206063379/70000000000000000000000000 : ℝ)*base74 + (46373812191061479/3500000000000000000000000000000 : ℝ)*base76 + (25124753240938521/3500000000000000000000000000000 : ℝ)*base77 + (1074533389938521/3500000000000000000000000000000 : ℝ)*base79 + (169681623199/70000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (1028131/156250000000000000000 : ℝ)*base90 + (1028131/156250000000000000000 : ℝ)*base92 + (1028131/156250000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1199_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8391/2048 : ℝ) ≤ p) (hpb : p ≤ (1049/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9411691/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (441/3125 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2849/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11421/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14087/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1199_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1199_s7_0 (p : ℝ) (hpa : (8391/2048 : ℝ) ≤ p) (hpb : p ≤ (1049/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-534979717/2500000000 : ℝ)*x 0 + (5392001191/10000000000 : ℝ)*x 1 + (658326199/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (534979717/2500000000 : ℝ)^1049 ≤ (13008673359747/100000000000000 : ℝ)^793 := by
    have hnat : (534979717 : ℕ)^1049*100000000000000^793 ≤ 13008673359747^793*2500000000^1049 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      534979717 2500000000 13008673359747 100000000000000 1049 793 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5392001191/10000000000 : ℝ)^1049 ≤ (1766901071099/4000000000000 : ℝ)^793 := by
    have hnat : (5392001191 : ℕ)^1049*4000000000000^793 ≤ 1766901071099^793*10000000000^1049 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392001191 10000000000 1766901071099 4000000000000 1049 793 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (658326199/1250000000 : ℝ)^1049 ≤ (10704699962327/25000000000000 : ℝ)^793 := by
    have hnat : (658326199 : ℕ)^1049*25000000000000^793 ≤ 10704699962327^793*1250000000^1049 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      658326199 1250000000 10704699962327 25000000000000 1049 793 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1049/256 : ℝ)) 1049 793 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-534979717/2500000000 : ℝ), (5392001191/10000000000 : ℝ), (658326199/1250000000 : ℝ)] ![(13008673359747/100000000000000 : ℝ), (1766901071099/4000000000000 : ℝ), (10704699962327/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-534979717/2500000000 : ℝ)|^1049 ≤ (13008673359747/100000000000000 : ℝ)^793
        have hw : |(-534979717/2500000000 : ℝ)|=(534979717/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5392001191/10000000000 : ℝ)|^1049 ≤ (1766901071099/4000000000000 : ℝ)^793
        have hw : |(5392001191/10000000000 : ℝ)|=(5392001191/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(658326199/1250000000 : ℝ)|^1049 ≤ (10704699962327/25000000000000 : ℝ)^793
        have hw : |(658326199/1250000000 : ℝ)|=(658326199/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1199_s7_1 (p : ℝ) (hpa : (8391/2048 : ℝ) ≤ p) (hpb : p ≤ (1049/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2672261977/5000000000 : ℝ)*x 0 + (-1101752581/5000000000 : ℝ)*x 1 + (2633305087/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672261977/5000000000 : ℝ)^1049 ≤ (43658754004863/100000000000000 : ℝ)^793 := by
    have hnat : (2672261977 : ℕ)^1049*100000000000000^793 ≤ 43658754004863^793*5000000000^1049 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672261977 5000000000 43658754004863 100000000000000 1049 793 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1101752581/5000000000 : ℝ)^1049 ≤ (13522439871273/100000000000000 : ℝ)^793 := by
    have hnat : (1101752581 : ℕ)^1049*100000000000000^793 ≤ 13522439871273^793*5000000000^1049 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1101752581 5000000000 13522439871273 100000000000000 1049 793 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2633305087/5000000000 : ℝ)^1049 ≤ (856376122173/2000000000000 : ℝ)^793 := by
    have hnat : (2633305087 : ℕ)^1049*2000000000000^793 ≤ 856376122173^793*5000000000^1049 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633305087 5000000000 856376122173 2000000000000 1049 793 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1049/256 : ℝ)) 1049 793 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672261977/5000000000 : ℝ), (-1101752581/5000000000 : ℝ), (2633305087/5000000000 : ℝ)] ![(43658754004863/100000000000000 : ℝ), (13522439871273/100000000000000 : ℝ), (856376122173/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672261977/5000000000 : ℝ)|^1049 ≤ (43658754004863/100000000000000 : ℝ)^793
        have hw : |(2672261977/5000000000 : ℝ)|=(2672261977/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1101752581/5000000000 : ℝ)|^1049 ≤ (13522439871273/100000000000000 : ℝ)^793
        have hw : |(-1101752581/5000000000 : ℝ)|=(1101752581/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2633305087/5000000000 : ℝ)|^1049 ≤ (856376122173/2000000000000 : ℝ)^793
        have hw : |(2633305087/5000000000 : ℝ)|=(2633305087/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1199_s7_2 (p : ℝ) (hpa : (8391/2048 : ℝ) ≤ p) (hpb : p ≤ (1049/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5344524111/10000000000 : ℝ)*x 0 + (2633304861/5000000000 : ℝ)*x 1 + (-2203505551/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344524111/10000000000 : ℝ)^1049 ≤ (10914688925351/25000000000000 : ℝ)^793 := by
    have hnat : (5344524111 : ℕ)^1049*25000000000000^793 ≤ 10914688925351^793*10000000000^1049 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344524111 10000000000 10914688925351 25000000000000 1049 793 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2633304861/5000000000 : ℝ)^1049 ≤ (42818801247443/100000000000000 : ℝ)^793 := by
    have hnat : (2633304861 : ℕ)^1049*100000000000000^793 ≤ 42818801247443^793*5000000000^1049 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633304861 5000000000 42818801247443 100000000000000 1049 793 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2203505551/10000000000 : ℝ)^1049 ≤ (13522443029133/100000000000000 : ℝ)^793 := by
    have hnat : (2203505551 : ℕ)^1049*100000000000000^793 ≤ 13522443029133^793*10000000000^1049 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2203505551 10000000000 13522443029133 100000000000000 1049 793 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1049/256 : ℝ)) 1049 793 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344524111/10000000000 : ℝ), (2633304861/5000000000 : ℝ), (-2203505551/10000000000 : ℝ)] ![(10914688925351/25000000000000 : ℝ), (42818801247443/100000000000000 : ℝ), (13522443029133/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344524111/10000000000 : ℝ)|^1049 ≤ (10914688925351/25000000000000 : ℝ)^793
        have hw : |(5344524111/10000000000 : ℝ)|=(5344524111/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2633304861/5000000000 : ℝ)|^1049 ≤ (42818801247443/100000000000000 : ℝ)^793
        have hw : |(2633304861/5000000000 : ℝ)|=(2633304861/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2203505551/10000000000 : ℝ)|^1049 ≤ (13522443029133/100000000000000 : ℝ)^793
        have hw : |(-2203505551/10000000000 : ℝ)|=(2203505551/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1199_s7_3 (p : ℝ) (hpa : (8391/2048 : ℝ) ≤ p) (hpb : p ≤ (1049/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2178352329/5000000000 : ℝ)*x 0 + (4232369319/10000000000 : ℝ)*x 1 + (2242312069/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2178352329/5000000000 : ℝ)^1049 ≤ (16658636310369/50000000000000 : ℝ)^793 := by
    have hnat : (2178352329 : ℕ)^1049*50000000000000^793 ≤ 16658636310369^793*5000000000^1049 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2178352329 5000000000 16658636310369 50000000000000 1049 793 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4232369319/10000000000 : ℝ)^1049 ≤ (32065314240021/100000000000000 : ℝ)^793 := by
    have hnat : (4232369319 : ℕ)^1049*100000000000000^793 ≤ 32065314240021^793*10000000000^1049 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4232369319 10000000000 32065314240021 100000000000000 1049 793 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2242312069/5000000000 : ℝ)^1049 ≤ (34617413133551/100000000000000 : ℝ)^793 := by
    have hnat : (2242312069 : ℕ)^1049*100000000000000^793 ≤ 34617413133551^793*5000000000^1049 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2242312069 5000000000 34617413133551 100000000000000 1049 793 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1049/256 : ℝ)) 1049 793 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2178352329/5000000000 : ℝ), (4232369319/10000000000 : ℝ), (2242312069/5000000000 : ℝ)] ![(16658636310369/50000000000000 : ℝ), (32065314240021/100000000000000 : ℝ), (34617413133551/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2178352329/5000000000 : ℝ)|^1049 ≤ (16658636310369/50000000000000 : ℝ)^793
        have hw : |(2178352329/5000000000 : ℝ)|=(2178352329/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4232369319/10000000000 : ℝ)|^1049 ≤ (32065314240021/100000000000000 : ℝ)^793
        have hw : |(4232369319/10000000000 : ℝ)|=(4232369319/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2242312069/5000000000 : ℝ)|^1049 ≤ (34617413133551/100000000000000 : ℝ)^793
        have hw : |(2242312069/5000000000 : ℝ)|=(2242312069/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1199_s7_4 (p : ℝ) (hpa : (8391/2048 : ℝ) ≤ p) (hpb : p ≤ (1049/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-66872619/312500000 : ℝ)*x 0 + (263346283/500000000 : ℝ)*x 1 + (5391683843/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (66872619/312500000 : ℝ)^1049 ≤ (13008713084857/100000000000000 : ℝ)^793 := by
    have hnat : (66872619 : ℕ)^1049*100000000000000^793 ≤ 13008713084857^793*312500000^1049 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      66872619 312500000 13008713084857 100000000000000 1049 793 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (263346283/500000000 : ℝ)^1049 ≤ (10705549789101/25000000000000 : ℝ)^793 := by
    have hnat : (263346283 : ℕ)^1049*25000000000000^793 ≤ 10705549789101^793*500000000^1049 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      263346283 500000000 10705549789101 25000000000000 1049 793 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5391683843/10000000000 : ℝ)^1049 ≤ (44169087745579/100000000000000 : ℝ)^793 := by
    have hnat : (5391683843 : ℕ)^1049*100000000000000^793 ≤ 44169087745579^793*10000000000^1049 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5391683843 10000000000 44169087745579 100000000000000 1049 793 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1049/256 : ℝ)) 1049 793 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-66872619/312500000 : ℝ), (263346283/500000000 : ℝ), (5391683843/10000000000 : ℝ)] ![(13008713084857/100000000000000 : ℝ), (10705549789101/25000000000000 : ℝ), (44169087745579/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-66872619/312500000 : ℝ)|^1049 ≤ (13008713084857/100000000000000 : ℝ)^793
        have hw : |(-66872619/312500000 : ℝ)|=(66872619/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(263346283/500000000 : ℝ)|^1049 ≤ (10705549789101/25000000000000 : ℝ)^793
        have hw : |(263346283/500000000 : ℝ)|=(263346283/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5391683843/10000000000 : ℝ)|^1049 ≤ (44169087745579/100000000000000 : ℝ)^793
        have hw : |(5391683843/10000000000 : ℝ)|=(5391683843/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1199_s7_5 (p : ℝ) (hpa : (8391/2048 : ℝ) ≤ p) (hpb : p ≤ (1049/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5312624593/10000000000 : ℝ)*x 0 + (-2078431121/10000000000 : ℝ)*x 1 + (5391684121/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312624593/10000000000 : ℝ)^1049 ≤ (1732575293167/4000000000000 : ℝ)^793 := by
    have hnat : (5312624593 : ℕ)^1049*4000000000000^793 ≤ 1732575293167^793*10000000000^1049 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312624593 10000000000 1732575293167 4000000000000 1049 793 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2078431121/10000000000 : ℝ)^1049 ≤ (12516526900129/100000000000000 : ℝ)^793 := by
    have hnat : (2078431121 : ℕ)^1049*100000000000000^793 ≤ 12516526900129^793*10000000000^1049 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2078431121 10000000000 12516526900129 100000000000000 1049 793 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5391684121/10000000000 : ℝ)^1049 ≤ (1380284086193/3125000000000 : ℝ)^793 := by
    have hnat : (5391684121 : ℕ)^1049*3125000000000^793 ≤ 1380284086193^793*10000000000^1049 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5391684121 10000000000 1380284086193 3125000000000 1049 793 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1049/256 : ℝ)) 1049 793 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312624593/10000000000 : ℝ), (-2078431121/10000000000 : ℝ), (5391684121/10000000000 : ℝ)] ![(1732575293167/4000000000000 : ℝ), (12516526900129/100000000000000 : ℝ), (1380284086193/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312624593/10000000000 : ℝ)|^1049 ≤ (1732575293167/4000000000000 : ℝ)^793
        have hw : |(5312624593/10000000000 : ℝ)|=(5312624593/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2078431121/10000000000 : ℝ)|^1049 ≤ (12516526900129/100000000000000 : ℝ)^793
        have hw : |(-2078431121/10000000000 : ℝ)|=(2078431121/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5391684121/10000000000 : ℝ)|^1049 ≤ (1380284086193/3125000000000 : ℝ)^793
        have hw : |(5391684121/10000000000 : ℝ)|=(5391684121/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1199_s7_6 (p : ℝ) (hpa : (8391/2048 : ℝ) ≤ p) (hpb : p ≤ (1049/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2656312119/5000000000 : ℝ)*x 0 + (2695842197/5000000000 : ℝ)*x 1 + (-207843123/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2656312119/5000000000 : ℝ)^1049 ≤ (21657189250227/50000000000000 : ℝ)^793 := by
    have hnat : (2656312119 : ℕ)^1049*50000000000000^793 ≤ 21657189250227^793*5000000000^1049 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2656312119 5000000000 21657189250227 50000000000000 1049 793 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2695842197/5000000000 : ℝ)^1049 ≤ (4416909371659/10000000000000 : ℝ)^793 := by
    have hnat : (2695842197 : ℕ)^1049*10000000000000^793 ≤ 4416909371659^793*5000000000^1049 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2695842197 5000000000 4416909371659 10000000000000 1049 793 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (207843123/1000000000 : ℝ)^1049 ≤ (12516527768443/100000000000000 : ℝ)^793 := by
    have hnat : (207843123 : ℕ)^1049*100000000000000^793 ≤ 12516527768443^793*1000000000^1049 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      207843123 1000000000 12516527768443 100000000000000 1049 793 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1049/256 : ℝ)) 1049 793 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2656312119/5000000000 : ℝ), (2695842197/5000000000 : ℝ), (-207843123/1000000000 : ℝ)] ![(21657189250227/50000000000000 : ℝ), (4416909371659/10000000000000 : ℝ), (12516527768443/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2656312119/5000000000 : ℝ)|^1049 ≤ (21657189250227/50000000000000 : ℝ)^793
        have hw : |(2656312119/5000000000 : ℝ)|=(2656312119/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2695842197/5000000000 : ℝ)|^1049 ≤ (4416909371659/10000000000000 : ℝ)^793
        have hw : |(2695842197/5000000000 : ℝ)|=(2695842197/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-207843123/1000000000 : ℝ)|^1049 ≤ (12516527768443/100000000000000 : ℝ)^793
        have hw : |(-207843123/1000000000 : ℝ)|=(207843123/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1199_s7_7 (p : ℝ) (hpa : (8391/2048 : ℝ) ≤ p) (hpb : p ≤ (1049/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2178356979/5000000000 : ℝ)*x 0 + (4483988861/10000000000 : ℝ)*x 1 + (2116503581/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2178356979/5000000000 : ℝ)^1049 ≤ (33317366700611/100000000000000 : ℝ)^793 := by
    have hnat : (2178356979 : ℕ)^1049*100000000000000^793 ≤ 33317366700611^793*5000000000^1049 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2178356979 5000000000 33317366700611 100000000000000 1049 793 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4483988861/10000000000 : ℝ)^1049 ≤ (34610926429811/100000000000000 : ℝ)^793 := by
    have hnat : (4483988861 : ℕ)^1049*100000000000000^793 ≤ 34610926429811^793*10000000000^1049 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4483988861 10000000000 34610926429811 100000000000000 1049 793 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2116503581/5000000000 : ℝ)^1049 ≤ (32071706855787/100000000000000 : ℝ)^793 := by
    have hnat : (2116503581 : ℕ)^1049*100000000000000^793 ≤ 32071706855787^793*5000000000^1049 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2116503581 5000000000 32071706855787 100000000000000 1049 793 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1049/256 : ℝ)) 1049 793 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2178356979/5000000000 : ℝ), (4483988861/10000000000 : ℝ), (2116503581/5000000000 : ℝ)] ![(33317366700611/100000000000000 : ℝ), (34610926429811/100000000000000 : ℝ), (32071706855787/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2178356979/5000000000 : ℝ)|^1049 ≤ (33317366700611/100000000000000 : ℝ)^793
        have hw : |(2178356979/5000000000 : ℝ)|=(2178356979/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4483988861/10000000000 : ℝ)|^1049 ≤ (34610926429811/100000000000000 : ℝ)^793
        have hw : |(4483988861/10000000000 : ℝ)|=(4483988861/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2116503581/5000000000 : ℝ)|^1049 ≤ (32071706855787/100000000000000 : ℝ)^793
        have hw : |(2116503581/5000000000 : ℝ)|=(2116503581/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1199_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8391/2048 : ℝ) ≤ p) (hpb : p ≤ (1049/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9411691/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14087/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11421/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (457/4000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7041/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14087/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11421/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14087/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11421/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14087/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11421/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14087/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11421/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14087/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11421/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14087/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11421/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hlower 2 1 (by decide)
  have fm0 := f.main 0
  simp only [pair0,pair1,pair2,Pi.add_apply] at fm0
  have fx01 := abs_le.mp (f.maximal 0 1)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx01
  have fx02 := abs_le.mp (f.maximal 0 2)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx02
  have fm1 := f.main 1
  simp only [pair0,pair1,pair2,Pi.add_apply] at fm1
  have fx10 := abs_le.mp (f.maximal 1 0)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx10
  have fx12 := abs_le.mp (f.maximal 1 2)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx12
  have fm2 := f.main 2
  simp only [pair0,pair1,pair2,Pi.add_apply] at fm2
  have fx20 := abs_le.mp (f.maximal 2 0)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx20
  have fx21 := abs_le.mp (f.maximal 2 1)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx21
  have base19 : ((1 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 2).2]
  have base23 : ((1 : ℝ)*X 2 1+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 1).2]
  have base65 : ((1 : ℝ)*X 0 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 0).2]
  have base66 : ((-1 : ℝ)*X 0 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 0).1]
  have base67 : ((1 : ℝ)*X 0 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 1).2]
  have base68 : ((-1 : ℝ)*X 0 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 1).1]
  have base69 : ((1 : ℝ)*X 0 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 2).2]
  have base70 : ((-1 : ℝ)*X 0 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 2).1]
  have base71 : ((1 : ℝ)*X 1 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 0).2]
  have base72 : ((-1 : ℝ)*X 1 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 0).1]
  have base73 : ((1 : ℝ)*X 1 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 1).2]
  have base74 : ((-1 : ℝ)*X 1 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 1).1]
  have base75 : ((1 : ℝ)*X 1 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 2).2]
  have base76 : ((-1 : ℝ)*X 1 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 2).1]
  have base77 : ((1 : ℝ)*X 2 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 0).2]
  have base78 : ((-1 : ℝ)*X 2 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 0).1]
  have base79 : ((1 : ℝ)*X 2 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 1).2]
  have base80 : ((-1 : ℝ)*X 2 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 1).1]
  have base81 : ((1 : ℝ)*X 2 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 2).2]
  have base82 : ((-1 : ℝ)*X 2 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 2).1]
  have base83 : ((1 : ℝ)*N 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 0).2]
  have base84 : ((-1 : ℝ)*N 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 0).1]
  have base85 : ((1 : ℝ)*N 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 1).2]
  have base86 : ((-1 : ℝ)*N 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 1).1]
  have base87 : ((1 : ℝ)*N 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 2).2]
  have base88 : ((-1 : ℝ)*N 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 2).1]
  have base89 : ((1 : ℝ)*P 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 0).2]
  have base90 : ((-1 : ℝ)*P 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 0).1]
  have base91 : ((1 : ℝ)*P 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 1).2]
  have base92 : ((-1 : ℝ)*P 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 1).1]
  have base93 : ((1 : ℝ)*P 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 2).2]
  have base94 : ((-1 : ℝ)*P 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 2).1]
  have base95 : ((1 : ℝ)*T) ≤ (3 : ℝ) := by
    linarith only [bounds.2.2.2.2]
  have base96 : ((-1 : ℝ)*T) ≤ (3 : ℝ) := by
    linarith only [bounds.2.2.2.1]
  have hpowlo : (11421/100000 : ℝ) ^ (8391/2048 : ℝ) ≤ (6890100473600301/50000000000000000000 : ℝ) := by
    have hpowers : (11421/100000 : ℝ)^8391 ≤ (6890100473600301/50000000000000000000 : ℝ)^2048 := by
      have hnat : (11421 : ℕ)^8391*50000000000000000000^2048 ≤ 6890100473600301^2048*100000^8391 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11421 100000 6890100473600301 50000000000000000000 8391 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11421/100000 : ℝ)) (X := (6890100473600301/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8391 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (14087/100000 : ℝ) ^ (8391/2048 : ℝ) ≤ (32551160947739493/100000000000000000000 : ℝ) := by
    have hpowers : (14087/100000 : ℝ)^8391 ≤ (32551160947739493/100000000000000000000 : ℝ)^2048 := by
      have hnat : (14087 : ℕ)^8391*100000000000000000000^2048 ≤ 32551160947739493^2048*100000^8391 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14087 100000 32551160947739493 100000000000000000000 8391 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14087/100000 : ℝ)) (X := (32551160947739493/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8391 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (25006890100473600301/25000000000000000000 : ℝ) ≤ (5000336299751939/5000000000000000 : ℝ) ^ (8391/2048 : ℝ) := by
    have hpowers : (25006890100473600301/25000000000000000000 : ℝ)^2048 ≤ (5000336299751939/5000000000000000 : ℝ)^8391 := by
      have hnat : (25006890100473600301 : ℕ)^2048*5000000000000000^8391 ≤ 5000336299751939^8391*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25006890100473600301 25000000000000000000 5000336299751939 5000000000000000 2048 8391 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000336299751939/5000000000000000 : ℝ)) (X := (25006890100473600301/25000000000000000000 : ℝ)) (by norm_num) 8391 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (20009266272378988019/20000000000000000000 : ℝ) ≤ (10001130616344769/10000000000000000 : ℝ) ^ (8391/2048 : ℝ) := by
    have hpowers : (20009266272378988019/20000000000000000000 : ℝ)^2048 ≤ (10001130616344769/10000000000000000 : ℝ)^8391 := by
      have hnat : (20009266272378988019 : ℕ)^2048*10000000000000000^8391 ≤ 10001130616344769^8391*20000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20009266272378988019 20000000000000000000 10001130616344769 10000000000000000 2048 8391 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001130616344769/10000000000000000 : ℝ)) (X := (20009266272378988019/20000000000000000000 : ℝ)) (by norm_num) 8391 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50032551160947739493/50000000000000000000 : ℝ) ≤ (500079431659283/500000000000000 : ℝ) ^ (8391/2048 : ℝ) := by
    have hpowers : (50032551160947739493/50000000000000000000 : ℝ)^2048 ≤ (500079431659283/500000000000000 : ℝ)^8391 := by
      have hnat : (50032551160947739493 : ℕ)^2048*500000000000000^8391 ≤ 500079431659283^8391*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50032551160947739493 50000000000000000000 500079431659283 500000000000000 2048 8391 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (500079431659283/500000000000000 : ℝ)) (X := (50032551160947739493/50000000000000000000 : ℝ)) (by norm_num) 8391 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(6890100473600301/50000000000000000000 : ℝ) ≤ ((13325665564798853263/13330000000000000000 : ℝ)+2*(458016840891/266600000000000 : ℝ)*(11421/100000 : ℝ))^(8391/2048 : ℝ) := by
    rw [show (13325665564798853263/13330000000000000000 : ℝ)+2*(458016840891/266600000000000 : ℝ)*(11421/100000 : ℝ)=(5000336299751939/5000000000000000 : ℝ) by norm_num, show 1+2*(6890100473600301/50000000000000000000 : ℝ)=(25006890100473600301/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(32551160947739493/100000000000000000000 : ℝ)+(6890100473600301/50000000000000000000 : ℝ) ≤ ((13325665564798853263/13330000000000000000 : ℝ)+(458016840891/266600000000000 : ℝ)*((14087/100000 : ℝ)+(11421/100000 : ℝ)))^(8391/2048 : ℝ) := by
    rw [show (13325665564798853263/13330000000000000000 : ℝ)+(458016840891/266600000000000 : ℝ)*((14087/100000 : ℝ)+(11421/100000 : ℝ))=(10001130616344769/10000000000000000 : ℝ) by norm_num, show 1+(32551160947739493/100000000000000000000 : ℝ)+(6890100473600301/50000000000000000000 : ℝ)=(20009266272378988019/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(32551160947739493/100000000000000000000 : ℝ) ≤ ((13325665564798853263/13330000000000000000 : ℝ)+2*(458016840891/266600000000000 : ℝ)*(14087/100000 : ℝ))^(8391/2048 : ℝ) := by
    rw [show (13325665564798853263/13330000000000000000 : ℝ)+2*(458016840891/266600000000000 : ℝ)*(14087/100000 : ℝ)=(500079431659283/500000000000000 : ℝ) by norm_num, show 1+2*(32551160947739493/100000000000000000000 : ℝ)=(50032551160947739493/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (13325665564798853263/13330000000000000000 : ℝ)*(X 1 0+X 2 0)+(458016840891/266600000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8391/2048 : ℝ)) (lo := (11421/100000 : ℝ)) (hi := (14087/100000 : ℝ)) (c := (13325665564798853263/13330000000000000000 : ℝ)) (alpha := (458016840891/266600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (13325665564798853263/13330000000000000000 : ℝ)*(X 0 1+X 2 1)+(458016840891/266600000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8391/2048 : ℝ)) (lo := (11421/100000 : ℝ)) (hi := (14087/100000 : ℝ)) (c := (13325665564798853263/13330000000000000000 : ℝ)) (alpha := (458016840891/266600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (13325665564798853263/13330000000000000000 : ℝ)*(X 0 2+X 1 2)+(458016840891/266600000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8391/2048 : ℝ)) (lo := (11421/100000 : ℝ)) (hi := (14087/100000 : ℝ)) (c := (13325665564798853263/13330000000000000000 : ℝ)) (alpha := (458016840891/266600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-534979717/2500000000 : ℝ)*X 0 0+(5392001191/10000000000 : ℝ)*X 0 1+(658326199/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1199_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2672261977/5000000000 : ℝ)*X 1 0+(-1101752581/5000000000 : ℝ)*X 1 1+(2633305087/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1199_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5344524111/10000000000 : ℝ)*X 2 0+(2633304861/5000000000 : ℝ)*X 2 1+(-2203505551/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1199_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2178352329/5000000000 : ℝ)*X 0 0+(4232369319/10000000000 : ℝ)*X 0 1+(2242312069/5000000000 : ℝ)*X 0 2+(2178352329/5000000000 : ℝ)*X 1 0+(4232369319/10000000000 : ℝ)*X 1 1+(2242312069/5000000000 : ℝ)*X 1 2+(2178352329/5000000000 : ℝ)*X 2 0+(4232369319/10000000000 : ℝ)*X 2 1+(2242312069/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1199_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-66872619/312500000 : ℝ)*X 0 0+(263346283/500000000 : ℝ)*X 0 1+(5391683843/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1199_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5312624593/10000000000 : ℝ)*X 1 0+(-2078431121/10000000000 : ℝ)*X 1 1+(5391684121/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1199_s7_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2656312119/5000000000 : ℝ)*X 2 0+(2695842197/5000000000 : ℝ)*X 2 1+(-207843123/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1199_s7_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2178356979/5000000000 : ℝ)*X 0 0+(4483988861/10000000000 : ℝ)*X 0 1+(2116503581/5000000000 : ℝ)*X 0 2+(2178356979/5000000000 : ℝ)*X 1 0+(4483988861/10000000000 : ℝ)*X 1 1+(2116503581/5000000000 : ℝ)*X 1 2+(2178356979/5000000000 : ℝ)*X 2 0+(4483988861/10000000000 : ℝ)*X 2 1+(2116503581/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1199_s7_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (125702472113130244396569/13330000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1216026879/50000000000000 : ℝ)*(base19) + (1319466613/50000000000000 : ℝ)*(base23) + (58799453/50000000000000 : ℝ)*(lower2) + (611702399/100000000000000 : ℝ)*(upper3) + (25738869/25000000000000 : ℝ)*(lower4) + (5969766714537801/100000000000000 : ℝ)*(major0) + (5969766714537801/100000000000000 : ℝ)*(major1) + (5969766714537801/100000000000000 : ℝ)*(major2) + (1993780904163641/25000000000000 : ℝ)*(sp0) + (7975201428160833/100000000000000 : ℝ)*(sp1) + (1993800305320341/25000000000000 : ℝ)*(sp2) + (3964280313150301/100000000000000 : ℝ)*(sp3) + (40121780013/50000000000000 : ℝ)*(sp4) + (12235343983/25000000000000 : ℝ)*(sp7) + (495541156815779/12500000000000 : ℝ)*(f.failure) + (797520386021459/10000000000000 : ℝ)*(f.sum) + (71960642538129/13330000000000000000000000000 : ℝ)*base66 + (17428120609314755337/1333000000000000000000000000000000 : ℝ)*base68 + (15576470215676244663/1333000000000000000000000000000000 : ℝ)*base69 + (1764695099567755337/1333000000000000000000000000000000 : ℝ)*base72 + (28954599017559/13330000000000000000000000000 : ℝ)*base74 + (4261596793388244663/1333000000000000000000000000000000 : ℝ)*base75 + (20533166770993755337/1333000000000000000000000000000000 : ℝ)*base78 + (12262364347993244663/1333000000000000000000000000000000 : ℝ)*base79 + (61777730289449/13330000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (1158961/78125000000000000000 : ℝ)*base90 + (1158961/78125000000000000000 : ℝ)*base92 + (1158961/78125000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3369934403639934217721811/430000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1105156219/50000000000000 : ℝ)*(base19) + (876162067/50000000000000 : ℝ)*(base23) + (2212111/5000000000000 : ℝ)*(upper2) + (96389623/25000000000000 : ℝ)*(upper3) + (101149593/50000000000000 : ℝ)*(upper5) + (239996900828631/4000000000000 : ℝ)*(major0) + (239996900828631/4000000000000 : ℝ)*(major1) + (239996900828631/4000000000000 : ℝ)*(major2) + (427673959/625000000000 : ℝ)*(sp1) + (4217807483/6250000000000 : ℝ)*(sp2) + (8015490028805347/100000000000000 : ℝ)*(sp4) + (801541939065947/10000000000000 : ℝ)*(sp5) + (1603084158312297/20000000000000 : ℝ)*(sp6) + (1992177375695483/50000000000000 : ℝ)*(sp7) + (1992177375695483/50000000000000 : ℝ)*(f.failure) + (8015490028805347/100000000000000 : ℝ)*(f.sum) + (226393950983/86000000000000000000000000 : ℝ)*base65 + (24209226111371063/1720000000000000000000000000000 : ℝ)*base67 + (15319108092131063/1720000000000000000000000000000 : ℝ)*base69 + (14722521790068937/1720000000000000000000000000000 : ℝ)*base72 + (787273521919/86000000000000000000000000 : ℝ)*base73 + (5021836328651063/1720000000000000000000000000000 : ℝ)*base75 + (652097648971063/1720000000000000000000000000000 : ℝ)*base77 + (72058152611451063/1720000000000000000000000000000 : ℝ)*base79 + (693441911451/86000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (783247/312500000000000000000 : ℝ)*base90 + (783247/312500000000000000000 : ℝ)*base92 + (783247/312500000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1199_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8391/2048 : ℝ) ≤ p) (hpb : p ≤ (1049/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9411691/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14087/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11421/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (457/4000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7041/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1199_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1199_s8_0 (p : ℝ) (hpa : (8391/2048 : ℝ) ≤ p) (hpb : p ≤ (1049/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-2139924997/10000000000 : ℝ)*x 0 + (5391956417/10000000000 : ℝ)*x 1 + (1316662531/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2139924997/10000000000 : ℝ)^1049 ≤ (13008722646229/100000000000000 : ℝ)^793 := by
    have hnat : (2139924997 : ℕ)^1049*100000000000000^793 ≤ 13008722646229^793*10000000000^1049 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2139924997 10000000000 13008722646229 100000000000000 1049 793 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5391956417/10000000000 : ℝ)^1049 ≤ (22086020783663/50000000000000 : ℝ)^793 := by
    have hnat : (5391956417 : ℕ)^1049*50000000000000^793 ≤ 22086020783663^793*10000000000^1049 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5391956417 10000000000 22086020783663 50000000000000 1049 793 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1316662531/2500000000 : ℝ)^1049 ≤ (42819235766743/100000000000000 : ℝ)^793 := by
    have hnat : (1316662531 : ℕ)^1049*100000000000000^793 ≤ 42819235766743^793*2500000000^1049 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316662531 2500000000 42819235766743 100000000000000 1049 793 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1049/256 : ℝ)) 1049 793 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2139924997/10000000000 : ℝ), (5391956417/10000000000 : ℝ), (1316662531/2500000000 : ℝ)] ![(13008722646229/100000000000000 : ℝ), (22086020783663/50000000000000 : ℝ), (42819235766743/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2139924997/10000000000 : ℝ)|^1049 ≤ (13008722646229/100000000000000 : ℝ)^793
        have hw : |(-2139924997/10000000000 : ℝ)|=(2139924997/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5391956417/10000000000 : ℝ)|^1049 ≤ (22086020783663/50000000000000 : ℝ)^793
        have hw : |(5391956417/10000000000 : ℝ)|=(5391956417/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1316662531/2500000000 : ℝ)|^1049 ≤ (42819235766743/100000000000000 : ℝ)^793
        have hw : |(1316662531/2500000000 : ℝ)|=(1316662531/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1199_s8_1 (p : ℝ) (hpa : (8391/2048 : ℝ) ≤ p) (hpb : p ≤ (1049/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2672256021/5000000000 : ℝ)*x 0 + (-2203468087/10000000000 : ℝ)*x 1 + (5266650127/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672256021/5000000000 : ℝ)^1049 ≤ (21829312641971/50000000000000 : ℝ)^793 := by
    have hnat : (2672256021 : ℕ)^1049*50000000000000^793 ≤ 21829312641971^793*5000000000^1049 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672256021 5000000000 21829312641971 50000000000000 1049 793 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2203468087/10000000000 : ℝ)^1049 ≤ (13522138901231/100000000000000 : ℝ)^793 := by
    have hnat : (2203468087 : ℕ)^1049*100000000000000^793 ≤ 13522138901231^793*10000000000^1049 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2203468087 10000000000 13522138901231 100000000000000 1049 793 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5266650127/10000000000 : ℝ)^1049 ≤ (42819235799007/100000000000000 : ℝ)^793 := by
    have hnat : (5266650127 : ℕ)^1049*100000000000000^793 ≤ 42819235799007^793*10000000000^1049 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266650127 10000000000 42819235799007 100000000000000 1049 793 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1049/256 : ℝ)) 1049 793 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672256021/5000000000 : ℝ), (-2203468087/10000000000 : ℝ), (5266650127/10000000000 : ℝ)] ![(21829312641971/50000000000000 : ℝ), (13522138901231/100000000000000 : ℝ), (42819235799007/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672256021/5000000000 : ℝ)|^1049 ≤ (21829312641971/50000000000000 : ℝ)^793
        have hw : |(2672256021/5000000000 : ℝ)|=(2672256021/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2203468087/10000000000 : ℝ)|^1049 ≤ (13522138901231/100000000000000 : ℝ)^793
        have hw : |(-2203468087/10000000000 : ℝ)|=(2203468087/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5266650127/10000000000 : ℝ)|^1049 ≤ (42819235799007/100000000000000 : ℝ)^793
        have hw : |(5266650127/10000000000 : ℝ)|=(5266650127/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1199_s8_2 (p : ℝ) (hpa : (8391/2048 : ℝ) ≤ p) (hpb : p ≤ (1049/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5344512009/10000000000 : ℝ)*x 0 + (2633325063/5000000000 : ℝ)*x 1 + (-550867033/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344512009/10000000000 : ℝ)^1049 ≤ (8731724985469/20000000000000 : ℝ)^793 := by
    have hnat : (5344512009 : ℕ)^1049*20000000000000^793 ≤ 8731724985469^793*10000000000^1049 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344512009 10000000000 8731724985469 20000000000000 1049 793 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2633325063/5000000000 : ℝ)^1049 ≤ (10704808947063/25000000000000 : ℝ)^793 := by
    have hnat : (2633325063 : ℕ)^1049*25000000000000^793 ≤ 10704808947063^793*5000000000^1049 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633325063 5000000000 10704808947063 25000000000000 1049 793 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (550867033/2500000000 : ℝ)^1049 ≤ (6761069633267/50000000000000 : ℝ)^793 := by
    have hnat : (550867033 : ℕ)^1049*50000000000000^793 ≤ 6761069633267^793*2500000000^1049 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      550867033 2500000000 6761069633267 50000000000000 1049 793 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1049/256 : ℝ)) 1049 793 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344512009/10000000000 : ℝ), (2633325063/5000000000 : ℝ), (-550867033/2500000000 : ℝ)] ![(8731724985469/20000000000000 : ℝ), (10704808947063/25000000000000 : ℝ), (6761069633267/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344512009/10000000000 : ℝ)|^1049 ≤ (8731724985469/20000000000000 : ℝ)^793
        have hw : |(5344512009/10000000000 : ℝ)|=(5344512009/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2633325063/5000000000 : ℝ)|^1049 ≤ (10704808947063/25000000000000 : ℝ)^793
        have hw : |(2633325063/5000000000 : ℝ)|=(2633325063/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-550867033/2500000000 : ℝ)|^1049 ≤ (6761069633267/50000000000000 : ℝ)^793
        have hw : |(-550867033/2500000000 : ℝ)|=(550867033/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1199_s8_3 (p : ℝ) (hpa : (8391/2048 : ℝ) ≤ p) (hpb : p ≤ (1049/256 : ℝ)) (x : Fin 3 → ℝ) :
    (217835317/500000000 : ℝ)*x 0 + (4232454879/10000000000 : ℝ)*x 1 + (896907699/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (217835317/500000000 : ℝ)^1049 ≤ (33317289636039/100000000000000 : ℝ)^793 := by
    have hnat : (217835317 : ℕ)^1049*100000000000000^793 ≤ 33317289636039^793*500000000^1049 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      217835317 500000000 33317289636039 100000000000000 1049 793 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4232454879/10000000000 : ℝ)^1049 ≤ (32066171724833/100000000000000 : ℝ)^793 := by
    have hnat : (4232454879 : ℕ)^1049*100000000000000^793 ≤ 32066171724833^793*10000000000^1049 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4232454879 10000000000 32066171724833 100000000000000 1049 793 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (896907699/2000000000 : ℝ)^1049 ≤ (34616538630367/100000000000000 : ℝ)^793 := by
    have hnat : (896907699 : ℕ)^1049*100000000000000^793 ≤ 34616538630367^793*2000000000^1049 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      896907699 2000000000 34616538630367 100000000000000 1049 793 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1049/256 : ℝ)) 1049 793 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(217835317/500000000 : ℝ), (4232454879/10000000000 : ℝ), (896907699/2000000000 : ℝ)] ![(33317289636039/100000000000000 : ℝ), (32066171724833/100000000000000 : ℝ), (34616538630367/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(217835317/500000000 : ℝ)|^1049 ≤ (33317289636039/100000000000000 : ℝ)^793
        have hw : |(217835317/500000000 : ℝ)|=(217835317/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4232454879/10000000000 : ℝ)|^1049 ≤ (32066171724833/100000000000000 : ℝ)^793
        have hw : |(4232454879/10000000000 : ℝ)|=(4232454879/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(896907699/2000000000 : ℝ)|^1049 ≤ (34616538630367/100000000000000 : ℝ)^793
        have hw : |(896907699/2000000000 : ℝ)|=(896907699/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1199_s8_4 (p : ℝ) (hpa : (8391/2048 : ℝ) ≤ p) (hpb : p ≤ (1049/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-6687281/31250000 : ℝ)*x 0 + (1053393087/2000000000 : ℝ)*x 1 + (5391639831/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6687281/31250000 : ℝ)^1049 ≤ (1300876223467/10000000000000 : ℝ)^793 := by
    have hnat : (6687281 : ℕ)^1049*10000000000000^793 ≤ 1300876223467^793*31250000^1049 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6687281 31250000 1300876223467 10000000000000 1049 793 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1053393087/2000000000 : ℝ)^1049 ≤ (2141131347033/5000000000000 : ℝ)^793 := by
    have hnat : (1053393087 : ℕ)^1049*5000000000000^793 ≤ 2141131347033^793*2000000000^1049 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1053393087 2000000000 2141131347033 5000000000000 1049 793 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5391639831/10000000000 : ℝ)^1049 ≤ (22084305401089/50000000000000 : ℝ)^793 := by
    have hnat : (5391639831 : ℕ)^1049*50000000000000^793 ≤ 22084305401089^793*10000000000^1049 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5391639831 10000000000 22084305401089 50000000000000 1049 793 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1049/256 : ℝ)) 1049 793 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-6687281/31250000 : ℝ), (1053393087/2000000000 : ℝ), (5391639831/10000000000 : ℝ)] ![(1300876223467/10000000000000 : ℝ), (2141131347033/5000000000000 : ℝ), (22084305401089/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-6687281/31250000 : ℝ)|^1049 ≤ (1300876223467/10000000000000 : ℝ)^793
        have hw : |(-6687281/31250000 : ℝ)|=(6687281/31250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1053393087/2000000000 : ℝ)|^1049 ≤ (2141131347033/5000000000000 : ℝ)^793
        have hw : |(1053393087/2000000000 : ℝ)|=(1053393087/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5391639831/10000000000 : ℝ)|^1049 ≤ (22084305401089/50000000000000 : ℝ)^793
        have hw : |(5391639831/10000000000 : ℝ)|=(5391639831/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1199_s8_5 (p : ℝ) (hpa : (8391/2048 : ℝ) ≤ p) (hpb : p ≤ (1049/256 : ℝ)) (x : Fin 3 → ℝ) :
    (33203963/62500000 : ℝ)*x 0 + (-2078478319/10000000000 : ℝ)*x 1 + (5391639983/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (33203963/62500000 : ℝ)^1049 ≤ (1353577645241/3125000000000 : ℝ)^793 := by
    have hnat : (33203963 : ℕ)^1049*3125000000000^793 ≤ 1353577645241^793*62500000^1049 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      33203963 62500000 1353577645241 3125000000000 1049 793 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2078478319/10000000000 : ℝ)^1049 ≤ (2503380577921/20000000000000 : ℝ)^793 := by
    have hnat : (2078478319 : ℕ)^1049*20000000000000^793 ≤ 2503380577921^793*10000000000^1049 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2078478319 10000000000 2503380577921 20000000000000 1049 793 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5391639983/10000000000 : ℝ)^1049 ≤ (44168612449349/100000000000000 : ℝ)^793 := by
    have hnat : (5391639983 : ℕ)^1049*100000000000000^793 ≤ 44168612449349^793*10000000000^1049 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5391639983 10000000000 44168612449349 100000000000000 1049 793 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1049/256 : ℝ)) 1049 793 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(33203963/62500000 : ℝ), (-2078478319/10000000000 : ℝ), (5391639983/10000000000 : ℝ)] ![(1353577645241/3125000000000 : ℝ), (2503380577921/20000000000000 : ℝ), (44168612449349/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(33203963/62500000 : ℝ)|^1049 ≤ (1353577645241/3125000000000 : ℝ)^793
        have hw : |(33203963/62500000 : ℝ)|=(33203963/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2078478319/10000000000 : ℝ)|^1049 ≤ (2503380577921/20000000000000 : ℝ)^793
        have hw : |(-2078478319/10000000000 : ℝ)|=(2078478319/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5391639983/10000000000 : ℝ)|^1049 ≤ (44168612449349/100000000000000 : ℝ)^793
        have hw : |(5391639983/10000000000 : ℝ)|=(5391639983/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1199_s8_6 (p : ℝ) (hpa : (8391/2048 : ℝ) ≤ p) (hpb : p ≤ (1049/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5312634231/10000000000 : ℝ)*x 0 + (5391639811/10000000000 : ℝ)*x 1 + (-2078478349/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312634231/10000000000 : ℝ)^1049 ≤ (43314486276267/100000000000000 : ℝ)^793 := by
    have hnat : (5312634231 : ℕ)^1049*100000000000000^793 ≤ 43314486276267^793*10000000000^1049 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312634231 10000000000 43314486276267 100000000000000 1049 793 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5391639811/10000000000 : ℝ)^1049 ≤ (8833722117089/20000000000000 : ℝ)^793 := by
    have hnat : (5391639811 : ℕ)^1049*20000000000000^793 ≤ 8833722117089^793*10000000000^1049 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5391639811 10000000000 8833722117089 20000000000000 1049 793 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2078478349/10000000000 : ℝ)^1049 ≤ (782306445537/6250000000000 : ℝ)^793 := by
    have hnat : (2078478349 : ℕ)^1049*6250000000000^793 ≤ 782306445537^793*10000000000^1049 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2078478349 10000000000 782306445537 6250000000000 1049 793 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1049/256 : ℝ)) 1049 793 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312634231/10000000000 : ℝ), (5391639811/10000000000 : ℝ), (-2078478349/10000000000 : ℝ)] ![(43314486276267/100000000000000 : ℝ), (8833722117089/20000000000000 : ℝ), (782306445537/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312634231/10000000000 : ℝ)|^1049 ≤ (43314486276267/100000000000000 : ℝ)^793
        have hw : |(5312634231/10000000000 : ℝ)|=(5312634231/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5391639811/10000000000 : ℝ)|^1049 ≤ (8833722117089/20000000000000 : ℝ)^793
        have hw : |(5391639811/10000000000 : ℝ)|=(5391639811/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2078478349/10000000000 : ℝ)|^1049 ≤ (782306445537/6250000000000 : ℝ)^793
        have hw : |(-2078478349/10000000000 : ℝ)|=(2078478349/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1199_s8_7 (p : ℝ) (hpa : (8391/2048 : ℝ) ≤ p) (hpb : p ≤ (1049/256 : ℝ)) (x : Fin 3 → ℝ) :
    (272294743/625000000 : ℝ)*x 0 + (1120976081/2500000000 : ℝ)*x 1 + (4233091337/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (272294743/625000000 : ℝ)^1049 ≤ (16658693112361/50000000000000 : ℝ)^793 := by
    have hnat : (272294743 : ℕ)^1049*50000000000000^793 ≤ 16658693112361^793*625000000^1049 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      272294743 625000000 16658693112361 50000000000000 1049 793 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1120976081/2500000000 : ℝ)^1049 ≤ (8652515814867/25000000000000 : ℝ)^793 := by
    have hnat : (1120976081 : ℕ)^1049*25000000000000^793 ≤ 8652515814867^793*2500000000^1049 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1120976081 2500000000 8652515814867 25000000000000 1049 793 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4233091337/10000000000 : ℝ)^1049 ≤ (6414510100217/20000000000000 : ℝ)^793 := by
    have hnat : (4233091337 : ℕ)^1049*20000000000000^793 ≤ 6414510100217^793*10000000000^1049 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4233091337 10000000000 6414510100217 20000000000000 1049 793 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1049/256 : ℝ)) 1049 793 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(272294743/625000000 : ℝ), (1120976081/2500000000 : ℝ), (4233091337/10000000000 : ℝ)] ![(16658693112361/50000000000000 : ℝ), (8652515814867/25000000000000 : ℝ), (6414510100217/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(272294743/625000000 : ℝ)|^1049 ≤ (16658693112361/50000000000000 : ℝ)^793
        have hw : |(272294743/625000000 : ℝ)|=(272294743/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1120976081/2500000000 : ℝ)|^1049 ≤ (8652515814867/25000000000000 : ℝ)^793
        have hw : |(1120976081/2500000000 : ℝ)|=(1120976081/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4233091337/10000000000 : ℝ)|^1049 ≤ (6414510100217/20000000000000 : ℝ)^793
        have hw : |(4233091337/10000000000 : ℝ)|=(4233091337/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1199_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8391/2048 : ℝ) ≤ p) (hpb : p ≤ (1049/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9411691/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7041/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (457/4000 : ℝ)*pair X i i ≤ pair X i h) :
    (5713/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14081/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7041/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (457/4000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7041/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (457/4000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7041/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (457/4000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7041/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (457/4000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7041/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (457/4000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7041/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (457/4000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hlower 2 1 (by decide)
  have fm0 := f.main 0
  simp only [pair0,pair1,pair2,Pi.add_apply] at fm0
  have fx01 := abs_le.mp (f.maximal 0 1)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx01
  have fx02 := abs_le.mp (f.maximal 0 2)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx02
  have fm1 := f.main 1
  simp only [pair0,pair1,pair2,Pi.add_apply] at fm1
  have fx10 := abs_le.mp (f.maximal 1 0)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx10
  have fx12 := abs_le.mp (f.maximal 1 2)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx12
  have fm2 := f.main 2
  simp only [pair0,pair1,pair2,Pi.add_apply] at fm2
  have fx20 := abs_le.mp (f.maximal 2 0)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx20
  have fx21 := abs_le.mp (f.maximal 2 1)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx21
  have base19 : ((1 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 2).2]
  have base23 : ((1 : ℝ)*X 2 1+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 1).2]
  have base65 : ((1 : ℝ)*X 0 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 0).2]
  have base66 : ((-1 : ℝ)*X 0 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 0).1]
  have base67 : ((1 : ℝ)*X 0 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 1).2]
  have base68 : ((-1 : ℝ)*X 0 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 1).1]
  have base69 : ((1 : ℝ)*X 0 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 2).2]
  have base70 : ((-1 : ℝ)*X 0 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 2).1]
  have base71 : ((1 : ℝ)*X 1 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 0).2]
  have base72 : ((-1 : ℝ)*X 1 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 0).1]
  have base73 : ((1 : ℝ)*X 1 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 1).2]
  have base74 : ((-1 : ℝ)*X 1 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 1).1]
  have base75 : ((1 : ℝ)*X 1 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 2).2]
  have base76 : ((-1 : ℝ)*X 1 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 2).1]
  have base77 : ((1 : ℝ)*X 2 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 0).2]
  have base78 : ((-1 : ℝ)*X 2 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 0).1]
  have base79 : ((1 : ℝ)*X 2 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 1).2]
  have base80 : ((-1 : ℝ)*X 2 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 1).1]
  have base81 : ((1 : ℝ)*X 2 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 2).2]
  have base82 : ((-1 : ℝ)*X 2 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 2).1]
  have base83 : ((1 : ℝ)*N 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 0).2]
  have base84 : ((-1 : ℝ)*N 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 0).1]
  have base85 : ((1 : ℝ)*N 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 1).2]
  have base86 : ((-1 : ℝ)*N 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 1).1]
  have base87 : ((1 : ℝ)*N 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 2).2]
  have base88 : ((-1 : ℝ)*N 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 2).1]
  have base89 : ((1 : ℝ)*P 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 0).2]
  have base90 : ((-1 : ℝ)*P 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 0).1]
  have base91 : ((1 : ℝ)*P 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 1).2]
  have base92 : ((-1 : ℝ)*P 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 1).1]
  have base93 : ((1 : ℝ)*P 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 2).2]
  have base94 : ((-1 : ℝ)*P 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 2).1]
  have base95 : ((1 : ℝ)*T) ≤ (3 : ℝ) := by
    linarith only [bounds.2.2.2.2]
  have base96 : ((-1 : ℝ)*T) ≤ (3 : ℝ) := by
    linarith only [bounds.2.2.2.1]
  have hpowlo : (457/4000 : ℝ) ^ (8391/2048 : ℝ) ≤ (551999428164423/4000000000000000000 : ℝ) := by
    have hpowers : (457/4000 : ℝ)^8391 ≤ (551999428164423/4000000000000000000 : ℝ)^2048 := by
      have hnat : (457 : ℕ)^8391*4000000000000000000^2048 ≤ 551999428164423^2048*4000^8391 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        457 4000 551999428164423 4000000000000000000 8391 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (457/4000 : ℝ)) (X := (551999428164423/4000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8391 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (7041/50000 : ℝ) ^ (8391/2048 : ℝ) ≤ (32503849850033451/100000000000000000000 : ℝ) := by
    have hpowers : (7041/50000 : ℝ)^8391 ≤ (32503849850033451/100000000000000000000 : ℝ)^2048 := by
      have hnat : (7041 : ℕ)^8391*100000000000000000000^2048 ≤ 32503849850033451^2048*50000^8391 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7041 50000 32503849850033451 100000000000000000000 8391 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7041/50000 : ℝ)) (X := (32503849850033451/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8391 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (2000551999428164423/2000000000000000000 : ℝ) ≤ (10000673565079769/10000000000000000 : ℝ) ^ (8391/2048 : ℝ) := by
    have hpowers : (2000551999428164423/2000000000000000000 : ℝ)^2048 ≤ (10000673565079769/10000000000000000 : ℝ)^8391 := by
      have hnat : (2000551999428164423 : ℕ)^2048*10000000000000000^8391 ≤ 10000673565079769^8391*2000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2000551999428164423 2000000000000000000 10000673565079769 10000000000000000 2048 8391 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000673565079769/10000000000000000 : ℝ)) (X := (2000551999428164423/2000000000000000000 : ℝ)) (by norm_num) 8391 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (50023151917777072013/50000000000000000000 : ℝ) ≤ (1250141243092709/1250000000000000 : ℝ) ^ (8391/2048 : ℝ) := by
    have hpowers : (50023151917777072013/50000000000000000000 : ℝ)^2048 ≤ (1250141243092709/1250000000000000 : ℝ)^8391 := by
      have hnat : (50023151917777072013 : ℕ)^2048*1250000000000000^8391 ≤ 1250141243092709^8391*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50023151917777072013 50000000000000000000 1250141243092709 1250000000000000 2048 8391 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250141243092709/1250000000000000 : ℝ)) (X := (50023151917777072013/50000000000000000000 : ℝ)) (by norm_num) 8391 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50032503849850033451/50000000000000000000 : ℝ) ≤ (400063452976143/400000000000000 : ℝ) ^ (8391/2048 : ℝ) := by
    have hpowers : (50032503849850033451/50000000000000000000 : ℝ)^2048 ≤ (400063452976143/400000000000000 : ℝ)^8391 := by
      have hnat : (50032503849850033451 : ℕ)^2048*400000000000000^8391 ≤ 400063452976143^8391*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50032503849850033451 50000000000000000000 400063452976143 400000000000000 2048 8391 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (400063452976143/400000000000000 : ℝ)) (X := (50032503849850033451/50000000000000000000 : ℝ)) (by norm_num) 8391 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(551999428164423/4000000000000000000 : ℝ) ≤ ((26561361387142462683/26570000000000000000 : ℝ)+2*(456379661903/265700000000000 : ℝ)*(457/4000 : ℝ))^(8391/2048 : ℝ) := by
    rw [show (26561361387142462683/26570000000000000000 : ℝ)+2*(456379661903/265700000000000 : ℝ)*(457/4000 : ℝ)=(10000673565079769/10000000000000000 : ℝ) by norm_num, show 1+2*(551999428164423/4000000000000000000 : ℝ)=(2000551999428164423/2000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(32503849850033451/100000000000000000000 : ℝ)+(551999428164423/4000000000000000000 : ℝ) ≤ ((26561361387142462683/26570000000000000000 : ℝ)+(456379661903/265700000000000 : ℝ)*((7041/50000 : ℝ)+(457/4000 : ℝ)))^(8391/2048 : ℝ) := by
    rw [show (26561361387142462683/26570000000000000000 : ℝ)+(456379661903/265700000000000 : ℝ)*((7041/50000 : ℝ)+(457/4000 : ℝ))=(1250141243092709/1250000000000000 : ℝ) by norm_num, show 1+(32503849850033451/100000000000000000000 : ℝ)+(551999428164423/4000000000000000000 : ℝ)=(50023151917777072013/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(32503849850033451/100000000000000000000 : ℝ) ≤ ((26561361387142462683/26570000000000000000 : ℝ)+2*(456379661903/265700000000000 : ℝ)*(7041/50000 : ℝ))^(8391/2048 : ℝ) := by
    rw [show (26561361387142462683/26570000000000000000 : ℝ)+2*(456379661903/265700000000000 : ℝ)*(7041/50000 : ℝ)=(400063452976143/400000000000000 : ℝ) by norm_num, show 1+2*(32503849850033451/100000000000000000000 : ℝ)=(50032503849850033451/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (26561361387142462683/26570000000000000000 : ℝ)*(X 1 0+X 2 0)+(456379661903/265700000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8391/2048 : ℝ)) (lo := (457/4000 : ℝ)) (hi := (7041/50000 : ℝ)) (c := (26561361387142462683/26570000000000000000 : ℝ)) (alpha := (456379661903/265700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (26561361387142462683/26570000000000000000 : ℝ)*(X 0 1+X 2 1)+(456379661903/265700000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8391/2048 : ℝ)) (lo := (457/4000 : ℝ)) (hi := (7041/50000 : ℝ)) (c := (26561361387142462683/26570000000000000000 : ℝ)) (alpha := (456379661903/265700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (26561361387142462683/26570000000000000000 : ℝ)*(X 0 2+X 1 2)+(456379661903/265700000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8391/2048 : ℝ)) (lo := (457/4000 : ℝ)) (hi := (7041/50000 : ℝ)) (c := (26561361387142462683/26570000000000000000 : ℝ)) (alpha := (456379661903/265700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2139924997/10000000000 : ℝ)*X 0 0+(5391956417/10000000000 : ℝ)*X 0 1+(1316662531/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1199_s8_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2672256021/5000000000 : ℝ)*X 1 0+(-2203468087/10000000000 : ℝ)*X 1 1+(5266650127/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1199_s8_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5344512009/10000000000 : ℝ)*X 2 0+(2633325063/5000000000 : ℝ)*X 2 1+(-550867033/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1199_s8_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((217835317/500000000 : ℝ)*X 0 0+(4232454879/10000000000 : ℝ)*X 0 1+(896907699/2000000000 : ℝ)*X 0 2+(217835317/500000000 : ℝ)*X 1 0+(4232454879/10000000000 : ℝ)*X 1 1+(896907699/2000000000 : ℝ)*X 1 2+(217835317/500000000 : ℝ)*X 2 0+(4232454879/10000000000 : ℝ)*X 2 1+(896907699/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1199_s8_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-6687281/31250000 : ℝ)*X 0 0+(1053393087/2000000000 : ℝ)*X 0 1+(5391639831/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1199_s8_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((33203963/62500000 : ℝ)*X 1 0+(-2078478319/10000000000 : ℝ)*X 1 1+(5391639983/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1199_s8_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5312634231/10000000000 : ℝ)*X 2 0+(5391639811/10000000000 : ℝ)*X 2 1+(-2078478349/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1199_s8_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((272294743/625000000 : ℝ)*X 0 0+(1120976081/2500000000 : ℝ)*X 0 1+(4233091337/10000000000 : ℝ)*X 0 2+(272294743/625000000 : ℝ)*X 1 0+(1120976081/2500000000 : ℝ)*X 1 1+(4233091337/10000000000 : ℝ)*X 1 2+(272294743/625000000 : ℝ)*X 2 0+(1120976081/2500000000 : ℝ)*X 2 1+(4233091337/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1199_s8_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (13266614899789397475596312451/1328500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1946834779/100000000000000 : ℝ)*(base19) + (431415157/25000000000000 : ℝ)*(base23) + (11483871/12500000000000 : ℝ)*(lower2) + (298646633/100000000000000 : ℝ)*(upper3) + (44782497/50000000000000 : ℝ)*(upper5) + (5973770948924499/100000000000000 : ℝ)*(major0) + (5973770948924499/100000000000000 : ℝ)*(major1) + (5973770948924499/100000000000000 : ℝ)*(major2) + (7980503203406187/100000000000000 : ℝ)*(sp0) + (7980551280894583/100000000000000 : ℝ)*(sp1) + (3990275751034367/50000000000000 : ℝ)*(sp2) + (1983480240288917/50000000000000 : ℝ)*(sp3) + (6253040397/12500000000000 : ℝ)*(sp4) + (13928334879/50000000000000 : ℝ)*(sp7) + (495873542155949/12500000000000 : ℝ)*(f.failure) + (3990276613864681/50000000000000 : ℝ)*(f.sum) + (3505213673791/1660625000000000000000000000 : ℝ)*base66 + (25699483520317329183/2657000000000000000000000000000000 : ℝ)*base68 + (37384404915788329183/2657000000000000000000000000000000 : ℝ)*base70 + (62451029813701670817/2657000000000000000000000000000000 : ℝ)*base71 + (11712362993037/3321250000000000000000000000 : ℝ)*base74 + (11221101500982670817/2657000000000000000000000000000000 : ℝ)*base75 + (27436231711138329183/2657000000000000000000000000000000 : ℝ)*base78 + (35445856233182329183/2657000000000000000000000000000000 : ℝ)*base80 + (10936223477983/13285000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (956009/78125000000000000000 : ℝ)*base89 + (956009/78125000000000000000 : ℝ)*base91 + (956009/78125000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (10046133959191069940810632779/1328500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (391965321/25000000000000 : ℝ)*(base19) + (493026489/25000000000000 : ℝ)*(base23) + (561105229/100000000000000 : ℝ)*(lower1) + (67176961/100000000000000 : ℝ)*(upper2) + (141669247/50000000000000 : ℝ)*(upper3) + (39196359/25000000000000 : ℝ)*(upper5) + (6003928960403771/100000000000000 : ℝ)*(major0) + (6003928960403771/100000000000000 : ℝ)*(major1) + (6003928960403771/100000000000000 : ℝ)*(major2) + (8303198027/100000000000000 : ℝ)*(sp2) + (2005210592539687/25000000000000 : ℝ)*(sp4) + (1002605100287183/12500000000000 : ℝ)*(sp5) + (2005208023713691/25000000000000 : ℝ)*(sp6) + (1993507649290843/50000000000000 : ℝ)*(sp7) + (1993507649290843/50000000000000 : ℝ)*(f.failure) + (2005210592539687/25000000000000 : ℝ)*(f.sum) + (65510095334933/13285000000000000000000000000 : ℝ)*base65 + (24049214833506722407/2657000000000000000000000000000000 : ℝ)*base68 + (46208082211711277593/2657000000000000000000000000000000 : ℝ)*base69 + (20244429742614722407/2657000000000000000000000000000000 : ℝ)*base72 + (21100462746533/13285000000000000000000000000 : ℝ)*base73 + (122915312407556722407/2657000000000000000000000000000000 : ℝ)*base76 + (14130615081586277593/2657000000000000000000000000000000 : ℝ)*base77 + (44691542491788722407/2657000000000000000000000000000000 : ℝ)*base80 + (322268134885343/13285000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (929487/312500000000000000000 : ℝ)*base90 + (929487/312500000000000000000 : ℝ)*base92 + (929487/312500000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1199_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8391/2048 : ℝ) ≤ p) (hpb : p ≤ (1049/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9411691/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7041/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (457/4000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5713/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14081/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1199_s8 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1199_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8391/2048 : ℝ) ≤ p) (hpb : p ≤ (1049/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9411691/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (441/3125 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2849/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5713/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14081/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1199_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1199_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1199_s8 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8391/2048 : ℝ) ≤ p) (hpb : p ≤ (1049/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9411691/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (441/3125 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2849/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5713/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14081/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1199_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
