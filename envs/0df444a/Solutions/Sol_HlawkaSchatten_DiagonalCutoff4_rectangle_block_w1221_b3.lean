-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1221_b3
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T16:11:25.214821+00:00
-- url     : https://prove2.me/submissions/d3d93d20-ef9e-4801-a8c9-b33bc95f83b3

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
theorem support_rectangle_w1221_box_0 (p : ℝ) (hpa : (8413/2048 : ℝ) ≤ p) (hpb : p ≤ (4207/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2005319193/10000000000 : ℝ)*x 0 + (1075031673/2000000000 : ℝ)*x 1 + (1343789587/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2005319193/10000000000 : ℝ)^4207 ≤ (11958855271383/100000000000000 : ℝ)^3183 := by
    have hnat : (2005319193 : ℕ)^4207*100000000000000^3183 ≤ 11958855271383^3183*10000000000^4207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2005319193 10000000000 11958855271383 100000000000000 4207 3183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1075031673/2000000000 : ℝ)^4207 ≤ (44020572450703/100000000000000 : ℝ)^3183 := by
    have hnat : (1075031673 : ℕ)^4207*100000000000000^3183 ≤ 44020572450703^3183*2000000000^4207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1075031673 2000000000 44020572450703 100000000000000 4207 3183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1343789587/2500000000 : ℝ)^4207 ≤ (4402057226669/10000000000000 : ℝ)^3183 := by
    have hnat : (1343789587 : ℕ)^4207*10000000000000^3183 ≤ 4402057226669^3183*2500000000^4207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1343789587 2500000000 4402057226669 10000000000000 4207 3183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4207/1024 : ℝ)) 4207 3183 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2005319193/10000000000 : ℝ), (1075031673/2000000000 : ℝ), (1343789587/2500000000 : ℝ)] ![(11958855271383/100000000000000 : ℝ), (44020572450703/100000000000000 : ℝ), (4402057226669/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2005319193/10000000000 : ℝ)|^4207 ≤ (11958855271383/100000000000000 : ℝ)^3183
        have hw : |(-2005319193/10000000000 : ℝ)|=(2005319193/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1075031673/2000000000 : ℝ)|^4207 ≤ (44020572450703/100000000000000 : ℝ)^3183
        have hw : |(1075031673/2000000000 : ℝ)|=(1075031673/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1343789587/2500000000 : ℝ)|^4207 ≤ (4402057226669/10000000000000 : ℝ)^3183
        have hw : |(1343789587/2500000000 : ℝ)|=(1343789587/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1221_box_1 (p : ℝ) (hpa : (8413/2048 : ℝ) ≤ p) (hpb : p ≤ (4207/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (82760077/156250000 : ℝ)*x 0 + (-42239677/200000000 : ℝ)*x 1 + (5375158367/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (82760077/156250000 : ℝ)^4207 ≤ (8634544388253/20000000000000 : ℝ)^3183 := by
    have hnat : (82760077 : ℕ)^4207*20000000000000^3183 ≤ 8634544388253^3183*156250000^4207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      82760077 156250000 8634544388253 20000000000000 4207 3183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (42239677/200000000 : ℝ)^4207 ≤ (1600838196579/12500000000000 : ℝ)^3183 := by
    have hnat : (42239677 : ℕ)^4207*12500000000000^3183 ≤ 1600838196579^3183*200000000^4207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      42239677 200000000 1600838196579 12500000000000 4207 3183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5375158367/10000000000 : ℝ)^4207 ≤ (1375642889761/3125000000000 : ℝ)^3183 := by
    have hnat : (5375158367 : ℕ)^4207*3125000000000^3183 ≤ 1375642889761^3183*10000000000^4207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5375158367 10000000000 1375642889761 3125000000000 4207 3183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4207/1024 : ℝ)) 4207 3183 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(82760077/156250000 : ℝ), (-42239677/200000000 : ℝ), (5375158367/10000000000 : ℝ)] ![(8634544388253/20000000000000 : ℝ), (1600838196579/12500000000000 : ℝ), (1375642889761/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(82760077/156250000 : ℝ)|^4207 ≤ (8634544388253/20000000000000 : ℝ)^3183
        have hw : |(82760077/156250000 : ℝ)|=(82760077/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-42239677/200000000 : ℝ)|^4207 ≤ (1600838196579/12500000000000 : ℝ)^3183
        have hw : |(-42239677/200000000 : ℝ)|=(42239677/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5375158367/10000000000 : ℝ)|^4207 ≤ (1375642889761/3125000000000 : ℝ)^3183
        have hw : |(5375158367/10000000000 : ℝ)|=(5375158367/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1221_box_2 (p : ℝ) (hpa : (8413/2048 : ℝ) ≤ p) (hpb : p ≤ (4207/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1324161219/2500000000 : ℝ)*x 0 + (1343789599/2500000000 : ℝ)*x 1 + (-2111983881/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1324161219/2500000000 : ℝ)^4207 ≤ (43172721381059/100000000000000 : ℝ)^3183 := by
    have hnat : (1324161219 : ℕ)^4207*100000000000000^3183 ≤ 43172721381059^3183*2500000000^4207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1324161219 2500000000 43172721381059 100000000000000 4207 3183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1343789599/2500000000 : ℝ)^4207 ≤ (44020572786257/100000000000000 : ℝ)^3183 := by
    have hnat : (1343789599 : ℕ)^4207*100000000000000^3183 ≤ 44020572786257^3183*2500000000^4207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1343789599 2500000000 44020572786257 100000000000000 4207 3183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2111983881/10000000000 : ℝ)^4207 ≤ (2561341164217/20000000000000 : ℝ)^3183 := by
    have hnat : (2111983881 : ℕ)^4207*20000000000000^3183 ≤ 2561341164217^3183*10000000000^4207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2111983881 10000000000 2561341164217 20000000000000 4207 3183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4207/1024 : ℝ)) 4207 3183 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1324161219/2500000000 : ℝ), (1343789599/2500000000 : ℝ), (-2111983881/10000000000 : ℝ)] ![(43172721381059/100000000000000 : ℝ), (44020572786257/100000000000000 : ℝ), (2561341164217/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1324161219/2500000000 : ℝ)|^4207 ≤ (43172721381059/100000000000000 : ℝ)^3183
        have hw : |(1324161219/2500000000 : ℝ)|=(1324161219/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1343789599/2500000000 : ℝ)|^4207 ≤ (44020572786257/100000000000000 : ℝ)^3183
        have hw : |(1343789599/2500000000 : ℝ)|=(1343789599/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2111983881/10000000000 : ℝ)|^4207 ≤ (2561341164217/20000000000000 : ℝ)^3183
        have hw : |(-2111983881/10000000000 : ℝ)|=(2111983881/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1221_box_3 (p : ℝ) (hpa : (8413/2048 : ℝ) ≤ p) (hpb : p ≤ (4207/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4460397181/10000000000 : ℝ)*x 0 + (4302351751/10000000000 : ℝ)*x 1 + (4302351767/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4460397181/10000000000 : ℝ)^4207 ≤ (134379756347/390625000000 : ℝ)^3183 := by
    have hnat : (4460397181 : ℕ)^4207*390625000000^3183 ≤ 134379756347^3183*10000000000^4207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4460397181 10000000000 134379756347 390625000000 4207 3183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4302351751/10000000000 : ℝ)^4207 ≤ (32799391102067/100000000000000 : ℝ)^3183 := by
    have hnat : (4302351751 : ℕ)^4207*100000000000000^3183 ≤ 32799391102067^3183*10000000000^4207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4302351751 10000000000 32799391102067 100000000000000 4207 3183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4302351767/10000000000 : ℝ)^4207 ≤ (16399695631643/50000000000000 : ℝ)^3183 := by
    have hnat : (4302351767 : ℕ)^4207*50000000000000^3183 ≤ 16399695631643^3183*10000000000^4207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4302351767 10000000000 16399695631643 50000000000000 4207 3183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4207/1024 : ℝ)) 4207 3183 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4460397181/10000000000 : ℝ), (4302351751/10000000000 : ℝ), (4302351767/10000000000 : ℝ)] ![(134379756347/390625000000 : ℝ), (32799391102067/100000000000000 : ℝ), (16399695631643/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4460397181/10000000000 : ℝ)|^4207 ≤ (134379756347/390625000000 : ℝ)^3183
        have hw : |(4460397181/10000000000 : ℝ)|=(4460397181/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4302351751/10000000000 : ℝ)|^4207 ≤ (32799391102067/100000000000000 : ℝ)^3183
        have hw : |(4302351751/10000000000 : ℝ)|=(4302351751/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4302351767/10000000000 : ℝ)|^4207 ≤ (16399695631643/50000000000000 : ℝ)^3183
        have hw : |(4302351767/10000000000 : ℝ)|=(4302351767/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1221_box_4 (p : ℝ) (hpa : (8413/2048 : ℝ) ≤ p) (hpb : p ≤ (4207/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-451080653/2000000000 : ℝ)*x 0 + (1056413339/2000000000 : ℝ)*x 1 + (1320516671/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (451080653/2000000000 : ℝ)^4207 ≤ (6984262655701/50000000000000 : ℝ)^3183 := by
    have hnat : (451080653 : ℕ)^4207*50000000000000^3183 ≤ 6984262655701^3183*2000000000^4207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      451080653 2000000000 6984262655701 50000000000000 4207 3183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1056413339/2000000000 : ℝ)^4207 ≤ (2688483587361/6250000000000 : ℝ)^3183 := by
    have hnat : (1056413339 : ℕ)^4207*6250000000000^3183 ≤ 2688483587361^3183*2000000000^4207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1056413339 2000000000 2688483587361 6250000000000 4207 3183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1320516671/2500000000 : ℝ)^4207 ≤ (2688483579961/6250000000000 : ℝ)^3183 := by
    have hnat : (1320516671 : ℕ)^4207*6250000000000^3183 ≤ 2688483579961^3183*2500000000^4207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1320516671 2500000000 2688483579961 6250000000000 4207 3183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4207/1024 : ℝ)) 4207 3183 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-451080653/2000000000 : ℝ), (1056413339/2000000000 : ℝ), (1320516671/2500000000 : ℝ)] ![(6984262655701/50000000000000 : ℝ), (2688483587361/6250000000000 : ℝ), (2688483579961/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-451080653/2000000000 : ℝ)|^4207 ≤ (6984262655701/50000000000000 : ℝ)^3183
        have hw : |(-451080653/2000000000 : ℝ)|=(451080653/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1056413339/2000000000 : ℝ)|^4207 ≤ (2688483587361/6250000000000 : ℝ)^3183
        have hw : |(1056413339/2000000000 : ℝ)|=(1056413339/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1320516671/2500000000 : ℝ)|^4207 ≤ (2688483579961/6250000000000 : ℝ)^3183
        have hw : |(1320516671/2500000000 : ℝ)|=(1320516671/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1221_box_5 (p : ℝ) (hpa : (8413/2048 : ℝ) ≤ p) (hpb : p ≤ (4207/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2681149101/5000000000 : ℝ)*x 0 + (-2148829803/10000000000 : ℝ)*x 1 + (2641033429/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2681149101/5000000000 : ℝ)^4207 ≤ (21940711818433/50000000000000 : ℝ)^3183 := by
    have hnat : (2681149101 : ℕ)^4207*50000000000000^3183 ≤ 21940711818433^3183*5000000000^4207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2681149101 5000000000 21940711818433 50000000000000 4207 3183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2148829803/10000000000 : ℝ)^4207 ≤ (6551418598729/50000000000000 : ℝ)^3183 := by
    have hnat : (2148829803 : ℕ)^4207*50000000000000^3183 ≤ 6551418598729^3183*10000000000^4207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2148829803 10000000000 6551418598729 50000000000000 4207 3183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2641033429/5000000000 : ℝ)^4207 ≤ (172062956609/400000000000 : ℝ)^3183 := by
    have hnat : (2641033429 : ℕ)^4207*400000000000^3183 ≤ 172062956609^3183*5000000000^4207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2641033429 5000000000 172062956609 400000000000 4207 3183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4207/1024 : ℝ)) 4207 3183 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2681149101/5000000000 : ℝ), (-2148829803/10000000000 : ℝ), (2641033429/5000000000 : ℝ)] ![(21940711818433/50000000000000 : ℝ), (6551418598729/50000000000000 : ℝ), (172062956609/400000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2681149101/5000000000 : ℝ)|^4207 ≤ (21940711818433/50000000000000 : ℝ)^3183
        have hw : |(2681149101/5000000000 : ℝ)|=(2681149101/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2148829803/10000000000 : ℝ)|^4207 ≤ (6551418598729/50000000000000 : ℝ)^3183
        have hw : |(-2148829803/10000000000 : ℝ)|=(2148829803/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2641033429/5000000000 : ℝ)|^4207 ≤ (172062956609/400000000000 : ℝ)^3183
        have hw : |(2641033429/5000000000 : ℝ)|=(2641033429/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1221_box_6 (p : ℝ) (hpa : (8413/2048 : ℝ) ≤ p) (hpb : p ≤ (4207/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5362298599/10000000000 : ℝ)*x 0 + (660258313/1250000000 : ℝ)*x 1 + (-1074414871/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5362298599/10000000000 : ℝ)^4207 ≤ (43881427930807/100000000000000 : ℝ)^3183 := by
    have hnat : (5362298599 : ℕ)^4207*100000000000000^3183 ≤ 43881427930807^3183*10000000000^4207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5362298599 10000000000 43881427930807 100000000000000 4207 3183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (660258313/1250000000 : ℝ)^4207 ≤ (268848345887/625000000000 : ℝ)^3183 := by
    have hnat : (660258313 : ℕ)^4207*625000000000^3183 ≤ 268848345887^3183*1250000000^4207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      660258313 1250000000 268848345887 625000000000 4207 3183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1074414871/5000000000 : ℝ)^4207 ≤ (6551418352919/50000000000000 : ℝ)^3183 := by
    have hnat : (1074414871 : ℕ)^4207*50000000000000^3183 ≤ 6551418352919^3183*5000000000^4207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1074414871 5000000000 6551418352919 50000000000000 4207 3183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4207/1024 : ℝ)) 4207 3183 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5362298599/10000000000 : ℝ), (660258313/1250000000 : ℝ), (-1074414871/5000000000 : ℝ)] ![(43881427930807/100000000000000 : ℝ), (268848345887/625000000000 : ℝ), (6551418352919/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5362298599/10000000000 : ℝ)|^4207 ≤ (43881427930807/100000000000000 : ℝ)^3183
        have hw : |(5362298599/10000000000 : ℝ)|=(5362298599/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(660258313/1250000000 : ℝ)|^4207 ≤ (268848345887/625000000000 : ℝ)^3183
        have hw : |(660258313/1250000000 : ℝ)|=(660258313/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1074414871/5000000000 : ℝ)|^4207 ≤ (6551418352919/50000000000000 : ℝ)^3183
        have hw : |(-1074414871/5000000000 : ℝ)|=(1074414871/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1221_box_7 (p : ℝ) (hpa : (8413/2048 : ℝ) ≤ p) (hpb : p ≤ (4207/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4246535831/10000000000 : ℝ)*x 0 + (4409262097/10000000000 : ℝ)*x 1 + (176370491/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4246535831/10000000000 : ℝ)^4207 ≤ (32238157187613/100000000000000 : ℝ)^3183 := by
    have hnat : (4246535831 : ℕ)^4207*100000000000000^3183 ≤ 32238157187613^3183*10000000000^4207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4246535831 10000000000 32238157187613 100000000000000 4207 3183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4409262097/10000000000 : ℝ)^4207 ≤ (4235115062201/12500000000000 : ℝ)^3183 := by
    have hnat : (4409262097 : ℕ)^4207*12500000000000^3183 ≤ 4235115062201^3183*10000000000^4207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4409262097 10000000000 4235115062201 12500000000000 4207 3183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (176370491/400000000 : ℝ)^4207 ≤ (16940461152693/50000000000000 : ℝ)^3183 := by
    have hnat : (176370491 : ℕ)^4207*50000000000000^3183 ≤ 16940461152693^3183*400000000^4207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      176370491 400000000 16940461152693 50000000000000 4207 3183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4207/1024 : ℝ)) 4207 3183 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4246535831/10000000000 : ℝ), (4409262097/10000000000 : ℝ), (176370491/400000000 : ℝ)] ![(32238157187613/100000000000000 : ℝ), (4235115062201/12500000000000 : ℝ), (16940461152693/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4246535831/10000000000 : ℝ)|^4207 ≤ (32238157187613/100000000000000 : ℝ)^3183
        have hw : |(4246535831/10000000000 : ℝ)|=(4246535831/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4409262097/10000000000 : ℝ)|^4207 ≤ (4235115062201/12500000000000 : ℝ)^3183
        have hw : |(4409262097/10000000000 : ℝ)|=(4409262097/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(176370491/400000000 : ℝ)|^4207 ≤ (16940461152693/50000000000000 : ℝ)^3183
        have hw : |(176370491/400000000 : ℝ)|=(176370491/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1221_box_8 (p : ℝ) (hpa : (8413/2048 : ℝ) ≤ p) (hpb : p ≤ (4207/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-137688773/625000000 : ℝ)*x 0 + (5218607273/10000000000 : ℝ)*x 1 + (2692385609/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (137688773/625000000 : ℝ)^4207 ≤ (6770669379657/50000000000000 : ℝ)^3183 := by
    have hnat : (137688773 : ℕ)^4207*50000000000000^3183 ≤ 6770669379657^3183*625000000^4207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      137688773 625000000 6770669379657 50000000000000 4207 3183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5218607273/10000000000 : ℝ)^4207 ≤ (42334006333989/100000000000000 : ℝ)^3183 := by
    have hnat : (5218607273 : ℕ)^4207*100000000000000^3183 ≤ 42334006333989^3183*10000000000^4207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5218607273 10000000000 42334006333989 100000000000000 4207 3183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2692385609/5000000000 : ℝ)^4207 ≤ (8824930977971/20000000000000 : ℝ)^3183 := by
    have hnat : (2692385609 : ℕ)^4207*20000000000000^3183 ≤ 8824930977971^3183*5000000000^4207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2692385609 5000000000 8824930977971 20000000000000 4207 3183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4207/1024 : ℝ)) 4207 3183 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-137688773/625000000 : ℝ), (5218607273/10000000000 : ℝ), (2692385609/5000000000 : ℝ)] ![(6770669379657/50000000000000 : ℝ), (42334006333989/100000000000000 : ℝ), (8824930977971/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-137688773/625000000 : ℝ)|^4207 ≤ (6770669379657/50000000000000 : ℝ)^3183
        have hw : |(-137688773/625000000 : ℝ)|=(137688773/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5218607273/10000000000 : ℝ)|^4207 ≤ (42334006333989/100000000000000 : ℝ)^3183
        have hw : |(5218607273/10000000000 : ℝ)|=(5218607273/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2692385609/5000000000 : ℝ)|^4207 ≤ (8824930977971/20000000000000 : ℝ)^3183
        have hw : |(2692385609/5000000000 : ℝ)|=(2692385609/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1221_box_9 (p : ℝ) (hpa : (8413/2048 : ℝ) ≤ p) (hpb : p ≤ (4207/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1057972457/2000000000 : ℝ)*x 0 + (-527027869/2500000000 : ℝ)*x 1 + (5384771189/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1057972457/2000000000 : ℝ)^4207 ≤ (21549833137103/50000000000000 : ℝ)^3183 := by
    have hnat : (1057972457 : ℕ)^4207*50000000000000^3183 ≤ 21549833137103^3183*2000000000^4207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1057972457 2000000000 21549833137103 50000000000000 4207 3183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (527027869/2500000000 : ℝ)^4207 ≤ (6387839570059/50000000000000 : ℝ)^3183 := by
    have hnat : (527027869 : ℕ)^4207*50000000000000^3183 ≤ 6387839570059^3183*2500000000^4207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      527027869 2500000000 6387839570059 50000000000000 4207 3183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5384771189/10000000000 : ℝ)^4207 ≤ (44124654575769/100000000000000 : ℝ)^3183 := by
    have hnat : (5384771189 : ℕ)^4207*100000000000000^3183 ≤ 44124654575769^3183*10000000000^4207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5384771189 10000000000 44124654575769 100000000000000 4207 3183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4207/1024 : ℝ)) 4207 3183 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1057972457/2000000000 : ℝ), (-527027869/2500000000 : ℝ), (5384771189/10000000000 : ℝ)] ![(21549833137103/50000000000000 : ℝ), (6387839570059/50000000000000 : ℝ), (44124654575769/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1057972457/2000000000 : ℝ)|^4207 ≤ (21549833137103/50000000000000 : ℝ)^3183
        have hw : |(1057972457/2000000000 : ℝ)|=(1057972457/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-527027869/2500000000 : ℝ)|^4207 ≤ (6387839570059/50000000000000 : ℝ)^3183
        have hw : |(-527027869/2500000000 : ℝ)|=(527027869/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5384771189/10000000000 : ℝ)|^4207 ≤ (44124654575769/100000000000000 : ℝ)^3183
        have hw : |(5384771189/10000000000 : ℝ)|=(5384771189/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1221_box_10 (p : ℝ) (hpa : (8413/2048 : ℝ) ≤ p) (hpb : p ≤ (4207/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2644931147/5000000000 : ℝ)*x 0 + (2692385617/5000000000 : ℝ)*x 1 + (-2108111403/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2644931147/5000000000 : ℝ)^4207 ≤ (344797330969/800000000000 : ℝ)^3183 := by
    have hnat : (2644931147 : ℕ)^4207*800000000000^3183 ≤ 344797330969^3183*5000000000^4207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2644931147 5000000000 344797330969 800000000000 4207 3183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2692385617/5000000000 : ℝ)^4207 ≤ (44124655063143/100000000000000 : ℝ)^3183 := by
    have hnat : (2692385617 : ℕ)^4207*100000000000000^3183 ≤ 44124655063143^3183*5000000000^4207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2692385617 5000000000 44124655063143 100000000000000 4207 3183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2108111403/10000000000 : ℝ)^4207 ≤ (3193919638849/25000000000000 : ℝ)^3183 := by
    have hnat : (2108111403 : ℕ)^4207*25000000000000^3183 ≤ 3193919638849^3183*10000000000^4207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2108111403 10000000000 3193919638849 25000000000000 4207 3183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4207/1024 : ℝ)) 4207 3183 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2644931147/5000000000 : ℝ), (2692385617/5000000000 : ℝ), (-2108111403/10000000000 : ℝ)] ![(344797330969/800000000000 : ℝ), (44124655063143/100000000000000 : ℝ), (3193919638849/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2644931147/5000000000 : ℝ)|^4207 ≤ (344797330969/800000000000 : ℝ)^3183
        have hw : |(2644931147/5000000000 : ℝ)|=(2644931147/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2692385617/5000000000 : ℝ)|^4207 ≤ (44124655063143/100000000000000 : ℝ)^3183
        have hw : |(2692385617/5000000000 : ℝ)|=(2692385617/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2108111403/10000000000 : ℝ)|^4207 ≤ (3193919638849/25000000000000 : ℝ)^3183
        have hw : |(-2108111403/10000000000 : ℝ)|=(2108111403/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1221_box_11 (p : ℝ) (hpa : (8413/2048 : ℝ) ≤ p) (hpb : p ≤ (4207/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4482208303/10000000000 : ℝ)*x 0 + (1072826411/2500000000 : ℝ)*x 1 + (4291305671/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4482208303/10000000000 : ℝ)^4207 ≤ (17311865278009/50000000000000 : ℝ)^3183 := by
    have hnat : (4482208303 : ℕ)^4207*50000000000000^3183 ≤ 17311865278009^3183*10000000000^4207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4482208303 10000000000 17311865278009 50000000000000 4207 3183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1072826411/2500000000 : ℝ)^4207 ≤ (32688134578173/100000000000000 : ℝ)^3183 := by
    have hnat : (1072826411 : ℕ)^4207*100000000000000^3183 ≤ 32688134578173^3183*2500000000^4207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1072826411 2500000000 32688134578173 100000000000000 4207 3183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4291305671/10000000000 : ℝ)^4207 ≤ (8172033712501/25000000000000 : ℝ)^3183 := by
    have hnat : (4291305671 : ℕ)^4207*25000000000000^3183 ≤ 8172033712501^3183*10000000000^4207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4291305671 10000000000 8172033712501 25000000000000 4207 3183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4207/1024 : ℝ)) 4207 3183 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4482208303/10000000000 : ℝ), (1072826411/2500000000 : ℝ), (4291305671/10000000000 : ℝ)] ![(17311865278009/50000000000000 : ℝ), (32688134578173/100000000000000 : ℝ), (8172033712501/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4482208303/10000000000 : ℝ)|^4207 ≤ (17311865278009/50000000000000 : ℝ)^3183
        have hw : |(4482208303/10000000000 : ℝ)|=(4482208303/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1072826411/2500000000 : ℝ)|^4207 ≤ (32688134578173/100000000000000 : ℝ)^3183
        have hw : |(1072826411/2500000000 : ℝ)|=(1072826411/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4291305671/10000000000 : ℝ)|^4207 ≤ (8172033712501/25000000000000 : ℝ)^3183
        have hw : |(4291305671/10000000000 : ℝ)|=(4291305671/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1221_box_12 (p : ℝ) (hpa : (8413/2048 : ℝ) ≤ p) (hpb : p ≤ (4207/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2057973803/10000000000 : ℝ)*x 0 + (849593/1562500 : ℝ)*x 1 + (5273995043/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2057973803/10000000000 : ℝ)^4207 ≤ (1546953355039/12500000000000 : ℝ)^3183 := by
    have hnat : (2057973803 : ℕ)^4207*12500000000000^3183 ≤ 1546953355039^3183*10000000000^4207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2057973803 10000000000 1546953355039 12500000000000 4207 3183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (849593/1562500 : ℝ)^4207 ≤ (5586936848009/12500000000000 : ℝ)^3183 := by
    have hnat : (849593 : ℕ)^4207*12500000000000^3183 ≤ 5586936848009^3183*1562500^4207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      849593 1562500 5586936848009 12500000000000 4207 3183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5273995043/10000000000 : ℝ)^4207 ≤ (42928878364301/100000000000000 : ℝ)^3183 := by
    have hnat : (5273995043 : ℕ)^4207*100000000000000^3183 ≤ 42928878364301^3183*10000000000^4207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5273995043 10000000000 42928878364301 100000000000000 4207 3183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4207/1024 : ℝ)) 4207 3183 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2057973803/10000000000 : ℝ), (849593/1562500 : ℝ), (5273995043/10000000000 : ℝ)] ![(1546953355039/12500000000000 : ℝ), (5586936848009/12500000000000 : ℝ), (42928878364301/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2057973803/10000000000 : ℝ)|^4207 ≤ (1546953355039/12500000000000 : ℝ)^3183
        have hw : |(-2057973803/10000000000 : ℝ)|=(2057973803/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(849593/1562500 : ℝ)|^4207 ≤ (5586936848009/12500000000000 : ℝ)^3183
        have hw : |(849593/1562500 : ℝ)|=(849593/1562500 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5273995043/10000000000 : ℝ)|^4207 ≤ (42928878364301/100000000000000 : ℝ)^3183
        have hw : |(5273995043/10000000000 : ℝ)|=(5273995043/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1221_box_13 (p : ℝ) (hpa : (8413/2048 : ℝ) ≤ p) (hpb : p ≤ (4207/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5367988479/10000000000 : ℝ)*x 0 + (-53799211/250000000 : ℝ)*x 1 + (2636997667/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5367988479/10000000000 : ℝ)^4207 ≤ (43942980025877/100000000000000 : ℝ)^3183 := by
    have hnat : (5367988479 : ℕ)^4207*100000000000000^3183 ≤ 43942980025877^3183*10000000000^4207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5367988479 10000000000 43942980025877 100000000000000 4207 3183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (53799211/250000000 : ℝ)^4207 ≤ (13128138465107/100000000000000 : ℝ)^3183 := by
    have hnat : (53799211 : ℕ)^4207*100000000000000^3183 ≤ 13128138465107^3183*250000000^4207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      53799211 250000000 13128138465107 100000000000000 4207 3183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2636997667/5000000000 : ℝ)^4207 ≤ (42928881494981/100000000000000 : ℝ)^3183 := by
    have hnat : (2636997667 : ℕ)^4207*100000000000000^3183 ≤ 42928881494981^3183*5000000000^4207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2636997667 5000000000 42928881494981 100000000000000 4207 3183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4207/1024 : ℝ)) 4207 3183 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5367988479/10000000000 : ℝ), (-53799211/250000000 : ℝ), (2636997667/5000000000 : ℝ)] ![(43942980025877/100000000000000 : ℝ), (13128138465107/100000000000000 : ℝ), (42928881494981/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5367988479/10000000000 : ℝ)|^4207 ≤ (43942980025877/100000000000000 : ℝ)^3183
        have hw : |(5367988479/10000000000 : ℝ)|=(5367988479/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-53799211/250000000 : ℝ)|^4207 ≤ (13128138465107/100000000000000 : ℝ)^3183
        have hw : |(-53799211/250000000 : ℝ)|=(53799211/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2636997667/5000000000 : ℝ)|^4207 ≤ (42928881494981/100000000000000 : ℝ)^3183
        have hw : |(2636997667/5000000000 : ℝ)|=(2636997667/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1221_box_14 (p : ℝ) (hpa : (8413/2048 : ℝ) ≤ p) (hpb : p ≤ (4207/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1341997257/2500000000 : ℝ)*x 0 + (164812347/312500000 : ℝ)*x 1 + (-215196801/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1341997257/2500000000 : ℝ)^4207 ≤ (43942985965873/100000000000000 : ℝ)^3183 := by
    have hnat : (1341997257 : ℕ)^4207*100000000000000^3183 ≤ 43942985965873^3183*2500000000^4207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1341997257 2500000000 43942985965873 100000000000000 4207 3183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (164812347/312500000 : ℝ)^4207 ≤ (536610987757/1250000000000 : ℝ)^3183 := by
    have hnat : (164812347 : ℕ)^4207*1250000000000^3183 ≤ 536610987757^3183*312500000^4207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      164812347 312500000 536610987757 1250000000000 4207 3183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (215196801/1000000000 : ℝ)^4207 ≤ (6564067498983/50000000000000 : ℝ)^3183 := by
    have hnat : (215196801 : ℕ)^4207*50000000000000^3183 ≤ 6564067498983^3183*1000000000^4207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      215196801 1000000000 6564067498983 50000000000000 4207 3183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4207/1024 : ℝ)) 4207 3183 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1341997257/2500000000 : ℝ), (164812347/312500000 : ℝ), (-215196801/1000000000 : ℝ)] ![(43942985965873/100000000000000 : ℝ), (536610987757/1250000000000 : ℝ), (6564067498983/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1341997257/2500000000 : ℝ)|^4207 ≤ (43942985965873/100000000000000 : ℝ)^3183
        have hw : |(1341997257/2500000000 : ℝ)|=(1341997257/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(164812347/312500000 : ℝ)|^4207 ≤ (536610987757/1250000000000 : ℝ)^3183
        have hw : |(164812347/312500000 : ℝ)|=(164812347/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-215196801/1000000000 : ℝ)|^4207 ≤ (6564067498983/50000000000000 : ℝ)^3183
        have hw : |(-215196801/1000000000 : ℝ)|=(215196801/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1221_box_15 (p : ℝ) (hpa : (8413/2048 : ℝ) ≤ p) (hpb : p ≤ (4207/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4227760211/10000000000 : ℝ)*x 0 + (276157993/625000000 : ℝ)*x 1 + (4418526867/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4227760211/10000000000 : ℝ)^4207 ≤ (8012474488589/25000000000000 : ℝ)^3183 := by
    have hnat : (4227760211 : ℕ)^4207*25000000000000^3183 ≤ 8012474488589^3183*10000000000^4207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4227760211 10000000000 8012474488589 25000000000000 4207 3183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (276157993/625000000 : ℝ)^4207 ≤ (33975056200033/100000000000000 : ℝ)^3183 := by
    have hnat : (276157993 : ℕ)^4207*100000000000000^3183 ≤ 33975056200033^3183*625000000^4207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      276157993 625000000 33975056200033 100000000000000 4207 3183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4418526867/10000000000 : ℝ)^4207 ≤ (33975045823693/100000000000000 : ℝ)^3183 := by
    have hnat : (4418526867 : ℕ)^4207*100000000000000^3183 ≤ 33975045823693^3183*10000000000^4207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4418526867 10000000000 33975045823693 100000000000000 4207 3183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4207/1024 : ℝ)) 4207 3183 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4227760211/10000000000 : ℝ), (276157993/625000000 : ℝ), (4418526867/10000000000 : ℝ)] ![(8012474488589/25000000000000 : ℝ), (33975056200033/100000000000000 : ℝ), (33975045823693/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4227760211/10000000000 : ℝ)|^4207 ≤ (8012474488589/25000000000000 : ℝ)^3183
        have hw : |(4227760211/10000000000 : ℝ)|=(4227760211/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(276157993/625000000 : ℝ)|^4207 ≤ (33975056200033/100000000000000 : ℝ)^3183
        have hw : |(276157993/625000000 : ℝ)|=(276157993/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4418526867/10000000000 : ℝ)|^4207 ≤ (33975045823693/100000000000000 : ℝ)^3183
        have hw : |(4418526867/10000000000 : ℝ)|=(4418526867/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1221_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (8413/2048 : ℝ) ≤ p) (hpb : p ≤ (4207/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (2359647/1562500 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14093/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5727/50000 : ℝ)*pair X i i ≤ pair X i h) :
    -(62243/100000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(371/625 : ℝ) ∧ (80047/100000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (833/1000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14093/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5727/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14093/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5727/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14093/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5727/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14093/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5727/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14093/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5727/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14093/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5727/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5727/50000 : ℝ) ^ (8413/2048 : ℝ) ≤ (2724649440443311/20000000000000000000 : ℝ) := by
    have hpowers : (5727/50000 : ℝ)^8413 ≤ (2724649440443311/20000000000000000000 : ℝ)^2048 := by
      have hnat : (5727 : ℕ)^8413*20000000000000000000^2048 ≤ 2724649440443311^2048*50000^8413 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5727 50000 2724649440443311 20000000000000000000 8413 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5727/50000 : ℝ)) (X := (2724649440443311/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8413 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (14093/100000 : ℝ) ^ (8413/2048 : ℝ) ≤ (31928802996460007/100000000000000000000 : ℝ) := by
    have hpowers : (14093/100000 : ℝ)^8413 ≤ (31928802996460007/100000000000000000000 : ℝ)^2048 := by
      have hnat : (14093 : ℕ)^8413*100000000000000000000^2048 ≤ 31928802996460007^2048*100000^8413 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14093 100000 31928802996460007 100000000000000000000 8413 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14093/100000 : ℝ)) (X := (31928802996460007/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8413 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (10002724649440443311/10000000000000000000 : ℝ) ≤ (1000066320064331/1000000000000000 : ℝ) ^ (8413/2048 : ℝ) := by
    have hpowers : (10002724649440443311/10000000000000000000 : ℝ)^2048 ≤ (1000066320064331/1000000000000000 : ℝ)^8413 := by
      have hnat : (10002724649440443311 : ℕ)^2048*1000000000000000^8413 ≤ 1000066320064331^8413*10000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10002724649440443311 10000000000000000000 1000066320064331 1000000000000000 2048 8413 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000066320064331/1000000000000000 : ℝ)) (X := (10002724649440443311/10000000000000000000 : ℝ)) (by norm_num) 8413 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (50022776025099338281/50000000000000000000 : ℝ) ≤ (2500277173801367/2500000000000000 : ℝ) ^ (8413/2048 : ℝ) := by
    have hpowers : (50022776025099338281/50000000000000000000 : ℝ)^2048 ≤ (2500277173801367/2500000000000000 : ℝ)^8413 := by
      have hnat : (50022776025099338281 : ℕ)^2048*2500000000000000^8413 ≤ 2500277173801367^8413*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50022776025099338281 50000000000000000000 2500277173801367 2500000000000000 2048 8413 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500277173801367/2500000000000000 : ℝ)) (X := (50022776025099338281/50000000000000000000 : ℝ)) (by norm_num) 8413 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50031928802996460007/50000000000000000000 : ℝ) ≤ (5000777094883813/5000000000000000 : ℝ) ^ (8413/2048 : ℝ) := by
    have hpowers : (50031928802996460007/50000000000000000000 : ℝ)^2048 ≤ (5000777094883813/5000000000000000 : ℝ)^8413 := by
      have hnat : (50031928802996460007 : ℕ)^2048*5000000000000000^8413 ≤ 5000777094883813^8413*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50031928802996460007 50000000000000000000 5000777094883813 5000000000000000 2048 8413 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000777094883813/5000000000000000 : ℝ)) (X := (50031928802996460007/50000000000000000000 : ℝ)) (by norm_num) 8413 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2724649440443311/20000000000000000000 : ℝ) ≤ ((13190772398533889813/13195000000000000000 : ℝ)+2*(222747281079/131950000000000 : ℝ)*(5727/50000 : ℝ))^(8413/2048 : ℝ) := by
    rw [show (13190772398533889813/13195000000000000000 : ℝ)+2*(222747281079/131950000000000 : ℝ)*(5727/50000 : ℝ)=(1000066320064331/1000000000000000 : ℝ) by norm_num, show 1+2*(2724649440443311/20000000000000000000 : ℝ)=(10002724649440443311/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(31928802996460007/100000000000000000000 : ℝ)+(2724649440443311/20000000000000000000 : ℝ) ≤ ((13190772398533889813/13195000000000000000 : ℝ)+(222747281079/131950000000000 : ℝ)*((14093/100000 : ℝ)+(5727/50000 : ℝ)))^(8413/2048 : ℝ) := by
    rw [show (13190772398533889813/13195000000000000000 : ℝ)+(222747281079/131950000000000 : ℝ)*((14093/100000 : ℝ)+(5727/50000 : ℝ))=(2500277173801367/2500000000000000 : ℝ) by norm_num, show 1+(31928802996460007/100000000000000000000 : ℝ)+(2724649440443311/20000000000000000000 : ℝ)=(50022776025099338281/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(31928802996460007/100000000000000000000 : ℝ) ≤ ((13190772398533889813/13195000000000000000 : ℝ)+2*(222747281079/131950000000000 : ℝ)*(14093/100000 : ℝ))^(8413/2048 : ℝ) := by
    rw [show (13190772398533889813/13195000000000000000 : ℝ)+2*(222747281079/131950000000000 : ℝ)*(14093/100000 : ℝ)=(5000777094883813/5000000000000000 : ℝ) by norm_num, show 1+2*(31928802996460007/100000000000000000000 : ℝ)=(50031928802996460007/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (13190772398533889813/13195000000000000000 : ℝ)*(X 1 0+X 2 0)+(222747281079/131950000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8413/2048 : ℝ)) (lo := (5727/50000 : ℝ)) (hi := (14093/100000 : ℝ)) (c := (13190772398533889813/13195000000000000000 : ℝ)) (alpha := (222747281079/131950000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (13190772398533889813/13195000000000000000 : ℝ)*(X 0 1+X 2 1)+(222747281079/131950000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8413/2048 : ℝ)) (lo := (5727/50000 : ℝ)) (hi := (14093/100000 : ℝ)) (c := (13190772398533889813/13195000000000000000 : ℝ)) (alpha := (222747281079/131950000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (13190772398533889813/13195000000000000000 : ℝ)*(X 0 2+X 1 2)+(222747281079/131950000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8413/2048 : ℝ)) (lo := (5727/50000 : ℝ)) (hi := (14093/100000 : ℝ)) (c := (13190772398533889813/13195000000000000000 : ℝ)) (alpha := (222747281079/131950000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2005319193/10000000000 : ℝ)*X 0 0+(1075031673/2000000000 : ℝ)*X 0 1+(1343789587/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1221_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((82760077/156250000 : ℝ)*X 1 0+(-42239677/200000000 : ℝ)*X 1 1+(5375158367/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1221_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1324161219/2500000000 : ℝ)*X 2 0+(1343789599/2500000000 : ℝ)*X 2 1+(-2111983881/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1221_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4460397181/10000000000 : ℝ)*X 0 0+(4302351751/10000000000 : ℝ)*X 0 1+(4302351767/10000000000 : ℝ)*X 0 2+(4460397181/10000000000 : ℝ)*X 1 0+(4302351751/10000000000 : ℝ)*X 1 1+(4302351767/10000000000 : ℝ)*X 1 2+(4460397181/10000000000 : ℝ)*X 2 0+(4302351751/10000000000 : ℝ)*X 2 1+(4302351767/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1221_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-451080653/2000000000 : ℝ)*X 0 0+(1056413339/2000000000 : ℝ)*X 0 1+(1320516671/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1221_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2681149101/5000000000 : ℝ)*X 1 0+(-2148829803/10000000000 : ℝ)*X 1 1+(2641033429/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1221_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5362298599/10000000000 : ℝ)*X 2 0+(660258313/1250000000 : ℝ)*X 2 1+(-1074414871/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1221_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4246535831/10000000000 : ℝ)*X 0 0+(4409262097/10000000000 : ℝ)*X 0 1+(176370491/400000000 : ℝ)*X 0 2+(4246535831/10000000000 : ℝ)*X 1 0+(4409262097/10000000000 : ℝ)*X 1 1+(176370491/400000000 : ℝ)*X 1 2+(4246535831/10000000000 : ℝ)*X 2 0+(4409262097/10000000000 : ℝ)*X 2 1+(176370491/400000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1221_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-137688773/625000000 : ℝ)*X 0 0+(5218607273/10000000000 : ℝ)*X 0 1+(2692385609/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1221_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((1057972457/2000000000 : ℝ)*X 1 0+(-527027869/2500000000 : ℝ)*X 1 1+(5384771189/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1221_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((2644931147/5000000000 : ℝ)*X 2 0+(2692385617/5000000000 : ℝ)*X 2 1+(-2108111403/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1221_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((4482208303/10000000000 : ℝ)*X 0 0+(1072826411/2500000000 : ℝ)*X 0 1+(4291305671/10000000000 : ℝ)*X 0 2+(4482208303/10000000000 : ℝ)*X 1 0+(1072826411/2500000000 : ℝ)*X 1 1+(4291305671/10000000000 : ℝ)*X 1 2+(4482208303/10000000000 : ℝ)*X 2 0+(1072826411/2500000000 : ℝ)*X 2 1+(4291305671/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1221_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-2057973803/10000000000 : ℝ)*X 0 0+(849593/1562500 : ℝ)*X 0 1+(5273995043/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1221_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((5367988479/10000000000 : ℝ)*X 1 0+(-53799211/250000000 : ℝ)*X 1 1+(2636997667/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1221_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((1341997257/2500000000 : ℝ)*X 2 0+(164812347/312500000 : ℝ)*X 2 1+(-215196801/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1221_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((4227760211/10000000000 : ℝ)*X 0 0+(276157993/625000000 : ℝ)*X 0 1+(4418526867/10000000000 : ℝ)*X 0 2+(4227760211/10000000000 : ℝ)*X 1 0+(276157993/625000000 : ℝ)*X 1 1+(4418526867/10000000000 : ℝ)*X 1 2+(4227760211/10000000000 : ℝ)*X 2 0+(276157993/625000000 : ℝ)*X 2 1+(4418526867/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1221_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-62243/100000 : ℝ) ≤ (-102657518446751348735873627333139/164937500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (75760283/100000000000000 : ℝ)*(upper0) + (13199967/50000000000000 : ℝ)*(lower1) + (130577743/100000000000000 : ℝ)*(lower2) + (3391053/100000000000000 : ℝ)*(lower3) + (19594743/100000000000000 : ℝ)*(upper5) + (1992943834336699/50000000000000 : ℝ)*(major0) + (1992943834336699/50000000000000 : ℝ)*(major1) + (1992943834336699/50000000000000 : ℝ)*(major2) + (989987933/20000000000000 : ℝ)*(sp2) + (5353165658443721/100000000000000 : ℝ)*(sp4) + (5353078765068887/100000000000000 : ℝ)*(sp5) + (669145088563007/12500000000000 : ℝ)*(sp6) + (52787128602729/2000000000000 : ℝ)*(sp7) + (43446687417/50000000000000 : ℝ)*(sp13) + (52787128602729/2000000000000 : ℝ)*(f.failure) + (5353165658443721/100000000000000 : ℝ)*(f.sum) + (2102342345309/13195000000000000000000000000 : ℝ)*base65 + (13842047707733502713/659750000000000000000000000000000 : ℝ)*base68 + (30972719837518747287/659750000000000000000000000000000 : ℝ)*base69 + (9576837100917252713/659750000000000000000000000000000 : ℝ)*base72 + (266671770297229/13195000000000000000000000000 : ℝ)*base73 + (4756424356451752713/659750000000000000000000000000000 : ℝ)*base76 + (7267214269401252713/659750000000000000000000000000000 : ℝ)*base78 + (19079107230906252713/659750000000000000000000000000000 : ℝ)*base80 + (663931089928949/13195000000000000000000000000 : ℝ)*base81 + (10837/3125000000000000000 : ℝ)*base90 + (10837/3125000000000000000 : ℝ)*base92 + (10837/3125000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (371/625 : ℝ) ≤ (3916472023417838984961189429/6597500000000000000000000000 : ℝ) := by norm_num
    linear_combination (5226827/50000000000000 : ℝ)*(lower0) + (2978021/12500000000000 : ℝ)*(upper2) + (3283319/50000000000000 : ℝ)*(lower4) + (698343/100000000000000 : ℝ)*(lower5) + (2025673871461789/50000000000000 : ℝ)*(major0) + (2025673871461789/50000000000000 : ℝ)*(major1) + (2025673871461789/50000000000000 : ℝ)*(major2) + (2700102676620311/50000000000000 : ℝ)*(sp0) + (5400204251057347/100000000000000 : ℝ)*(sp1) + (540020460287217/10000000000000 : ℝ)*(sp2) + (2682701718781131/100000000000000 : ℝ)*(sp3) + (551091637/50000000000000 : ℝ)*(sp5) + (750368451/100000000000000 : ℝ)*(sp6) + (756766309/100000000000000 : ℝ)*(sp7) + (33533780944343/1250000000000 : ℝ)*(f.failure) + (2700102676620311/50000000000000 : ℝ)*(f.sum) + (4456974934859/824687500000000000000000000 : ℝ)*base65 + (2791900279004955457/659750000000000000000000000000000 : ℝ)*base67 + (4069242764204044543/659750000000000000000000000000000 : ℝ)*base70 + (15251513714827544543/659750000000000000000000000000000 : ℝ)*base72 + (76436305692083/6597500000000000000000000000 : ℝ)*base74 + (1099771163942205457/659750000000000000000000000000000 : ℝ)*base75 + (35169720570298705457/659750000000000000000000000000000 : ℝ)*base77 + (18171393122636544543/659750000000000000000000000000000 : ℝ)*base80 + (2286206608381/3298750000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (11783/3906250000000000000 : ℝ)*base90 + (11783/3906250000000000000 : ℝ)*base92 + (11783/3906250000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (80047/100000 : ℝ) ≤ (18861565079082462235225577008077/23562500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (954063/2000000000000 : ℝ)*(lower3) + (24588071/100000000000000 : ℝ)*(upper4) + (6638743/100000000000000 : ℝ)*(lower5) + (2259204589646099/50000000000000 : ℝ)*(major0) + (2259204589646099/50000000000000 : ℝ)*(major1) + (2259204589646099/50000000000000 : ℝ)*(major2) + (272369629/25000000000000 : ℝ)*(sp0) + (32558389339/100000000000000 : ℝ)*(sp1) + (6082480781/10000000000000 : ℝ)*(sp2) + (1046799889/4000000000000 : ℝ)*(sp3) + (6018155211397453/100000000000000 : ℝ)*(sp8) + (601812374248663/10000000000000 : ℝ)*(sp9) + (6018095476068159/100000000000000 : ℝ)*(sp10) + (1495976430094971/50000000000000 : ℝ)*(sp11) + (2991979030187167/100000000000000 : ℝ)*(f.failure) + (6018156300875969/100000000000000 : ℝ)*(f.sum) + (79379943258779/13195000000000000000000000000 : ℝ)*base65 + (11093545464901389487/659750000000000000000000000000000 : ℝ)*base67 + (6679645403781860513/659750000000000000000000000000000 : ℝ)*base70 + (8045831883056639487/659750000000000000000000000000000 : ℝ)*base71 + (157999029128649/13195000000000000000000000000 : ℝ)*base73 + (5661510658248389487/659750000000000000000000000000000 : ℝ)*base75 + (279250816357639487/659750000000000000000000000000000 : ℝ)*base77 + (2167293590520639487/659750000000000000000000000000000 : ℝ)*base79 + (27674126130433/6597500000000000000000000000 : ℝ)*base82 + (1324951/156250000000000000000 : ℝ)*base90 + (1324951/156250000000000000000 : ℝ)*base92 + (1324951/156250000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (-833/1000 : ℝ) ≤ (-274776885467552787245945597526711/329875000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (19145279/10000000000000 : ℝ)*(lower0) + (40508953/100000000000000 : ℝ)*(upper1) + (83995793/25000000000000 : ℝ)*(lower2) + (217657801/100000000000000 : ℝ)*(upper3) + (404932123/100000000000000 : ℝ)*(upper5) + (4553770290532849/100000000000000 : ℝ)*(major0) + (4553770290532849/100000000000000 : ℝ)*(major1) + (4553770290532849/100000000000000 : ℝ)*(major2) + (1165303627/100000000000000 : ℝ)*(sp4) + (117250216739/50000000000000 : ℝ)*(sp7) + (1223982177764427/20000000000000 : ℝ)*(sp12) + (6119912054125763/100000000000000 : ℝ)*(sp13) + (6119912054125763/100000000000000 : ℝ)*(sp14) + (1507579892397723/50000000000000 : ℝ)*(sp15) + (753848571307231/25000000000000 : ℝ)*(f.failure) + (6119912054125763/100000000000000 : ℝ)*(f.sum) + (20812380116081/6597500000000000000000000000 : ℝ)*base65 + (20884865918639567237/1319500000000000000000000000000000 : ℝ)*base67 + (28306797929132567237/1319500000000000000000000000000000 : ℝ)*base69 + (5720383356410567237/1319500000000000000000000000000000 : ℝ)*base71 + (339447693953/3298750000000000000000000000 : ℝ)*base73 + (1268329431137067237/1319500000000000000000000000000000 : ℝ)*base75 + (8735382947514067237/1319500000000000000000000000000000 : ℝ)*base77 + (30338268681406932763/1319500000000000000000000000000000 : ℝ)*base80 + (19884255086063/3298750000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (27073/2441406250000000000 : ℝ)*base90 + (27073/2441406250000000000 : ℝ)*base92 + (27073/2441406250000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1221_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (8413/2048 : ℝ) ≤ p) (hpb : p ≤ (4207/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (2359647/1562500 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14093/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5727/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62243/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(371/625 : ℝ) else (80047/100000 : ℝ) ≤ X j i ∧ X j i ≤ (833/1000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1221_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1221_b3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8413/2048 : ℝ) ≤ p) (hpb : p ≤ (4207/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (2359647/1562500 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14093/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5727/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62243/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(371/625 : ℝ) else (80047/100000 : ℝ) ≤ X j i ∧ X j i ≤ (833/1000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1221_box p A d hA hpa hpb X hX hsign hratio hlower
  exact h0
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8413/2048 : ℝ) ≤ p) (hpb : p ≤ (4207/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (2359647/1562500 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14093/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5727/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62243/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(371/625 : ℝ) else (80047/100000 : ℝ) ≤ X j i ∧ X j i ≤ (833/1000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1221_b3 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
