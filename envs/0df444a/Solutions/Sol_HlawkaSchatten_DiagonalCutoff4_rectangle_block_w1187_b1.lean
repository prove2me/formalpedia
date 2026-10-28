-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1187_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:52:07.773353+00:00
-- url     : https://prove2.me/submissions/3d84a396-f68f-4737-8e55-ae3cecfddb54

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
theorem support_rectangle_w1187_s3_0 (p : ℝ) (hpa : (8379/2048 : ℝ) ≤ p) (hpb : p ≤ (2095/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-267776699/1250000000 : ℝ)*x 0 + (5424701/10000000 : ℝ)*x 1 + (2618068703/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (267776699/1250000000 : ℝ)^2095 ≤ (13014855730431/100000000000000 : ℝ)^1583 := by
    have hnat : (267776699 : ℕ)^2095*100000000000000^1583 ≤ 13014855730431^1583*1250000000^2095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      267776699 1250000000 13014855730431 100000000000000 2095 1583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5424701/10000000 : ℝ)^2095 ≤ (22255289436673/50000000000000 : ℝ)^1583 := by
    have hnat : (5424701 : ℕ)^2095*50000000000000^1583 ≤ 22255289436673^1583*10000000^2095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5424701 10000000 22255289436673 50000000000000 2095 1583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2618068703/5000000000 : ℝ)^2095 ≤ (1327330168011/3125000000000 : ℝ)^1583 := by
    have hnat : (2618068703 : ℕ)^2095*3125000000000^1583 ≤ 1327330168011^1583*5000000000^2095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2618068703 5000000000 1327330168011 3125000000000 2095 1583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2095/512 : ℝ)) 2095 1583 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-267776699/1250000000 : ℝ), (5424701/10000000 : ℝ), (2618068703/5000000000 : ℝ)] ![(13014855730431/100000000000000 : ℝ), (22255289436673/50000000000000 : ℝ), (1327330168011/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-267776699/1250000000 : ℝ)|^2095 ≤ (13014855730431/100000000000000 : ℝ)^1583
        have hw : |(-267776699/1250000000 : ℝ)|=(267776699/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5424701/10000000 : ℝ)|^2095 ≤ (22255289436673/50000000000000 : ℝ)^1583
        have hw : |(5424701/10000000 : ℝ)|=(5424701/10000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2618068703/5000000000 : ℝ)|^2095 ≤ (1327330168011/3125000000000 : ℝ)^1583
        have hw : |(2618068703/5000000000 : ℝ)|=(2618068703/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1187_s3_1 (p : ℝ) (hpa : (8379/2048 : ℝ) ≤ p) (hpb : p ≤ (2095/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5352732029/10000000000 : ℝ)*x 0 + (-89540377/400000000 : ℝ)*x 1 + (5236137167/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5352732029/10000000000 : ℝ)^2095 ≤ (170823235579/390625000000 : ℝ)^1583 := by
    have hnat : (5352732029 : ℕ)^2095*390625000000^1583 ≤ 170823235579^1583*10000000000^2095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5352732029 10000000000 170823235579 390625000000 2095 1583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (89540377/400000000 : ℝ)^2095 ≤ (2758937772299/20000000000000 : ℝ)^1583 := by
    have hnat : (89540377 : ℕ)^2095*20000000000000^1583 ≤ 2758937772299^1583*400000000^2095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      89540377 400000000 2758937772299 20000000000000 2095 1583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5236137167/10000000000 : ℝ)^2095 ≤ (1698982512423/4000000000000 : ℝ)^1583 := by
    have hnat : (5236137167 : ℕ)^2095*4000000000000^1583 ≤ 1698982512423^1583*10000000000^2095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5236137167 10000000000 1698982512423 4000000000000 2095 1583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2095/512 : ℝ)) 2095 1583 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5352732029/10000000000 : ℝ), (-89540377/400000000 : ℝ), (5236137167/10000000000 : ℝ)] ![(170823235579/390625000000 : ℝ), (2758937772299/20000000000000 : ℝ), (1698982512423/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5352732029/10000000000 : ℝ)|^2095 ≤ (170823235579/390625000000 : ℝ)^1583
        have hw : |(5352732029/10000000000 : ℝ)|=(5352732029/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-89540377/400000000 : ℝ)|^2095 ≤ (2758937772299/20000000000000 : ℝ)^1583
        have hw : |(-89540377/400000000 : ℝ)|=(89540377/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5236137167/10000000000 : ℝ)|^2095 ≤ (1698982512423/4000000000000 : ℝ)^1583
        have hw : |(5236137167/10000000000 : ℝ)|=(5236137167/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1187_s3_2 (p : ℝ) (hpa : (8379/2048 : ℝ) ≤ p) (hpb : p ≤ (2095/512 : ℝ)) (x : Fin 3 → ℝ) :
    (669091517/1250000000 : ℝ)*x 0 + (5236137099/10000000000 : ℝ)*x 1 + (-1119254687/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (669091517/1250000000 : ℝ)^2095 ≤ (4373074946513/10000000000000 : ℝ)^1583 := by
    have hnat : (669091517 : ℕ)^2095*10000000000000^1583 ≤ 4373074946513^1583*1250000000^2095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      669091517 1250000000 4373074946513 10000000000000 2095 1583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5236137099/10000000000 : ℝ)^2095 ≤ (42474562080563/100000000000000 : ℝ)^1583 := by
    have hnat : (5236137099 : ℕ)^2095*100000000000000^1583 ≤ 42474562080563^1583*10000000000^2095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5236137099 10000000000 42474562080563 100000000000000 2095 1583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1119254687/5000000000 : ℝ)^2095 ≤ (13794688445559/100000000000000 : ℝ)^1583 := by
    have hnat : (1119254687 : ℕ)^2095*100000000000000^1583 ≤ 13794688445559^1583*5000000000^2095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1119254687 5000000000 13794688445559 100000000000000 2095 1583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2095/512 : ℝ)) 2095 1583 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(669091517/1250000000 : ℝ), (5236137099/10000000000 : ℝ), (-1119254687/5000000000 : ℝ)] ![(4373074946513/10000000000000 : ℝ), (42474562080563/100000000000000 : ℝ), (13794688445559/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(669091517/1250000000 : ℝ)|^2095 ≤ (4373074946513/10000000000000 : ℝ)^1583
        have hw : |(669091517/1250000000 : ℝ)|=(669091517/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5236137099/10000000000 : ℝ)|^2095 ≤ (42474562080563/100000000000000 : ℝ)^1583
        have hw : |(5236137099/10000000000 : ℝ)|=(5236137099/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1119254687/5000000000 : ℝ)|^2095 ≤ (13794688445559/100000000000000 : ℝ)^1583
        have hw : |(-1119254687/5000000000 : ℝ)|=(1119254687/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1187_s3_3 (p : ℝ) (hpa : (8379/2048 : ℝ) ≤ p) (hpb : p ≤ (2095/512 : ℝ)) (x : Fin 3 → ℝ) :
    (217819277/500000000 : ℝ)*x 0 + (417119903/1000000000 : ℝ)*x 1 + (909931137/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (217819277/500000000 : ℝ)^2095 ≤ (8324278235579/25000000000000 : ℝ)^1583 := by
    have hnat : (217819277 : ℕ)^2095*25000000000000^1583 ≤ 8324278235579^1583*500000000^2095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      217819277 500000000 8324278235579 25000000000000 2095 1583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (417119903/1000000000 : ℝ)^2095 ≤ (31436879228529/100000000000000 : ℝ)^1583 := by
    have hnat : (417119903 : ℕ)^2095*100000000000000^1583 ≤ 31436879228529^1583*1000000000^2095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      417119903 1000000000 31436879228529 100000000000000 2095 1583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (909931137/2000000000 : ℝ)^2095 ≤ (3526600781487/10000000000000 : ℝ)^1583 := by
    have hnat : (909931137 : ℕ)^2095*10000000000000^1583 ≤ 3526600781487^1583*2000000000^2095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      909931137 2000000000 3526600781487 10000000000000 2095 1583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2095/512 : ℝ)) 2095 1583 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(217819277/500000000 : ℝ), (417119903/1000000000 : ℝ), (909931137/2000000000 : ℝ)] ![(8324278235579/25000000000000 : ℝ), (31436879228529/100000000000000 : ℝ), (3526600781487/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(217819277/500000000 : ℝ)|^2095 ≤ (8324278235579/25000000000000 : ℝ)^1583
        have hw : |(217819277/500000000 : ℝ)|=(217819277/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(417119903/1000000000 : ℝ)|^2095 ≤ (31436879228529/100000000000000 : ℝ)^1583
        have hw : |(417119903/1000000000 : ℝ)|=(417119903/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(909931137/2000000000 : ℝ)|^2095 ≤ (3526600781487/10000000000000 : ℝ)^1583
        have hw : |(909931137/2000000000 : ℝ)|=(909931137/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1187_s3_4 (p : ℝ) (hpa : (8379/2048 : ℝ) ≤ p) (hpb : p ≤ (2095/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2142229629/10000000000 : ℝ)*x 0 + (2618423541/5000000000 : ℝ)*x 1 + (1084797499/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2142229629/10000000000 : ℝ)^2095 ≤ (13014984675089/100000000000000 : ℝ)^1583 := by
    have hnat : (2142229629 : ℕ)^2095*100000000000000^1583 ≤ 13014984675089^1583*10000000000^2095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2142229629 10000000000 13014984675089 100000000000000 2095 1583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2618423541/5000000000 : ℝ)^2095 ≤ (2124109212401/5000000000000 : ℝ)^1583 := by
    have hnat : (2618423541 : ℕ)^2095*5000000000000^1583 ≤ 2124109212401^1583*5000000000^2095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2618423541 5000000000 2124109212401 5000000000000 2095 1583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1084797499/2000000000 : ℝ)^2095 ≤ (44502831074583/100000000000000 : ℝ)^1583 := by
    have hnat : (1084797499 : ℕ)^2095*100000000000000^1583 ≤ 44502831074583^1583*2000000000^2095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1084797499 2000000000 44502831074583 100000000000000 2095 1583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2095/512 : ℝ)) 2095 1583 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2142229629/10000000000 : ℝ), (2618423541/5000000000 : ℝ), (1084797499/2000000000 : ℝ)] ![(13014984675089/100000000000000 : ℝ), (2124109212401/5000000000000 : ℝ), (44502831074583/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2142229629/10000000000 : ℝ)|^2095 ≤ (13014984675089/100000000000000 : ℝ)^1583
        have hw : |(-2142229629/10000000000 : ℝ)|=(2142229629/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2618423541/5000000000 : ℝ)|^2095 ≤ (2124109212401/5000000000000 : ℝ)^1583
        have hw : |(2618423541/5000000000 : ℝ)|=(2618423541/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1084797499/2000000000 : ℝ)|^2095 ≤ (44502831074583/100000000000000 : ℝ)^1583
        have hw : |(1084797499/2000000000 : ℝ)|=(1084797499/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1187_s3_5 (p : ℝ) (hpa : (8379/2048 : ℝ) ≤ p) (hpb : p ≤ (2095/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1326201553/2500000000 : ℝ)*x 0 + (-2050658867/10000000000 : ℝ)*x 1 + (1084797487/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1326201553/2500000000 : ℝ)^2095 ≤ (10803329019667/25000000000000 : ℝ)^1583 := by
    have hnat : (1326201553 : ℕ)^2095*25000000000000^1583 ≤ 10803329019667^1583*2500000000^2095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1326201553 2500000000 10803329019667 25000000000000 2095 1583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2050658867/10000000000 : ℝ)^2095 ≤ (12283853478427/100000000000000 : ℝ)^1583 := by
    have hnat : (2050658867 : ℕ)^2095*100000000000000^1583 ≤ 12283853478427^1583*10000000000^2095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2050658867 10000000000 12283853478427 100000000000000 2095 1583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1084797487/2000000000 : ℝ)^2095 ≤ (4450283042307/10000000000000 : ℝ)^1583 := by
    have hnat : (1084797487 : ℕ)^2095*10000000000000^1583 ≤ 4450283042307^1583*2000000000^2095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1084797487 2000000000 4450283042307 10000000000000 2095 1583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2095/512 : ℝ)) 2095 1583 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1326201553/2500000000 : ℝ), (-2050658867/10000000000 : ℝ), (1084797487/2000000000 : ℝ)] ![(10803329019667/25000000000000 : ℝ), (12283853478427/100000000000000 : ℝ), (4450283042307/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1326201553/2500000000 : ℝ)|^2095 ≤ (10803329019667/25000000000000 : ℝ)^1583
        have hw : |(1326201553/2500000000 : ℝ)|=(1326201553/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2050658867/10000000000 : ℝ)|^2095 ≤ (12283853478427/100000000000000 : ℝ)^1583
        have hw : |(-2050658867/10000000000 : ℝ)|=(2050658867/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1084797487/2000000000 : ℝ)|^2095 ≤ (4450283042307/10000000000000 : ℝ)^1583
        have hw : |(1084797487/2000000000 : ℝ)|=(1084797487/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1187_s3_6 (p : ℝ) (hpa : (8379/2048 : ℝ) ≤ p) (hpb : p ≤ (2095/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5304805861/10000000000 : ℝ)*x 0 + (5423987819/10000000000 : ℝ)*x 1 + (-2050658819/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5304805861/10000000000 : ℝ)^2095 ≤ (21606656147303/50000000000000 : ℝ)^1583 := by
    have hnat : (5304805861 : ℕ)^2095*50000000000000^1583 ≤ 21606656147303^1583*10000000000^2095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5304805861 10000000000 21606656147303 50000000000000 2095 1583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5423987819/10000000000 : ℝ)^2095 ≤ (11125708648189/25000000000000 : ℝ)^1583 := by
    have hnat : (5423987819 : ℕ)^2095*25000000000000^1583 ≤ 11125708648189^1583*10000000000^2095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5423987819 10000000000 11125708648189 25000000000000 2095 1583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2050658819/10000000000 : ℝ)^2095 ≤ (122838530979/1000000000000 : ℝ)^1583 := by
    have hnat : (2050658819 : ℕ)^2095*1000000000000^1583 ≤ 122838530979^1583*10000000000^2095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2050658819 10000000000 122838530979 1000000000000 2095 1583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2095/512 : ℝ)) 2095 1583 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5304805861/10000000000 : ℝ), (5423987819/10000000000 : ℝ), (-2050658819/10000000000 : ℝ)] ![(21606656147303/50000000000000 : ℝ), (11125708648189/25000000000000 : ℝ), (122838530979/1000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5304805861/10000000000 : ℝ)|^2095 ≤ (21606656147303/50000000000000 : ℝ)^1583
        have hw : |(5304805861/10000000000 : ℝ)|=(5304805861/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5423987819/10000000000 : ℝ)|^2095 ≤ (11125708648189/25000000000000 : ℝ)^1583
        have hw : |(5423987819/10000000000 : ℝ)|=(5423987819/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2050658819/10000000000 : ℝ)|^2095 ≤ (122838530979/1000000000000 : ℝ)^1583
        have hw : |(-2050658819/10000000000 : ℝ)|=(2050658819/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1187_s3_7 (p : ℝ) (hpa : (8379/2048 : ℝ) ≤ p) (hpb : p ≤ (2095/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4356418019/10000000000 : ℝ)*x 0 + (568528863/1250000000 : ℝ)*x 1 + (4172631307/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4356418019/10000000000 : ℝ)^2095 ≤ (33297441481033/100000000000000 : ℝ)^1583 := by
    have hnat : (4356418019 : ℕ)^2095*100000000000000^1583 ≤ 33297441481033^1583*10000000000^2095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4356418019 10000000000 33297441481033 100000000000000 2095 1583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (568528863/1250000000 : ℝ)^2095 ≤ (35251392539597/100000000000000 : ℝ)^1583 := by
    have hnat : (568528863 : ℕ)^2095*100000000000000^1583 ≤ 35251392539597^1583*1250000000^2095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      568528863 1250000000 35251392539597 100000000000000 2095 1583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4172631307/10000000000 : ℝ)^2095 ≤ (31451165955919/100000000000000 : ℝ)^1583 := by
    have hnat : (4172631307 : ℕ)^2095*100000000000000^1583 ≤ 31451165955919^1583*10000000000^2095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4172631307 10000000000 31451165955919 100000000000000 2095 1583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2095/512 : ℝ)) 2095 1583 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4356418019/10000000000 : ℝ), (568528863/1250000000 : ℝ), (4172631307/10000000000 : ℝ)] ![(33297441481033/100000000000000 : ℝ), (35251392539597/100000000000000 : ℝ), (31451165955919/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4356418019/10000000000 : ℝ)|^2095 ≤ (33297441481033/100000000000000 : ℝ)^1583
        have hw : |(4356418019/10000000000 : ℝ)|=(4356418019/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(568528863/1250000000 : ℝ)|^2095 ≤ (35251392539597/100000000000000 : ℝ)^1583
        have hw : |(568528863/1250000000 : ℝ)|=(568528863/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4172631307/10000000000 : ℝ)|^2095 ≤ (31451165955919/100000000000000 : ℝ)^1583
        have hw : |(4172631307/10000000000 : ℝ)|=(4172631307/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1187_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8379/2048 : ℝ) ≤ p) (hpb : p ≤ (2095/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150352467/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4093/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9269/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (2691/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (2951/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (4093/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (9269/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (4093/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (9269/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (4093/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (9269/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (4093/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (9269/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (4093/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (9269/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (4093/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (9269/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (9269/100000 : ℝ) ^ (8379/2048 : ℝ) ≤ (2970179922399663/50000000000000000000 : ℝ) := by
    have hpowers : (9269/100000 : ℝ)^8379 ≤ (2970179922399663/50000000000000000000 : ℝ)^2048 := by
      have hnat : (9269 : ℕ)^8379*50000000000000000000^2048 ≤ 2970179922399663^2048*100000^8379 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        9269 100000 2970179922399663 50000000000000000000 8379 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (9269/100000 : ℝ)) (X := (2970179922399663/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8379 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (4093/25000 : ℝ) ^ (8379/2048 : ℝ) ≤ (60904261091573111/100000000000000000000 : ℝ) := by
    have hpowers : (4093/25000 : ℝ)^8379 ≤ (60904261091573111/100000000000000000000 : ℝ)^2048 := by
      have hnat : (4093 : ℕ)^8379*100000000000000000000^2048 ≤ 60904261091573111^2048*25000^8379 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4093 25000 60904261091573111 100000000000000000000 8379 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4093/25000 : ℝ)) (X := (60904261091573111/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8379 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (25002970179922399663/25000000000000000000 : ℝ) ≤ (80002323009609/80000000000000 : ℝ) ^ (8379/2048 : ℝ) := by
    have hpowers : (25002970179922399663/25000000000000000000 : ℝ)^2048 ≤ (80002323009609/80000000000000 : ℝ)^8379 := by
      have hnat : (25002970179922399663 : ℕ)^2048*80000000000000^8379 ≤ 80002323009609^8379*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25002970179922399663 25000000000000000000 80002323009609 80000000000000 2048 8379 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (80002323009609/80000000000000 : ℝ)) (X := (25002970179922399663/25000000000000000000 : ℝ)) (by norm_num) 8379 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100066844620936372437/100000000000000000000 : ℝ) ≤ (10001633407639453/10000000000000000 : ℝ) ^ (8379/2048 : ℝ) := by
    have hpowers : (100066844620936372437/100000000000000000000 : ℝ)^2048 ≤ (10001633407639453/10000000000000000 : ℝ)^8379 := by
      have hnat : (100066844620936372437 : ℕ)^2048*10000000000000000^8379 ≤ 10001633407639453^8379*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100066844620936372437 100000000000000000000 10001633407639453 10000000000000000 2048 8379 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001633407639453/10000000000000000 : ℝ)) (X := (100066844620936372437/100000000000000000000 : ℝ)) (by norm_num) 8379 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50060904261091573111/50000000000000000000 : ℝ) ≤ (10002976439077781/10000000000000000 : ℝ) ^ (8379/2048 : ℝ) := by
    have hpowers : (50060904261091573111/50000000000000000000 : ℝ)^2048 ≤ (10002976439077781/10000000000000000 : ℝ)^8379 := by
      have hnat : (50060904261091573111 : ℕ)^2048*10000000000000000^8379 ≤ 10002976439077781^8379*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50060904261091573111 50000000000000000000 10002976439077781 10000000000000000 2048 8379 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10002976439077781/10000000000000000 : ℝ)) (X := (50060904261091573111/50000000000000000000 : ℝ)) (by norm_num) 8379 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2970179922399663/50000000000000000000 : ℝ) ≤ ((71007165425352866411/71030000000000000000 : ℝ)+2*(167878929791/88787500000000 : ℝ)*(9269/100000 : ℝ))^(8379/2048 : ℝ) := by
    rw [show (71007165425352866411/71030000000000000000 : ℝ)+2*(167878929791/88787500000000 : ℝ)*(9269/100000 : ℝ)=(80002323009609/80000000000000 : ℝ) by norm_num, show 1+2*(2970179922399663/50000000000000000000 : ℝ)=(25002970179922399663/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(60904261091573111/100000000000000000000 : ℝ)+(2970179922399663/50000000000000000000 : ℝ) ≤ ((71007165425352866411/71030000000000000000 : ℝ)+(167878929791/88787500000000 : ℝ)*((4093/25000 : ℝ)+(9269/100000 : ℝ)))^(8379/2048 : ℝ) := by
    rw [show (71007165425352866411/71030000000000000000 : ℝ)+(167878929791/88787500000000 : ℝ)*((4093/25000 : ℝ)+(9269/100000 : ℝ))=(10001633407639453/10000000000000000 : ℝ) by norm_num, show 1+(60904261091573111/100000000000000000000 : ℝ)+(2970179922399663/50000000000000000000 : ℝ)=(100066844620936372437/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(60904261091573111/100000000000000000000 : ℝ) ≤ ((71007165425352866411/71030000000000000000 : ℝ)+2*(167878929791/88787500000000 : ℝ)*(4093/25000 : ℝ))^(8379/2048 : ℝ) := by
    rw [show (71007165425352866411/71030000000000000000 : ℝ)+2*(167878929791/88787500000000 : ℝ)*(4093/25000 : ℝ)=(10002976439077781/10000000000000000 : ℝ) by norm_num, show 1+2*(60904261091573111/100000000000000000000 : ℝ)=(50060904261091573111/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (71007165425352866411/71030000000000000000 : ℝ)*(X 1 0+X 2 0)+(167878929791/88787500000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8379/2048 : ℝ)) (lo := (9269/100000 : ℝ)) (hi := (4093/25000 : ℝ)) (c := (71007165425352866411/71030000000000000000 : ℝ)) (alpha := (167878929791/88787500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (71007165425352866411/71030000000000000000 : ℝ)*(X 0 1+X 2 1)+(167878929791/88787500000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8379/2048 : ℝ)) (lo := (9269/100000 : ℝ)) (hi := (4093/25000 : ℝ)) (c := (71007165425352866411/71030000000000000000 : ℝ)) (alpha := (167878929791/88787500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (71007165425352866411/71030000000000000000 : ℝ)*(X 0 2+X 1 2)+(167878929791/88787500000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8379/2048 : ℝ)) (lo := (9269/100000 : ℝ)) (hi := (4093/25000 : ℝ)) (c := (71007165425352866411/71030000000000000000 : ℝ)) (alpha := (167878929791/88787500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-267776699/1250000000 : ℝ)*X 0 0+(5424701/10000000 : ℝ)*X 0 1+(2618068703/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1187_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5352732029/10000000000 : ℝ)*X 1 0+(-89540377/400000000 : ℝ)*X 1 1+(5236137167/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1187_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((669091517/1250000000 : ℝ)*X 2 0+(5236137099/10000000000 : ℝ)*X 2 1+(-1119254687/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1187_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((217819277/500000000 : ℝ)*X 0 0+(417119903/1000000000 : ℝ)*X 0 1+(909931137/2000000000 : ℝ)*X 0 2+(217819277/500000000 : ℝ)*X 1 0+(417119903/1000000000 : ℝ)*X 1 1+(909931137/2000000000 : ℝ)*X 1 2+(217819277/500000000 : ℝ)*X 2 0+(417119903/1000000000 : ℝ)*X 2 1+(909931137/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1187_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2142229629/10000000000 : ℝ)*X 0 0+(2618423541/5000000000 : ℝ)*X 0 1+(1084797499/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1187_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1326201553/2500000000 : ℝ)*X 1 0+(-2050658867/10000000000 : ℝ)*X 1 1+(1084797487/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1187_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5304805861/10000000000 : ℝ)*X 2 0+(5423987819/10000000000 : ℝ)*X 2 1+(-2050658819/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1187_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4356418019/10000000000 : ℝ)*X 0 0+(568528863/1250000000 : ℝ)*X 0 1+(4172631307/10000000000 : ℝ)*X 0 2+(4356418019/10000000000 : ℝ)*X 1 0+(568528863/1250000000 : ℝ)*X 1 1+(4172631307/10000000000 : ℝ)*X 1 2+(4356418019/10000000000 : ℝ)*X 2 0+(568528863/1250000000 : ℝ)*X 2 1+(4172631307/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1187_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3638999253917960448018396963/443937500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1943094403/100000000000000 : ℝ)*(base19) + (960973197/50000000000000 : ℝ)*(base23) + (17016347/25000000000000 : ℝ)*(lower2) + (201010089/100000000000000 : ℝ)*(upper3) + (90032913/50000000000000 : ℝ)*(upper5) + (496603506243689/12500000000000 : ℝ)*(major0) + (496603506243689/12500000000000 : ℝ)*(major1) + (496603506243689/12500000000000 : ℝ)*(major2) + (1060656177910713/20000000000000 : ℝ)*(sp0) + (165728461726793/3125000000000 : ℝ)*(sp1) + (1060662159281077/20000000000000 : ℝ)*(sp2) + (1321163088802121/50000000000000 : ℝ)*(sp3) + (15914399107/50000000000000 : ℝ)*(sp4) + (16930706387/100000000000000 : ℝ)*(sp7) + (660585777077657/25000000000000 : ℝ)*(f.failure) + (5303312718351779/100000000000000 : ℝ)*(f.sum) + (131000489071769/35515000000000000000000000000 : ℝ)*base66 + (810772536007030179/887875000000000000000000000000000 : ℝ)*base67 + (13834471872496594821/887875000000000000000000000000000 : ℝ)*base70 + (5068756199764155179/887875000000000000000000000000000 : ℝ)*base71 + (47955783935671/8878750000000000000000000000 : ℝ)*base74 + (14289958381698594821/887875000000000000000000000000000 : ℝ)*base76 + (4767538873893155179/887875000000000000000000000000000 : ℝ)*base77 + (11394152357206905179/887875000000000000000000000000000 : ℝ)*base79 + (355504464632399/35515000000000000000000000000 : ℝ)*base82 + (19470181/2500000000000000000000 : ℝ)*base90 + (19470181/2500000000000000000000 : ℝ)*base92 + (19470181/2500000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (10836012517904383739858195379/1775750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (113248949/6250000000000 : ℝ)*(base19) + (1721415239/100000000000000 : ℝ)*(base23) + (3695501/3125000000000 : ℝ)*(upper3) + (32726013/25000000000000 : ℝ)*(lower4) + (113655831/50000000000000 : ℝ)*(upper5) + (2001496595533679/50000000000000 : ℝ)*(major0) + (2001496595533679/50000000000000 : ℝ)*(major1) + (2001496595533679/50000000000000 : ℝ)*(major2) + (36137732261/100000000000000 : ℝ)*(sp1) + (18967053451/50000000000000 : ℝ)*(sp2) + (5343580119858223/100000000000000 : ℝ)*(sp4) + (5343542170142779/100000000000000 : ℝ)*(sp5) + (5343540464336083/100000000000000 : ℝ)*(sp6) + (665601514717307/25000000000000 : ℝ)*(sp7) + (665601514717307/25000000000000 : ℝ)*(f.failure) + (5343580119858223/100000000000000 : ℝ)*(f.sum) + (279086244638949/35515000000000000000000000000 : ℝ)*base65 + (73044134428812556069/3551500000000000000000000000000000 : ℝ)*base67 + (53851952791688056069/3551500000000000000000000000000000 : ℝ)*base69 + (46030812258786056069/3551500000000000000000000000000000 : ℝ)*base71 + (28330372924257/17757500000000000000000000000 : ℝ)*base73 + (33806913646237556069/3551500000000000000000000000000000 : ℝ)*base75 + (61943114743259056069/3551500000000000000000000000000000 : ℝ)*base77 + (38462912605379056069/3551500000000000000000000000000000 : ℝ)*base79 + (111852303241859/35515000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (34953631/2500000000000000000000 : ℝ)*base90 + (34953631/2500000000000000000000 : ℝ)*base92 + (34953631/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1187_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8379/2048 : ℝ) ≤ p) (hpb : p ≤ (2095/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150352467/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4093/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9269/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2691/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2951/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1187_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1187_s4_0 (p : ℝ) (hpa : (8379/2048 : ℝ) ≤ p) (hpb : p ≤ (2095/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1072436559/5000000000 : ℝ)*x 0 + (1349955321/2500000000 : ℝ)*x 1 + (5259275967/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1072436559/5000000000 : ℝ)^2095 ≤ (13036243776021/100000000000000 : ℝ)^1583 := by
    have hnat : (1072436559 : ℕ)^2095*100000000000000^1583 ≤ 13036243776021^1583*5000000000^2095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1072436559 5000000000 13036243776021 100000000000000 2095 1583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1349955321/2500000000 : ℝ)^2095 ≤ (22120305092101/50000000000000 : ℝ)^1583 := by
    have hnat : (1349955321 : ℕ)^2095*50000000000000^1583 ≤ 22120305092101^1583*2500000000^2095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1349955321 2500000000 22120305092101 50000000000000 2095 1583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5259275967/10000000000 : ℝ)^2095 ≤ (1708925840853/4000000000000 : ℝ)^1583 := by
    have hnat : (5259275967 : ℕ)^2095*4000000000000^1583 ≤ 1708925840853^1583*10000000000^2095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5259275967 10000000000 1708925840853 4000000000000 2095 1583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2095/512 : ℝ)) 2095 1583 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1072436559/5000000000 : ℝ), (1349955321/2500000000 : ℝ), (5259275967/10000000000 : ℝ)] ![(13036243776021/100000000000000 : ℝ), (22120305092101/50000000000000 : ℝ), (1708925840853/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1072436559/5000000000 : ℝ)|^2095 ≤ (13036243776021/100000000000000 : ℝ)^1583
        have hw : |(-1072436559/5000000000 : ℝ)|=(1072436559/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1349955321/2500000000 : ℝ)|^2095 ≤ (22120305092101/50000000000000 : ℝ)^1583
        have hw : |(1349955321/2500000000 : ℝ)|=(1349955321/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5259275967/10000000000 : ℝ)|^2095 ≤ (1708925840853/4000000000000 : ℝ)^1583
        have hw : |(5259275967/10000000000 : ℝ)|=(5259275967/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1187_s4_1 (p : ℝ) (hpa : (8379/2048 : ℝ) ≤ p) (hpb : p ≤ (2095/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1336622801/2500000000 : ℝ)*x 0 + (-554066297/2500000000 : ℝ)*x 1 + (1051855271/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1336622801/2500000000 : ℝ)^2095 ≤ (43663283916559/100000000000000 : ℝ)^1583 := by
    have hnat : (1336622801 : ℕ)^2095*100000000000000^1583 ≤ 43663283916559^1583*2500000000^2095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1336622801 2500000000 43663283916559 100000000000000 2095 1583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (554066297/2500000000 : ℝ)^2095 ≤ (13613565879549/100000000000000 : ℝ)^1583 := by
    have hnat : (554066297 : ℕ)^2095*100000000000000^1583 ≤ 13613565879549^1583*2500000000^2095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      554066297 2500000000 13613565879549 100000000000000 2095 1583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1051855271/2000000000 : ℝ)^2095 ≤ (5340393774079/12500000000000 : ℝ)^1583 := by
    have hnat : (1051855271 : ℕ)^2095*12500000000000^1583 ≤ 5340393774079^1583*2000000000^2095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1051855271 2000000000 5340393774079 12500000000000 2095 1583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2095/512 : ℝ)) 2095 1583 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1336622801/2500000000 : ℝ), (-554066297/2500000000 : ℝ), (1051855271/2000000000 : ℝ)] ![(43663283916559/100000000000000 : ℝ), (13613565879549/100000000000000 : ℝ), (5340393774079/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1336622801/2500000000 : ℝ)|^2095 ≤ (43663283916559/100000000000000 : ℝ)^1583
        have hw : |(1336622801/2500000000 : ℝ)|=(1336622801/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-554066297/2500000000 : ℝ)|^2095 ≤ (13613565879549/100000000000000 : ℝ)^1583
        have hw : |(-554066297/2500000000 : ℝ)|=(554066297/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1051855271/2000000000 : ℝ)|^2095 ≤ (5340393774079/12500000000000 : ℝ)^1583
        have hw : |(1051855271/2000000000 : ℝ)|=(1051855271/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1187_s4_2 (p : ℝ) (hpa : (8379/2048 : ℝ) ≤ p) (hpb : p ≤ (2095/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1336622897/2500000000 : ℝ)*x 0 + (5259275747/10000000000 : ℝ)*x 1 + (-55406637/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1336622897/2500000000 : ℝ)^2095 ≤ (21831644033441/50000000000000 : ℝ)^1583 := by
    have hnat : (1336622897 : ℕ)^2095*50000000000000^1583 ≤ 21831644033441^1583*2500000000^2095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1336622897 2500000000 21831644033441 50000000000000 2095 1583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5259275747/10000000000 : ℝ)^2095 ≤ (42723143656151/100000000000000 : ℝ)^1583 := by
    have hnat : (5259275747 : ℕ)^2095*100000000000000^1583 ≤ 42723143656151^1583*10000000000^2095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5259275747 10000000000 42723143656151 100000000000000 2095 1583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (55406637/250000000 : ℝ)^2095 ≤ (2722713650661/20000000000000 : ℝ)^1583 := by
    have hnat : (55406637 : ℕ)^2095*20000000000000^1583 ≤ 2722713650661^1583*250000000^2095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      55406637 250000000 2722713650661 20000000000000 2095 1583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2095/512 : ℝ)) 2095 1583 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1336622897/2500000000 : ℝ), (5259275747/10000000000 : ℝ), (-55406637/250000000 : ℝ)] ![(21831644033441/50000000000000 : ℝ), (42723143656151/100000000000000 : ℝ), (2722713650661/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1336622897/2500000000 : ℝ)|^2095 ≤ (21831644033441/50000000000000 : ℝ)^1583
        have hw : |(1336622897/2500000000 : ℝ)|=(1336622897/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5259275747/10000000000 : ℝ)|^2095 ≤ (42723143656151/100000000000000 : ℝ)^1583
        have hw : |(5259275747/10000000000 : ℝ)|=(5259275747/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-55406637/250000000 : ℝ)|^2095 ≤ (2722713650661/20000000000000 : ℝ)^1583
        have hw : |(-55406637/250000000 : ℝ)|=(55406637/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1187_s4_3 (p : ℝ) (hpa : (8379/2048 : ℝ) ≤ p) (hpb : p ≤ (2095/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4357975461/10000000000 : ℝ)*x 0 + (421918217/1000000000 : ℝ)*x 1 + (2250631887/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4357975461/10000000000 : ℝ)^2095 ≤ (4164149573787/12500000000000 : ℝ)^1583 := by
    have hnat : (4357975461 : ℕ)^2095*12500000000000^1583 ≤ 4164149573787^1583*10000000000^2095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4357975461 10000000000 4164149573787 12500000000000 2095 1583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (421918217/1000000000 : ℝ)^2095 ≤ (31916364623727/100000000000000 : ℝ)^1583 := by
    have hnat : (421918217 : ℕ)^2095*100000000000000^1583 ≤ 31916364623727^1583*1000000000^2095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      421918217 1000000000 31916364623727 100000000000000 2095 1583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2250631887/5000000000 : ℝ)^2095 ≤ (3477043876149/10000000000000 : ℝ)^1583 := by
    have hnat : (2250631887 : ℕ)^2095*10000000000000^1583 ≤ 3477043876149^1583*5000000000^2095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2250631887 5000000000 3477043876149 10000000000000 2095 1583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2095/512 : ℝ)) 2095 1583 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4357975461/10000000000 : ℝ), (421918217/1000000000 : ℝ), (2250631887/5000000000 : ℝ)] ![(4164149573787/12500000000000 : ℝ), (31916364623727/100000000000000 : ℝ), (3477043876149/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4357975461/10000000000 : ℝ)|^2095 ≤ (4164149573787/12500000000000 : ℝ)^1583
        have hw : |(4357975461/10000000000 : ℝ)|=(4357975461/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(421918217/1000000000 : ℝ)|^2095 ≤ (31916364623727/100000000000000 : ℝ)^1583
        have hw : |(421918217/1000000000 : ℝ)|=(421918217/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2250631887/5000000000 : ℝ)|^2095 ≤ (3477043876149/10000000000000 : ℝ)^1583
        have hw : |(2250631887/5000000000 : ℝ)|=(2250631887/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1187_s4_4 (p : ℝ) (hpa : (8379/2048 : ℝ) ≤ p) (hpb : p ≤ (2095/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-214487993/1000000000 : ℝ)*x 0 + (1051934143/2000000000 : ℝ)*x 1 + (5399424827/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (214487993/1000000000 : ℝ)^2095 ≤ (1629537321187/12500000000000 : ℝ)^1583 := by
    have hnat : (214487993 : ℕ)^2095*12500000000000^1583 ≤ 1629537321187^1583*1000000000^2095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      214487993 1000000000 1629537321187 12500000000000 2095 1583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1051934143/2000000000 : ℝ)^2095 ≤ (21363694962841/50000000000000 : ℝ)^1583 := by
    have hnat : (1051934143 : ℕ)^2095*50000000000000^1583 ≤ 21363694962841^1583*2000000000^2095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1051934143 2000000000 21363694962841 50000000000000 2095 1583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5399424827/10000000000 : ℝ)^2095 ≤ (11059077874439/25000000000000 : ℝ)^1583 := by
    have hnat : (5399424827 : ℕ)^2095*25000000000000^1583 ≤ 11059077874439^1583*10000000000^2095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5399424827 10000000000 11059077874439 25000000000000 2095 1583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2095/512 : ℝ)) 2095 1583 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-214487993/1000000000 : ℝ), (1051934143/2000000000 : ℝ), (5399424827/10000000000 : ℝ)] ![(1629537321187/12500000000000 : ℝ), (21363694962841/50000000000000 : ℝ), (11059077874439/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-214487993/1000000000 : ℝ)|^2095 ≤ (1629537321187/12500000000000 : ℝ)^1583
        have hw : |(-214487993/1000000000 : ℝ)|=(214487993/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1051934143/2000000000 : ℝ)|^2095 ≤ (21363694962841/50000000000000 : ℝ)^1583
        have hw : |(1051934143/2000000000 : ℝ)|=(1051934143/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5399424827/10000000000 : ℝ)|^2095 ≤ (11059077874439/25000000000000 : ℝ)^1583
        have hw : |(5399424827/10000000000 : ℝ)|=(5399424827/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1187_s4_5 (p : ℝ) (hpa : (8379/2048 : ℝ) ≤ p) (hpb : p ≤ (2095/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2655384541/5000000000 : ℝ)*x 0 + (-207611629/1000000000 : ℝ)*x 1 + (2699712469/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2655384541/5000000000 : ℝ)^2095 ≤ (8655522459783/20000000000000 : ℝ)^1583 := by
    have hnat : (2655384541 : ℕ)^2095*20000000000000^1583 ≤ 8655522459783^1583*5000000000^2095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2655384541 5000000000 8655522459783 20000000000000 2095 1583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (207611629/1000000000 : ℝ)^2095 ≤ (12486074991881/100000000000000 : ℝ)^1583 := by
    have hnat : (207611629 : ℕ)^2095*100000000000000^1583 ≤ 12486074991881^1583*1000000000^2095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      207611629 1000000000 12486074991881 100000000000000 2095 1583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2699712469/5000000000 : ℝ)^2095 ≤ (5529539087661/12500000000000 : ℝ)^1583 := by
    have hnat : (2699712469 : ℕ)^2095*12500000000000^1583 ≤ 5529539087661^1583*5000000000^2095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2699712469 5000000000 5529539087661 12500000000000 2095 1583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2095/512 : ℝ)) 2095 1583 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2655384541/5000000000 : ℝ), (-207611629/1000000000 : ℝ), (2699712469/5000000000 : ℝ)] ![(8655522459783/20000000000000 : ℝ), (12486074991881/100000000000000 : ℝ), (5529539087661/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2655384541/5000000000 : ℝ)|^2095 ≤ (8655522459783/20000000000000 : ℝ)^1583
        have hw : |(2655384541/5000000000 : ℝ)|=(2655384541/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-207611629/1000000000 : ℝ)|^2095 ≤ (12486074991881/100000000000000 : ℝ)^1583
        have hw : |(-207611629/1000000000 : ℝ)|=(207611629/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2699712469/5000000000 : ℝ)|^2095 ≤ (5529539087661/12500000000000 : ℝ)^1583
        have hw : |(2699712469/5000000000 : ℝ)|=(2699712469/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1187_s4_6 (p : ℝ) (hpa : (8379/2048 : ℝ) ≤ p) (hpb : p ≤ (2095/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5310769379/10000000000 : ℝ)*x 0 + (1349856151/2500000000 : ℝ)*x 1 + (-1038058171/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5310769379/10000000000 : ℝ)^2095 ≤ (21638807750989/50000000000000 : ℝ)^1583 := by
    have hnat : (5310769379 : ℕ)^2095*50000000000000^1583 ≤ 21638807750989^1583*10000000000^2095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5310769379 10000000000 21638807750989 50000000000000 2095 1583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1349856151/2500000000 : ℝ)^2095 ≤ (884726181597/2000000000000 : ℝ)^1583 := by
    have hnat : (1349856151 : ℕ)^2095*2000000000000^1583 ≤ 884726181597^1583*2500000000^2095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1349856151 2500000000 884726181597 2000000000000 2095 1583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1038058171/5000000000 : ℝ)^2095 ≤ (12486075405767/100000000000000 : ℝ)^1583 := by
    have hnat : (1038058171 : ℕ)^2095*100000000000000^1583 ≤ 12486075405767^1583*5000000000^2095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1038058171 5000000000 12486075405767 100000000000000 2095 1583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2095/512 : ℝ)) 2095 1583 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5310769379/10000000000 : ℝ), (1349856151/2500000000 : ℝ), (-1038058171/5000000000 : ℝ)] ![(21638807750989/50000000000000 : ℝ), (884726181597/2000000000000 : ℝ), (12486075405767/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5310769379/10000000000 : ℝ)|^2095 ≤ (21638807750989/50000000000000 : ℝ)^1583
        have hw : |(5310769379/10000000000 : ℝ)|=(5310769379/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1349856151/2500000000 : ℝ)|^2095 ≤ (884726181597/2000000000000 : ℝ)^1583
        have hw : |(1349856151/2500000000 : ℝ)|=(1349856151/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1038058171/5000000000 : ℝ)|^2095 ≤ (12486075405767/100000000000000 : ℝ)^1583
        have hw : |(-1038058171/5000000000 : ℝ)|=(1038058171/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1187_s4_7 (p : ℝ) (hpa : (8379/2048 : ℝ) ≤ p) (hpb : p ≤ (2095/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2178994673/5000000000 : ℝ)*x 0 + (900094137/2000000000 : ℝ)*x 1 + (4219977957/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2178994673/5000000000 : ℝ)^2095 ≤ (33313337059379/100000000000000 : ℝ)^1583 := by
    have hnat : (2178994673 : ℕ)^2095*100000000000000^1583 ≤ 33313337059379^1583*5000000000^2095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2178994673 5000000000 33313337059379 100000000000000 2095 1583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (900094137/2000000000 : ℝ)^2095 ≤ (34762331235097/100000000000000 : ℝ)^1583 := by
    have hnat : (900094137 : ℕ)^2095*100000000000000^1583 ≤ 34762331235097^1583*2000000000^2095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      900094137 2000000000 34762331235097 100000000000000 2095 1583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4219977957/10000000000 : ℝ)^2095 ≤ (3990541461043/12500000000000 : ℝ)^1583 := by
    have hnat : (4219977957 : ℕ)^2095*12500000000000^1583 ≤ 3990541461043^1583*10000000000^2095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4219977957 10000000000 3990541461043 12500000000000 2095 1583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2095/512 : ℝ)) 2095 1583 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2178994673/5000000000 : ℝ), (900094137/2000000000 : ℝ), (4219977957/10000000000 : ℝ)] ![(33313337059379/100000000000000 : ℝ), (34762331235097/100000000000000 : ℝ), (3990541461043/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2178994673/5000000000 : ℝ)|^2095 ≤ (33313337059379/100000000000000 : ℝ)^1583
        have hw : |(2178994673/5000000000 : ℝ)|=(2178994673/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(900094137/2000000000 : ℝ)|^2095 ≤ (34762331235097/100000000000000 : ℝ)^1583
        have hw : |(900094137/2000000000 : ℝ)|=(900094137/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4219977957/10000000000 : ℝ)|^2095 ≤ (3990541461043/12500000000000 : ℝ)^1583
        have hw : |(4219977957/10000000000 : ℝ)|=(4219977957/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1187_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8379/2048 : ℝ) ≤ p) (hpb : p ≤ (2095/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150352467/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2951/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2691/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (5629/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7117/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (2951/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2691/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (2951/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2691/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (2951/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2691/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (2951/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2691/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (2951/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2691/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (2951/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2691/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2691/25000 : ℝ) ^ (8379/2048 : ℝ) ≤ (10952307664836701/100000000000000000000 : ℝ) := by
    have hpowers : (2691/25000 : ℝ)^8379 ≤ (10952307664836701/100000000000000000000 : ℝ)^2048 := by
      have hnat : (2691 : ℕ)^8379*100000000000000000000^2048 ≤ 10952307664836701^2048*25000^8379 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2691 25000 10952307664836701 100000000000000000000 8379 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2691/25000 : ℝ)) (X := (10952307664836701/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8379 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (2951/20000 : ℝ) ^ (8379/2048 : ℝ) ≤ (9949789030341129/25000000000000000000 : ℝ) := by
    have hpowers : (2951/20000 : ℝ)^8379 ≤ (9949789030341129/25000000000000000000 : ℝ)^2048 := by
      have hnat : (2951 : ℕ)^8379*25000000000000000000^2048 ≤ 9949789030341129^2048*20000^8379 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2951 20000 9949789030341129 25000000000000000000 8379 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2951/20000 : ℝ)) (X := (9949789030341129/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8379 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50010952307664836701/50000000000000000000 : ℝ) ≤ (10000535349567971/10000000000000000 : ℝ) ^ (8379/2048 : ℝ) := by
    have hpowers : (50010952307664836701/50000000000000000000 : ℝ)^2048 ≤ (10000535349567971/10000000000000000 : ℝ)^8379 := by
      have hnat : (50010952307664836701 : ℕ)^2048*10000000000000000^8379 ≤ 10000535349567971^8379*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50010952307664836701 50000000000000000000 10000535349567971 10000000000000000 2048 8379 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000535349567971/10000000000000000 : ℝ)) (X := (50010952307664836701/50000000000000000000 : ℝ)) (by norm_num) 8379 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100050751463786201217/100000000000000000000 : ℝ) ≤ (2000248046485573/2000000000000000 : ℝ) ^ (8379/2048 : ℝ) := by
    have hpowers : (100050751463786201217/100000000000000000000 : ℝ)^2048 ≤ (2000248046485573/2000000000000000 : ℝ)^8379 := by
      have hnat : (100050751463786201217 : ℕ)^2048*2000000000000000^8379 ≤ 2000248046485573^8379*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100050751463786201217 100000000000000000000 2000248046485573 2000000000000000 2048 8379 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000248046485573/2000000000000000 : ℝ)) (X := (100050751463786201217/100000000000000000000 : ℝ)) (by norm_num) 8379 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (12509949789030341129/12500000000000000000 : ℝ) ≤ (10001945115287759/10000000000000000 : ℝ) ^ (8379/2048 : ℝ) := by
    have hpowers : (12509949789030341129/12500000000000000000 : ℝ)^2048 ≤ (10001945115287759/10000000000000000 : ℝ)^8379 := by
      have hnat : (12509949789030341129 : ℕ)^2048*10000000000000000^8379 ≤ 10001945115287759^8379*12500000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12509949789030341129 12500000000000000000 10001945115287759 10000000000000000 2048 8379 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001945115287759/10000000000000000 : ℝ)) (X := (12509949789030341129/12500000000000000000 : ℝ)) (by norm_num) 8379 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(10952307664836701/100000000000000000000 : ℝ) ≤ ((3068997066301382633/3070000000000000000 : ℝ)+2*(352441429947/199550000000000 : ℝ)*(2691/25000 : ℝ))^(8379/2048 : ℝ) := by
    rw [show (3068997066301382633/3070000000000000000 : ℝ)+2*(352441429947/199550000000000 : ℝ)*(2691/25000 : ℝ)=(10000535349567971/10000000000000000 : ℝ) by norm_num, show 1+2*(10952307664836701/100000000000000000000 : ℝ)=(50010952307664836701/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(9949789030341129/25000000000000000000 : ℝ)+(10952307664836701/100000000000000000000 : ℝ) ≤ ((3068997066301382633/3070000000000000000 : ℝ)+(352441429947/199550000000000 : ℝ)*((2951/20000 : ℝ)+(2691/25000 : ℝ)))^(8379/2048 : ℝ) := by
    rw [show (3068997066301382633/3070000000000000000 : ℝ)+(352441429947/199550000000000 : ℝ)*((2951/20000 : ℝ)+(2691/25000 : ℝ))=(2000248046485573/2000000000000000 : ℝ) by norm_num, show 1+(9949789030341129/25000000000000000000 : ℝ)+(10952307664836701/100000000000000000000 : ℝ)=(100050751463786201217/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(9949789030341129/25000000000000000000 : ℝ) ≤ ((3068997066301382633/3070000000000000000 : ℝ)+2*(352441429947/199550000000000 : ℝ)*(2951/20000 : ℝ))^(8379/2048 : ℝ) := by
    rw [show (3068997066301382633/3070000000000000000 : ℝ)+2*(352441429947/199550000000000 : ℝ)*(2951/20000 : ℝ)=(10001945115287759/10000000000000000 : ℝ) by norm_num, show 1+2*(9949789030341129/25000000000000000000 : ℝ)=(12509949789030341129/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (3068997066301382633/3070000000000000000 : ℝ)*(X 1 0+X 2 0)+(352441429947/199550000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8379/2048 : ℝ)) (lo := (2691/25000 : ℝ)) (hi := (2951/20000 : ℝ)) (c := (3068997066301382633/3070000000000000000 : ℝ)) (alpha := (352441429947/199550000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (3068997066301382633/3070000000000000000 : ℝ)*(X 0 1+X 2 1)+(352441429947/199550000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8379/2048 : ℝ)) (lo := (2691/25000 : ℝ)) (hi := (2951/20000 : ℝ)) (c := (3068997066301382633/3070000000000000000 : ℝ)) (alpha := (352441429947/199550000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (3068997066301382633/3070000000000000000 : ℝ)*(X 0 2+X 1 2)+(352441429947/199550000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8379/2048 : ℝ)) (lo := (2691/25000 : ℝ)) (hi := (2951/20000 : ℝ)) (c := (3068997066301382633/3070000000000000000 : ℝ)) (alpha := (352441429947/199550000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1072436559/5000000000 : ℝ)*X 0 0+(1349955321/2500000000 : ℝ)*X 0 1+(5259275967/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1187_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1336622801/2500000000 : ℝ)*X 1 0+(-554066297/2500000000 : ℝ)*X 1 1+(1051855271/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1187_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1336622897/2500000000 : ℝ)*X 2 0+(5259275747/10000000000 : ℝ)*X 2 1+(-55406637/250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1187_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4357975461/10000000000 : ℝ)*X 0 0+(421918217/1000000000 : ℝ)*X 0 1+(2250631887/5000000000 : ℝ)*X 0 2+(4357975461/10000000000 : ℝ)*X 1 0+(421918217/1000000000 : ℝ)*X 1 1+(2250631887/5000000000 : ℝ)*X 1 2+(4357975461/10000000000 : ℝ)*X 2 0+(421918217/1000000000 : ℝ)*X 2 1+(2250631887/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1187_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-214487993/1000000000 : ℝ)*X 0 0+(1051934143/2000000000 : ℝ)*X 0 1+(5399424827/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1187_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2655384541/5000000000 : ℝ)*X 1 0+(-207611629/1000000000 : ℝ)*X 1 1+(2699712469/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1187_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5310769379/10000000000 : ℝ)*X 2 0+(1349856151/2500000000 : ℝ)*X 2 1+(-1038058171/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1187_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2178994673/5000000000 : ℝ)*X 0 0+(900094137/2000000000 : ℝ)*X 0 1+(4219977957/10000000000 : ℝ)*X 0 2+(2178994673/5000000000 : ℝ)*X 1 0+(900094137/2000000000 : ℝ)*X 1 1+(4219977957/10000000000 : ℝ)*X 1 2+(2178994673/5000000000 : ℝ)*X 2 0+(900094137/2000000000 : ℝ)*X 2 1+(4219977957/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1187_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2051943668602759755682311363/249437500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (272624497/100000000000000 : ℝ)*(base19) + (957631879/100000000000000 : ℝ)*(base23) + (827711/625000000000 : ℝ)*(upper2) + (5206509/2500000000000 : ℝ)*(upper3) + (7883593/20000000000000 : ℝ)*(upper4) + (1332534012413149/25000000000000 : ℝ)*(major0) + (1332534012413149/25000000000000 : ℝ)*(major1) + (5330136049652597/100000000000000 : ℝ)*(major2) + (3557581961194959/50000000000000 : ℝ)*(sp0) + (444698606873669/6250000000000 : ℝ)*(sp1) + (3557588512485661/50000000000000 : ℝ)*(sp2) + (886270225250343/25000000000000 : ℝ)*(sp3) + (14060213283/100000000000000 : ℝ)*(sp4) + (12941491147/100000000000000 : ℝ)*(sp7) + (1772546921246259/50000000000000 : ℝ)*(f.failure) + (7115177982603201/100000000000000 : ℝ)*(f.sum) + (14095811317571/19955000000000000000000000000 : ℝ)*base65 + (3490123143767312879/997750000000000000000000000000000 : ℝ)*base68 + (1137391923914052099/307000000000000000000000000000000 : ℝ)*base70 + (15208683901066812879/997750000000000000000000000000000 : ℝ)*base72 + (47107856524497/9977500000000000000000000000 : ℝ)*base74 + (884244160974947901/307000000000000000000000000000000 : ℝ)*base75 + (23912394091858683/76750000000000000000000000000000 : ℝ)*base78 + (2000739025380108683/76750000000000000000000000000000 : ℝ)*base80 + (5690466188697/1535000000000000000000000000 : ℝ)*base82 + (44829047/5000000000000000000000 : ℝ)*base90 + (44829047/5000000000000000000000 : ℝ)*base92 + (94829047/5000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (33870532484632492895726613/31179687500000000000000000000000 : ℝ) := by norm_num
    linear_combination (208012119/50000000000000 : ℝ)*(base19) + (1088238807/100000000000000 : ℝ)*(base23) + (37070523/25000000000000 : ℝ)*(upper2) + (211815557/100000000000000 : ℝ)*(upper5) + (335018321844077/6250000000000 : ℝ)*(major0) + (335018321844077/6250000000000 : ℝ)*(major1) + (335018321844077/6250000000000 : ℝ)*(major2) + (615733613/100000000000000 : ℝ)*(sp0) + (4984885143/25000000000000 : ℝ)*(sp1) + (755019719/4000000000000 : ℝ)*(sp2) + (3577717101145943/50000000000000 : ℝ)*(sp4) + (7155414462460689/100000000000000 : ℝ)*(sp5) + (7155414854293717/100000000000000 : ℝ)*(sp6) + (1782575722387459/50000000000000 : ℝ)*(sp7) + (1782575722387459/50000000000000 : ℝ)*(f.failure) + (7155434818025499/100000000000000 : ℝ)*(f.sum) + (92596546199769/9977500000000000000000000000 : ℝ)*base65 + (1812039230957841633/249437500000000000000000000000000 : ℝ)*base67 + (1970981153424279133/249437500000000000000000000000000 : ℝ)*base69 + (988783058253533367/249437500000000000000000000000000 : ℝ)*base72 + (40454016480547/4988750000000000000000000000 : ℝ)*base73 + (369591193901841633/249437500000000000000000000000000 : ℝ)*base75 + (925515093666029133/249437500000000000000000000000000 : ℝ)*base77 + (1993915882914029133/249437500000000000000000000000000 : ℝ)*base79 + (12613405407431/2494375000000000000000000000 : ℝ)*base81 + (9488647/5000000000000000000000 : ℝ)*base90 + (9488647/5000000000000000000000 : ℝ)*base92 + (9488647/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1187_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8379/2048 : ℝ) ≤ p) (hpb : p ≤ (2095/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150352467/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2951/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2691/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5629/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7117/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1187_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1187_s5_0 (p : ℝ) (hpa : (8379/2048 : ℝ) ≤ p) (hpb : p ≤ (2095/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1072709279/5000000000 : ℝ)*x 0 + (5393757293/10000000000 : ℝ)*x 1 + (5264981681/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1072709279/5000000000 : ℝ)^2095 ≤ (6520315646561/50000000000000 : ℝ)^1583 := by
    have hnat : (1072709279 : ℕ)^2095*50000000000000^1583 ≤ 6520315646561^1583*5000000000^2095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1072709279 5000000000 6520315646561 50000000000000 2095 1583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5393757293/10000000000 : ℝ)^2095 ≤ (8834974194763/20000000000000 : ℝ)^1583 := by
    have hnat : (5393757293 : ℕ)^2095*20000000000000^1583 ≤ 8834974194763^1583*10000000000^2095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5393757293 10000000000 8834974194763 20000000000000 2095 1583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5264981681/10000000000 : ℝ)^2095 ≤ (1337015553551/3125000000000 : ℝ)^1583 := by
    have hnat : (5264981681 : ℕ)^2095*3125000000000^1583 ≤ 1337015553551^1583*10000000000^2095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264981681 10000000000 1337015553551 3125000000000 2095 1583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2095/512 : ℝ)) 2095 1583 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1072709279/5000000000 : ℝ), (5393757293/10000000000 : ℝ), (5264981681/10000000000 : ℝ)] ![(6520315646561/50000000000000 : ℝ), (8834974194763/20000000000000 : ℝ), (1337015553551/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1072709279/5000000000 : ℝ)|^2095 ≤ (6520315646561/50000000000000 : ℝ)^1583
        have hw : |(-1072709279/5000000000 : ℝ)|=(1072709279/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5393757293/10000000000 : ℝ)|^2095 ≤ (8834974194763/20000000000000 : ℝ)^1583
        have hw : |(5393757293/10000000000 : ℝ)|=(5393757293/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5264981681/10000000000 : ℝ)|^2095 ≤ (1337015553551/3125000000000 : ℝ)^1583
        have hw : |(5264981681/10000000000 : ℝ)|=(5264981681/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1187_s5_1 (p : ℝ) (hpa : (8379/2048 : ℝ) ≤ p) (hpb : p ≤ (2095/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2672482203/5000000000 : ℝ)*x 0 + (-442149267/2000000000 : ℝ)*x 1 + (5264981671/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672482203/5000000000 : ℝ)^2095 ≤ (43646782843933/100000000000000 : ℝ)^1583 := by
    have hnat : (2672482203 : ℕ)^2095*100000000000000^1583 ≤ 43646782843933^1583*5000000000^2095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672482203 5000000000 43646782843933 100000000000000 2095 1583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (442149267/2000000000 : ℝ)^2095 ≤ (13568719531251/100000000000000 : ℝ)^1583 := by
    have hnat : (442149267 : ℕ)^2095*100000000000000^1583 ≤ 13568719531251^1583*2000000000^2095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      442149267 2000000000 13568719531251 100000000000000 2095 1583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5264981671/10000000000 : ℝ)^2095 ≤ (21392248803043/50000000000000 : ℝ)^1583 := by
    have hnat : (5264981671 : ℕ)^2095*50000000000000^1583 ≤ 21392248803043^1583*10000000000^2095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264981671 10000000000 21392248803043 50000000000000 2095 1583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2095/512 : ℝ)) 2095 1583 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672482203/5000000000 : ℝ), (-442149267/2000000000 : ℝ), (5264981671/10000000000 : ℝ)] ![(43646782843933/100000000000000 : ℝ), (13568719531251/100000000000000 : ℝ), (21392248803043/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672482203/5000000000 : ℝ)|^2095 ≤ (43646782843933/100000000000000 : ℝ)^1583
        have hw : |(2672482203/5000000000 : ℝ)|=(2672482203/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-442149267/2000000000 : ℝ)|^2095 ≤ (13568719531251/100000000000000 : ℝ)^1583
        have hw : |(-442149267/2000000000 : ℝ)|=(442149267/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5264981671/10000000000 : ℝ)|^2095 ≤ (21392248803043/50000000000000 : ℝ)^1583
        have hw : |(5264981671/10000000000 : ℝ)|=(5264981671/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1187_s5_2 (p : ℝ) (hpa : (8379/2048 : ℝ) ≤ p) (hpb : p ≤ (2095/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5344964431/10000000000 : ℝ)*x 0 + (5264981651/10000000000 : ℝ)*x 1 + (-2210746329/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344964431/10000000000 : ℝ)^2095 ≤ (43646783114111/100000000000000 : ℝ)^1583 := by
    have hnat : (5344964431 : ℕ)^2095*100000000000000^1583 ≤ 43646783114111^1583*10000000000^2095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344964431 10000000000 43646783114111 100000000000000 2095 1583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5264981651/10000000000 : ℝ)^2095 ≤ (8556899478199/20000000000000 : ℝ)^1583 := by
    have hnat : (5264981651 : ℕ)^2095*20000000000000^1583 ≤ 8556899478199^1583*10000000000^2095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264981651 10000000000 8556899478199 20000000000000 2095 1583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2210746329/10000000000 : ℝ)^2095 ≤ (6784359741257/50000000000000 : ℝ)^1583 := by
    have hnat : (2210746329 : ℕ)^2095*50000000000000^1583 ≤ 6784359741257^1583*10000000000^2095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2210746329 10000000000 6784359741257 50000000000000 2095 1583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2095/512 : ℝ)) 2095 1583 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344964431/10000000000 : ℝ), (5264981651/10000000000 : ℝ), (-2210746329/10000000000 : ℝ)] ![(43646783114111/100000000000000 : ℝ), (8556899478199/20000000000000 : ℝ), (6784359741257/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344964431/10000000000 : ℝ)|^2095 ≤ (43646783114111/100000000000000 : ℝ)^1583
        have hw : |(5344964431/10000000000 : ℝ)|=(5344964431/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5264981651/10000000000 : ℝ)|^2095 ≤ (8556899478199/20000000000000 : ℝ)^1583
        have hw : |(5264981651/10000000000 : ℝ)|=(5264981651/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2210746329/10000000000 : ℝ)|^2095 ≤ (6784359741257/50000000000000 : ℝ)^1583
        have hw : |(-2210746329/10000000000 : ℝ)|=(2210746329/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1187_s5_3 (p : ℝ) (hpa : (8379/2048 : ℝ) ≤ p) (hpb : p ≤ (2095/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4358295063/10000000000 : ℝ)*x 0 + (4230952079/10000000000 : ℝ)*x 1 + (897882229/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4358295063/10000000000 : ℝ)^2095 ≤ (520569217417/1562500000000 : ℝ)^1583 := by
    have hnat : (4358295063 : ℕ)^2095*1562500000000^1583 ≤ 520569217417^1583*10000000000^2095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4358295063 10000000000 520569217417 1562500000000 2095 1583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4230952079/10000000000 : ℝ)^2095 ≤ (3203424923489/10000000000000 : ℝ)^1583 := by
    have hnat : (4230952079 : ℕ)^2095*10000000000000^1583 ≤ 3203424923489^1583*10000000000^2095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4230952079 10000000000 3203424923489 10000000000000 2095 1583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (897882229/2000000000 : ℝ)^2095 ≤ (34649320835741/100000000000000 : ℝ)^1583 := by
    have hnat : (897882229 : ℕ)^2095*100000000000000^1583 ≤ 34649320835741^1583*2000000000^2095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      897882229 2000000000 34649320835741 100000000000000 2095 1583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2095/512 : ℝ)) 2095 1583 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4358295063/10000000000 : ℝ), (4230952079/10000000000 : ℝ), (897882229/2000000000 : ℝ)] ![(520569217417/1562500000000 : ℝ), (3203424923489/10000000000000 : ℝ), (34649320835741/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4358295063/10000000000 : ℝ)|^2095 ≤ (520569217417/1562500000000 : ℝ)^1583
        have hw : |(4358295063/10000000000 : ℝ)|=(4358295063/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4230952079/10000000000 : ℝ)|^2095 ≤ (3203424923489/10000000000000 : ℝ)^1583
        have hw : |(4230952079/10000000000 : ℝ)|=(4230952079/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(897882229/2000000000 : ℝ)|^2095 ≤ (34649320835741/100000000000000 : ℝ)^1583
        have hw : |(897882229/2000000000 : ℝ)|=(897882229/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1187_s5_4 (p : ℝ) (hpa : (8379/2048 : ℝ) ≤ p) (hpb : p ≤ (2095/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1072711839/5000000000 : ℝ)*x 0 + (5265313417/10000000000 : ℝ)*x 1 + (5393424333/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1072711839/5000000000 : ℝ)^2095 ≤ (1304067248009/10000000000000 : ℝ)^1583 := by
    have hnat : (1072711839 : ℕ)^2095*10000000000000^1583 ≤ 1304067248009^1583*5000000000^2095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1072711839 5000000000 1304067248009 10000000000000 2095 1583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5265313417/10000000000 : ℝ)^2095 ≤ (2139403271251/5000000000000 : ℝ)^1583 := by
    have hnat : (5265313417 : ℕ)^2095*5000000000000^1583 ≤ 2139403271251^1583*10000000000^2095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265313417 10000000000 2139403271251 5000000000000 2095 1583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5393424333/10000000000 : ℝ)^2095 ≤ (8834252414961/20000000000000 : ℝ)^1583 := by
    have hnat : (5393424333 : ℕ)^2095*20000000000000^1583 ≤ 8834252414961^1583*10000000000^2095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5393424333 10000000000 8834252414961 20000000000000 2095 1583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2095/512 : ℝ)) 2095 1583 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1072711839/5000000000 : ℝ), (5265313417/10000000000 : ℝ), (5393424333/10000000000 : ℝ)] ![(1304067248009/10000000000000 : ℝ), (2139403271251/5000000000000 : ℝ), (8834252414961/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1072711839/5000000000 : ℝ)|^2095 ≤ (1304067248009/10000000000000 : ℝ)^1583
        have hw : |(-1072711839/5000000000 : ℝ)|=(1072711839/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5265313417/10000000000 : ℝ)|^2095 ≤ (2139403271251/5000000000000 : ℝ)^1583
        have hw : |(5265313417/10000000000 : ℝ)|=(5265313417/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5393424333/10000000000 : ℝ)|^2095 ≤ (8834252414961/20000000000000 : ℝ)^1583
        have hw : |(5393424333/10000000000 : ℝ)|=(5393424333/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1187_s5_5 (p : ℝ) (hpa : (8379/2048 : ℝ) ≤ p) (hpb : p ≤ (2095/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5312232177/10000000000 : ℝ)*x 0 + (-1041151821/5000000000 : ℝ)*x 1 + (5393424319/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312232177/10000000000 : ℝ)^2095 ≤ (43293392075851/100000000000000 : ℝ)^1583 := by
    have hnat : (5312232177 : ℕ)^2095*100000000000000^1583 ≤ 43293392075851^1583*10000000000^2095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312232177 10000000000 43293392075851 100000000000000 2095 1583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1041151821/5000000000 : ℝ)^2095 ≤ (12535345985607/100000000000000 : ℝ)^1583 := by
    have hnat : (1041151821 : ℕ)^2095*100000000000000^1583 ≤ 12535345985607^1583*5000000000^2095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1041151821 5000000000 12535345985607 100000000000000 2095 1583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5393424319/10000000000 : ℝ)^2095 ≤ (44171261923063/100000000000000 : ℝ)^1583 := by
    have hnat : (5393424319 : ℕ)^2095*100000000000000^1583 ≤ 44171261923063^1583*10000000000^2095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5393424319 10000000000 44171261923063 100000000000000 2095 1583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2095/512 : ℝ)) 2095 1583 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312232177/10000000000 : ℝ), (-1041151821/5000000000 : ℝ), (5393424319/10000000000 : ℝ)] ![(43293392075851/100000000000000 : ℝ), (12535345985607/100000000000000 : ℝ), (44171261923063/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312232177/10000000000 : ℝ)|^2095 ≤ (43293392075851/100000000000000 : ℝ)^1583
        have hw : |(5312232177/10000000000 : ℝ)|=(5312232177/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1041151821/5000000000 : ℝ)|^2095 ≤ (12535345985607/100000000000000 : ℝ)^1583
        have hw : |(-1041151821/5000000000 : ℝ)|=(1041151821/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5393424319/10000000000 : ℝ)|^2095 ≤ (44171261923063/100000000000000 : ℝ)^1583
        have hw : |(5393424319/10000000000 : ℝ)|=(5393424319/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1187_s5_6 (p : ℝ) (hpa : (8379/2048 : ℝ) ≤ p) (hpb : p ≤ (2095/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5312232177/10000000000 : ℝ)*x 0 + (5393424317/10000000000 : ℝ)*x 1 + (-520575911/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312232177/10000000000 : ℝ)^2095 ≤ (43293392075851/100000000000000 : ℝ)^1583 := by
    have hnat : (5312232177 : ℕ)^2095*100000000000000^1583 ≤ 43293392075851^1583*10000000000^2095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312232177 10000000000 43293392075851 100000000000000 2095 1583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5393424317/10000000000 : ℝ)^2095 ≤ (8834252380277/20000000000000 : ℝ)^1583 := by
    have hnat : (5393424317 : ℕ)^2095*20000000000000^1583 ≤ 8834252380277^1583*10000000000^2095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5393424317 10000000000 8834252380277 20000000000000 2095 1583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (520575911/2500000000 : ℝ)^2095 ≤ (12535346001541/100000000000000 : ℝ)^1583 := by
    have hnat : (520575911 : ℕ)^2095*100000000000000^1583 ≤ 12535346001541^1583*2500000000^2095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      520575911 2500000000 12535346001541 100000000000000 2095 1583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2095/512 : ℝ)) 2095 1583 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312232177/10000000000 : ℝ), (5393424317/10000000000 : ℝ), (-520575911/2500000000 : ℝ)] ![(43293392075851/100000000000000 : ℝ), (8834252380277/20000000000000 : ℝ), (12535346001541/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312232177/10000000000 : ℝ)|^2095 ≤ (43293392075851/100000000000000 : ℝ)^1583
        have hw : |(5312232177/10000000000 : ℝ)|=(5312232177/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5393424317/10000000000 : ℝ)|^2095 ≤ (8834252380277/20000000000000 : ℝ)^1583
        have hw : |(5393424317/10000000000 : ℝ)|=(5393424317/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-520575911/2500000000 : ℝ)|^2095 ≤ (12535346001541/100000000000000 : ℝ)^1583
        have hw : |(-520575911/2500000000 : ℝ)|=(520575911/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1187_s5_7 (p : ℝ) (hpa : (8379/2048 : ℝ) ≤ p) (hpb : p ≤ (2095/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2179152691/5000000000 : ℝ)*x 0 + (4488745299/10000000000 : ℝ)*x 1 + (2115810183/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2179152691/5000000000 : ℝ)^2095 ≤ (16658267155207/50000000000000 : ℝ)^1583 := by
    have hnat : (2179152691 : ℕ)^2095*50000000000000^1583 ≤ 16658267155207^1583*5000000000^2095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2179152691 5000000000 16658267155207 50000000000000 2095 1583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4488745299/10000000000 : ℝ)^2095 ≤ (8660629962609/25000000000000 : ℝ)^1583 := by
    have hnat : (4488745299 : ℕ)^2095*25000000000000^1583 ≤ 8660629962609^1583*10000000000^2095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4488745299 10000000000 8660629962609 25000000000000 2095 1583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2115810183/5000000000 : ℝ)^2095 ≤ (4005118228019/12500000000000 : ℝ)^1583 := by
    have hnat : (2115810183 : ℕ)^2095*12500000000000^1583 ≤ 4005118228019^1583*5000000000^2095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2115810183 5000000000 4005118228019 12500000000000 2095 1583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2095/512 : ℝ)) 2095 1583 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2179152691/5000000000 : ℝ), (4488745299/10000000000 : ℝ), (2115810183/5000000000 : ℝ)] ![(16658267155207/50000000000000 : ℝ), (8660629962609/25000000000000 : ℝ), (4005118228019/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2179152691/5000000000 : ℝ)|^2095 ≤ (16658267155207/50000000000000 : ℝ)^1583
        have hw : |(2179152691/5000000000 : ℝ)|=(2179152691/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4488745299/10000000000 : ℝ)|^2095 ≤ (8660629962609/25000000000000 : ℝ)^1583
        have hw : |(4488745299/10000000000 : ℝ)|=(4488745299/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2115810183/5000000000 : ℝ)|^2095 ≤ (4005118228019/12500000000000 : ℝ)^1583
        have hw : |(2115810183/5000000000 : ℝ)|=(2115810183/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1187_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8379/2048 : ℝ) ≤ p) (hpb : p ≤ (2095/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150352467/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7117/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5629/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (569/5000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14107/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7117/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5629/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7117/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5629/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7117/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5629/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7117/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5629/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7117/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5629/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7117/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5629/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5629/50000 : ℝ) ^ (8379/2048 : ℝ) ≤ (13159374221221797/100000000000000000000 : ℝ) := by
    have hpowers : (5629/50000 : ℝ)^8379 ≤ (13159374221221797/100000000000000000000 : ℝ)^2048 := by
      have hnat : (5629 : ℕ)^8379*100000000000000000000^2048 ≤ 13159374221221797^2048*50000^8379 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5629 50000 13159374221221797 100000000000000000000 8379 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5629/50000 : ℝ)) (X := (13159374221221797/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8379 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (7117/50000 : ℝ) ^ (8379/2048 : ℝ) ≤ (1073616909749483/3125000000000000000 : ℝ) := by
    have hpowers : (7117/50000 : ℝ)^8379 ≤ (1073616909749483/3125000000000000000 : ℝ)^2048 := by
      have hnat : (7117 : ℕ)^8379*3125000000000000000^2048 ≤ 1073616909749483^2048*50000^8379 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7117 50000 1073616909749483 3125000000000000000 8379 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7117/50000 : ℝ)) (X := (1073616909749483/3125000000000000000 : ℝ)) (by norm_num) (by norm_num) 8379 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50013159374221221797/50000000000000000000 : ℝ) ≤ (5000321610205901/5000000000000000 : ℝ) ^ (8379/2048 : ℝ) := by
    have hpowers : (50013159374221221797/50000000000000000000 : ℝ)^2048 ≤ (5000321610205901/5000000000000000 : ℝ)^8379 := by
      have hnat : (50013159374221221797 : ℕ)^2048*5000000000000000^8379 ≤ 5000321610205901^8379*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50013159374221221797 50000000000000000000 5000321610205901 5000000000000000 2048 8379 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000321610205901/5000000000000000 : ℝ)) (X := (50013159374221221797/50000000000000000000 : ℝ)) (by norm_num) 8379 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100047515115333205253/100000000000000000000 : ℝ) ≤ (10001161158766427/10000000000000000 : ℝ) ^ (8379/2048 : ℝ) := by
    have hpowers : (100047515115333205253/100000000000000000000 : ℝ)^2048 ≤ (10001161158766427/10000000000000000 : ℝ)^8379 := by
      have hnat : (100047515115333205253 : ℕ)^2048*10000000000000000^8379 ≤ 10001161158766427^8379*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100047515115333205253 100000000000000000000 10001161158766427 10000000000000000 2048 8379 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001161158766427/10000000000000000 : ℝ)) (X := (100047515115333205253/100000000000000000000 : ℝ)) (by norm_num) 8379 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (1563573616909749483/1562500000000000000 : ℝ) ≤ (2500419774280263/2500000000000000 : ℝ) ^ (8379/2048 : ℝ) := by
    have hpowers : (1563573616909749483/1562500000000000000 : ℝ)^2048 ≤ (2500419774280263/2500000000000000 : ℝ)^8379 := by
      have hnat : (1563573616909749483 : ℕ)^2048*2500000000000000^8379 ≤ 2500419774280263^8379*1562500000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1563573616909749483 1562500000000000000 2500419774280263 2500000000000000 2048 8379 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500419774280263/2500000000000000 : ℝ)) (X := (1563573616909749483/1562500000000000000 : ℝ)) (by norm_num) 8379 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(13159374221221797/100000000000000000000 : ℝ) ≤ ((7437563080988196563/7440000000000000000 : ℝ)+2*(4143506837/2380800000000 : ℝ)*(5629/50000 : ℝ))^(8379/2048 : ℝ) := by
    rw [show (7437563080988196563/7440000000000000000 : ℝ)+2*(4143506837/2380800000000 : ℝ)*(5629/50000 : ℝ)=(5000321610205901/5000000000000000 : ℝ) by norm_num, show 1+2*(13159374221221797/100000000000000000000 : ℝ)=(50013159374221221797/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1073616909749483/3125000000000000000 : ℝ)+(13159374221221797/100000000000000000000 : ℝ) ≤ ((7437563080988196563/7440000000000000000 : ℝ)+(4143506837/2380800000000 : ℝ)*((7117/50000 : ℝ)+(5629/50000 : ℝ)))^(8379/2048 : ℝ) := by
    rw [show (7437563080988196563/7440000000000000000 : ℝ)+(4143506837/2380800000000 : ℝ)*((7117/50000 : ℝ)+(5629/50000 : ℝ))=(10001161158766427/10000000000000000 : ℝ) by norm_num, show 1+(1073616909749483/3125000000000000000 : ℝ)+(13159374221221797/100000000000000000000 : ℝ)=(100047515115333205253/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1073616909749483/3125000000000000000 : ℝ) ≤ ((7437563080988196563/7440000000000000000 : ℝ)+2*(4143506837/2380800000000 : ℝ)*(7117/50000 : ℝ))^(8379/2048 : ℝ) := by
    rw [show (7437563080988196563/7440000000000000000 : ℝ)+2*(4143506837/2380800000000 : ℝ)*(7117/50000 : ℝ)=(2500419774280263/2500000000000000 : ℝ) by norm_num, show 1+2*(1073616909749483/3125000000000000000 : ℝ)=(1563573616909749483/1562500000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (7437563080988196563/7440000000000000000 : ℝ)*(X 1 0+X 2 0)+(4143506837/2380800000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8379/2048 : ℝ)) (lo := (5629/50000 : ℝ)) (hi := (7117/50000 : ℝ)) (c := (7437563080988196563/7440000000000000000 : ℝ)) (alpha := (4143506837/2380800000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (7437563080988196563/7440000000000000000 : ℝ)*(X 0 1+X 2 1)+(4143506837/2380800000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8379/2048 : ℝ)) (lo := (5629/50000 : ℝ)) (hi := (7117/50000 : ℝ)) (c := (7437563080988196563/7440000000000000000 : ℝ)) (alpha := (4143506837/2380800000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (7437563080988196563/7440000000000000000 : ℝ)*(X 0 2+X 1 2)+(4143506837/2380800000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8379/2048 : ℝ)) (lo := (5629/50000 : ℝ)) (hi := (7117/50000 : ℝ)) (c := (7437563080988196563/7440000000000000000 : ℝ)) (alpha := (4143506837/2380800000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1072709279/5000000000 : ℝ)*X 0 0+(5393757293/10000000000 : ℝ)*X 0 1+(5264981681/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1187_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2672482203/5000000000 : ℝ)*X 1 0+(-442149267/2000000000 : ℝ)*X 1 1+(5264981671/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1187_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5344964431/10000000000 : ℝ)*X 2 0+(5264981651/10000000000 : ℝ)*X 2 1+(-2210746329/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1187_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4358295063/10000000000 : ℝ)*X 0 0+(4230952079/10000000000 : ℝ)*X 0 1+(897882229/2000000000 : ℝ)*X 0 2+(4358295063/10000000000 : ℝ)*X 1 0+(4230952079/10000000000 : ℝ)*X 1 1+(897882229/2000000000 : ℝ)*X 1 2+(4358295063/10000000000 : ℝ)*X 2 0+(4230952079/10000000000 : ℝ)*X 2 1+(897882229/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1187_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1072711839/5000000000 : ℝ)*X 0 0+(5265313417/10000000000 : ℝ)*X 0 1+(5393424333/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1187_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5312232177/10000000000 : ℝ)*X 1 0+(-1041151821/5000000000 : ℝ)*X 1 1+(5393424319/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1187_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5312232177/10000000000 : ℝ)*X 2 0+(5393424317/10000000000 : ℝ)*X 2 1+(-520575911/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1187_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2179152691/5000000000 : ℝ)*X 0 0+(4488745299/10000000000 : ℝ)*X 0 1+(2115810183/5000000000 : ℝ)*X 0 2+(2179152691/5000000000 : ℝ)*X 1 0+(4488745299/10000000000 : ℝ)*X 1 1+(2115810183/5000000000 : ℝ)*X 1 2+(2179152691/5000000000 : ℝ)*X 2 0+(4488745299/10000000000 : ℝ)*X 2 1+(2115810183/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1187_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (307701979564992698950446563/124000000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (204181731/50000000000000 : ℝ)*(base19) + (110215919/25000000000000 : ℝ)*(base23) + (2119849/5000000000000 : ℝ)*(upper3) + (1021207/50000000000000 : ℝ)*(upper4) + (56380321/100000000000000 : ℝ)*(upper5) + (1163456284021919/20000000000000 : ℝ)*(major0) + (1163456284021919/20000000000000 : ℝ)*(major1) + (1454320355027399/25000000000000 : ℝ)*(major2) + (7765455519884767/100000000000000 : ℝ)*(sp0) + (7765466260341273/100000000000000 : ℝ)*(sp1) + (388273311392053/5000000000000 : ℝ)*(sp2) + (1934545193278829/50000000000000 : ℝ)*(sp3) + (21775039/195312500000 : ℝ)*(sp4) + (2851120601/50000000000000 : ℝ)*(sp7) + (193454804439943/5000000000000 : ℝ)*(f.failure) + (1553093333740947/20000000000000 : ℝ)*(f.sum) + (409203784473/1984000000000000000000000000 : ℝ)*base65 + (84460000650364397/148800000000000000000000000000000 : ℝ)*base67 + (631186905412401613/186000000000000000000000000000000 : ℝ)*base70 + (1314905995727164397/148800000000000000000000000000000 : ℝ)*base71 + (504297936319/79360000000000000000000000 : ℝ)*base74 + (2010632192644401613/186000000000000000000000000000000 : ℝ)*base76 + (1250132189906520201/49600000000000000000000000000000 : ℝ)*base78 + (697355168778279799/49600000000000000000000000000000 : ℝ)*base79 + (14115817390177/2976000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (8389381/500000000000000000000 : ℝ)*base89 + (8389381/500000000000000000000 : ℝ)*base91 + (3389381/500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (205502948653659387479754711/62000000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (665387327/100000000000000 : ℝ)*(base19) + (354954669/50000000000000 : ℝ)*(base23) + (68883047/100000000000000 : ℝ)*(upper3) + (1281251/6250000000000 : ℝ)*(lower4) + (68440221/100000000000000 : ℝ)*(upper5) + (2923723866688797/50000000000000 : ℝ)*(major0) + (2923723866688797/50000000000000 : ℝ)*(major1) + (2923723866688797/50000000000000 : ℝ)*(major2) + (3530052257/20000000000000 : ℝ)*(sp1) + (4653235227/25000000000000 : ℝ)*(sp2) + (7805735537310719/100000000000000 : ℝ)*(sp4) + (7805717221662107/100000000000000 : ℝ)*(sp5) + (975714526807559/12500000000000 : ℝ)*(sp6) + (1944579909479501/50000000000000 : ℝ)*(sp7) + (1944579909479501/50000000000000 : ℝ)*(f.failure) + (7805735537310719/100000000000000 : ℝ)*(f.sum) + (6497207145203/496000000000000000000000000 : ℝ)*base65 + (222150932440956763/124000000000000000000000000000000 : ℝ)*base68 + (148979987952956763/124000000000000000000000000000000 : ℝ)*base70 + (998537432551043237/124000000000000000000000000000000 : ℝ)*base71 + (581190384291/496000000000000000000000000 : ℝ)*base73 + (1902856068636956763/124000000000000000000000000000000 : ℝ)*base76 + (299248085580956763/124000000000000000000000000000000 : ℝ)*base78 + (1558642838843043237/124000000000000000000000000000000 : ℝ)*base79 + (1477883685203/496000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (38721033/5000000000000000000000 : ℝ)*base90 + (38721033/5000000000000000000000 : ℝ)*base92 + (38721033/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1187_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8379/2048 : ℝ) ≤ p) (hpb : p ≤ (2095/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150352467/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7117/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5629/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (569/5000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14107/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1187_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1187_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8379/2048 : ℝ) ≤ p) (hpb : p ≤ (2095/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150352467/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4093/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9269/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (569/5000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14107/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1187_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1187_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1187_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8379/2048 : ℝ) ≤ p) (hpb : p ≤ (2095/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150352467/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4093/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9269/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (569/5000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14107/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1187_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
