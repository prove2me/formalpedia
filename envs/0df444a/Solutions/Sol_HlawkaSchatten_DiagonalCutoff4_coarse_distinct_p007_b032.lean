-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p007_b032
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:12:17.71565+00:00
-- url     : https://prove2.me/submissions/cf379b46-57f4-4e31-944d-364aab190055

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_FiniteCharts
import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_ordered_majorant
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
theorem raw_linear_data {p k A : ℝ} (hp : 1 ≤ p) (X : Fin 3 → Fin 3 → ℝ)
    (h : RawFrame p k A X) :
    RawLinearData k A X (fun j => lpNorm p (X j))
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

theorem raw_linear_data_bounds {k A T : ℝ} {X : Fin 3 → Fin 3 → ℝ} {N P : Fin 3 → ℝ}
    (h : RawLinearData k A X N P T) (hA : A ≤ 3) :
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



theorem abs_signValue (b : Bool) : |signValue b|=1 := by
  cases b <;> norm_num [signValue]

theorem abs_signedPair (X : Fin 3 → Fin 3 → ℝ) (signs : Fin 3 → Fin 3 → Bool) (i h : Fin 3) :
    |signedPair X signs i h|=|pair X i h| := by
  simp [signedPair,abs_mul,abs_signValue]

theorem chart_majorant {p k A d a rho alpha beta : ℝ}
    (hp : 1 ≤ p) (ha : 0 < a) (hap : a ≤ p)
    (hrho : 0 < rho) (hrho1 : rho ≤ 1) (halpha : 0 ≤ alpha) (hbeta : 0 ≤ beta)
    (hcorner1 : 1+rho^a ≤ (1+alpha*rho)^a)
    (hcorner2 : 1+2*rho^a ≤ (1+(alpha+beta)*rho)^a)
    (X : Fin 3 → Fin 3 → ℝ) (orders : Fin 3 → Fin 3 → Fin 3)
    (signs : Fin 3 → Fin 3 → Bool) (hX : OrderedChart p k A d X orders signs)
    (i : Fin 3)
    (hratio : signedPair X signs i (orders i 1) ≤ rho*signedPair X signs i (orders i 0)) :
    lpNorm p (pair X i) ≤ signedPair X signs i (orders i 0)+
      alpha*signedPair X signs i (orders i 1)+beta*signedPair X signs i (orders i 2) := by
  obtain ⟨h2,h21,h10⟩ := hX.ordered i
  have h1 : 0 ≤ signedPair X signs i (orders i 1) := h2.trans h21
  have h0 : 0 ≤ signedPair X signs i (orders i 0) := h1.trans h10
  have hh := ordered_majorant (M := signedPair X signs i (orders i 0))
    (u := signedPair X signs i (orders i 1)) (v := signedPair X signs i (orders i 2)) hp ha hap hrho hrho1 halpha hbeta hcorner1 hcorner2 h0
    (by simpa only [abs_of_nonneg h1,abs_of_nonneg h2] using h21)
    (by simpa only [abs_of_nonneg h1] using hratio)
  have he := HlawkaSchatten.DiagonalRealBundle.lpNorm_eq3 p (pair X i)
    (i := orders i 0) (j := orders i 1) (k := orders i 2)
    ((hX.permutation i).1.ne (by decide)) ((hX.permutation i).1.ne (by decide))
    ((hX.permutation i).1.ne (by decide))
  rw [he]
  calc
    _ ≤ signedPair X signs i (orders i 0)+alpha*|signedPair X signs i (orders i 1)|+
        beta*|signedPair X signs i (orders i 2)| := by
      simpa only [abs_signedPair] using hh
    _ = _ := by rw [abs_of_nonneg h1,abs_of_nonneg h2]

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
theorem collision_support_c307069_s0_0 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-508340979/2500000000 : ℝ)*x 0 + (-7446597477/10000000000 : ℝ)*x 1 + (2868844329/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (508340979/2500000000 : ℝ)^17 ≤ (6227707808233/50000000000000 : ℝ)^13 := by
    have hnat : (508340979 : ℕ)^17*50000000000000^13 ≤ 6227707808233^13*2500000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      508340979 2500000000 6227707808233 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (7446597477/10000000000 : ℝ)^17 ≤ (68008046970127/100000000000000 : ℝ)^13 := by
    have hnat : (7446597477 : ℕ)^17*100000000000000^13 ≤ 68008046970127^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7446597477 10000000000 68008046970127 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2868844329/10000000000 : ℝ)^17 ≤ (1221033587419/6250000000000 : ℝ)^13 := by
    have hnat : (2868844329 : ℕ)^17*6250000000000^13 ≤ 1221033587419^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2868844329 10000000000 1221033587419 6250000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-508340979/2500000000 : ℝ), (-7446597477/10000000000 : ℝ), (2868844329/10000000000 : ℝ)] ![(6227707808233/50000000000000 : ℝ), (68008046970127/100000000000000 : ℝ), (1221033587419/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-508340979/2500000000 : ℝ)|^17 ≤ (6227707808233/50000000000000 : ℝ)^13
        have hw : |(-508340979/2500000000 : ℝ)|=(508340979/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-7446597477/10000000000 : ℝ)|^17 ≤ (68008046970127/100000000000000 : ℝ)^13
        have hw : |(-7446597477/10000000000 : ℝ)|=(7446597477/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2868844329/10000000000 : ℝ)|^17 ≤ (1221033587419/6250000000000 : ℝ)^13
        have hw : |(2868844329/10000000000 : ℝ)|=(2868844329/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307069_s0_4 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (0 : ℝ)*x 0 + (-1 : ℝ)*x 1 + (0 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (0 : ℝ)^17 ≤ (0 : ℝ)^13 := by
    have hnat : (0 : ℕ)^17*1^13 ≤ 0^13*1^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      0 1 0 1 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1 : ℝ)^17 ≤ (1 : ℝ)^13 := by
    have hnat : (1 : ℕ)^17*1^13 ≤ 1^13*1^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1 1 1 1 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (0 : ℝ)^17 ≤ (0 : ℝ)^13 := by
    have hnat : (0 : ℕ)^17*1^13 ≤ 0^13*1^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      0 1 0 1 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(0 : ℝ), (-1 : ℝ), (0 : ℝ)] ![(0 : ℝ), (1 : ℝ), (0 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(0 : ℝ)|^17 ≤ (0 : ℝ)^13
        have hw : |(0 : ℝ)|=(0 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1 : ℝ)|^17 ≤ (1 : ℝ)^13
        have hw : |(-1 : ℝ)|=(1 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(0 : ℝ)|^17 ≤ (0 : ℝ)^13
        have hw : |(0 : ℝ)|=(0 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307069_s0_6 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (1174143319/2000000000 : ℝ)*x 0 + (-541476127/2000000000 : ℝ)*x 1 + (261842761/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1174143319/2000000000 : ℝ)^17 ≤ (9966648611043/20000000000000 : ℝ)^13 := by
    have hnat : (1174143319 : ℕ)^17*20000000000000^13 ≤ 9966648611043^13*2000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1174143319 2000000000 9966648611043 20000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (541476127/2000000000 : ℝ)^17 ≤ (1811127848357/10000000000000 : ℝ)^13 := by
    have hnat : (541476127 : ℕ)^17*10000000000000^13 ≤ 1811127848357^13*2000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      541476127 2000000000 1811127848357 10000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (261842761/625000000 : ℝ)^17 ≤ (8013869613063/25000000000000 : ℝ)^13 := by
    have hnat : (261842761 : ℕ)^17*25000000000000^13 ≤ 8013869613063^13*625000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      261842761 625000000 8013869613063 25000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1174143319/2000000000 : ℝ), (-541476127/2000000000 : ℝ), (261842761/625000000 : ℝ)] ![(9966648611043/20000000000000 : ℝ), (1811127848357/10000000000000 : ℝ), (8013869613063/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1174143319/2000000000 : ℝ)|^17 ≤ (9966648611043/20000000000000 : ℝ)^13
        have hw : |(1174143319/2000000000 : ℝ)|=(1174143319/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-541476127/2000000000 : ℝ)|^17 ≤ (1811127848357/10000000000000 : ℝ)^13
        have hw : |(-541476127/2000000000 : ℝ)|=(541476127/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(261842761/625000000 : ℝ)|^17 ≤ (8013869613063/25000000000000 : ℝ)^13
        have hw : |(261842761/625000000 : ℝ)|=(261842761/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307069_s0_7 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-1534045307/10000000000 : ℝ)*x 0 + (-2061797369/2500000000 : ℝ)*x 1 + (1091035767/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1534045307/10000000000 : ℝ)^17 ≤ (430820999027/5000000000000 : ℝ)^13 := by
    have hnat : (1534045307 : ℕ)^17*5000000000000^13 ≤ 430820999027^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1534045307 10000000000 430820999027 5000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2061797369/2500000000 : ℝ)^17 ≤ (77723788970649/100000000000000 : ℝ)^13 := by
    have hnat : (2061797369 : ℕ)^17*100000000000000^13 ≤ 77723788970649^13*2500000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2061797369 2500000000 77723788970649 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1091035767/5000000000 : ℝ)^17 ≤ (6829895518917/50000000000000 : ℝ)^13 := by
    have hnat : (1091035767 : ℕ)^17*50000000000000^13 ≤ 6829895518917^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1091035767 5000000000 6829895518917 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1534045307/10000000000 : ℝ), (-2061797369/2500000000 : ℝ), (1091035767/5000000000 : ℝ)] ![(430820999027/5000000000000 : ℝ), (77723788970649/100000000000000 : ℝ), (6829895518917/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1534045307/10000000000 : ℝ)|^17 ≤ (430820999027/5000000000000 : ℝ)^13
        have hw : |(-1534045307/10000000000 : ℝ)|=(1534045307/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2061797369/2500000000 : ℝ)|^17 ≤ (77723788970649/100000000000000 : ℝ)^13
        have hw : |(-2061797369/2500000000 : ℝ)|=(2061797369/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1091035767/5000000000 : ℝ)|^17 ≤ (6829895518917/50000000000000 : ℝ)^13
        have hw : |(1091035767/5000000000 : ℝ)|=(1091035767/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307069_s0_8 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (5662064363/10000000000 : ℝ)*x 0 + (2627368869/10000000000 : ℝ)*x 1 + (4486139/10000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5662064363/10000000000 : ℝ)^17 ≤ (47529916199499/100000000000000 : ℝ)^13 := by
    have hnat : (5662064363 : ℕ)^17*100000000000000^13 ≤ 47529916199499^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5662064363 10000000000 47529916199499 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2627368869/10000000000 : ℝ)^17 ≤ (870727270299/5000000000000 : ℝ)^13 := by
    have hnat : (2627368869 : ℕ)^17*5000000000000^13 ≤ 870727270299^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2627368869 10000000000 870727270299 5000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4486139/10000000 : ℝ)^17 ≤ (3505553838361/10000000000000 : ℝ)^13 := by
    have hnat : (4486139 : ℕ)^17*10000000000000^13 ≤ 3505553838361^13*10000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4486139 10000000 3505553838361 10000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5662064363/10000000000 : ℝ), (2627368869/10000000000 : ℝ), (4486139/10000000 : ℝ)] ![(47529916199499/100000000000000 : ℝ), (870727270299/5000000000000 : ℝ), (3505553838361/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5662064363/10000000000 : ℝ)|^17 ≤ (47529916199499/100000000000000 : ℝ)^13
        have hw : |(5662064363/10000000000 : ℝ)|=(5662064363/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2627368869/10000000000 : ℝ)|^17 ≤ (870727270299/5000000000000 : ℝ)^13
        have hw : |(2627368869/10000000000 : ℝ)|=(2627368869/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4486139/10000000 : ℝ)|^17 ≤ (3505553838361/10000000000000 : ℝ)^13
        have hw : |(4486139/10000000 : ℝ)|=(4486139/10000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307069_s0_9 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (4180370087/10000000000 : ℝ)*x 0 + (-524260511/2000000000 : ℝ)*x 1 + (-5946282371/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4180370087/10000000000 : ℝ)^17 ≤ (1997769761887/6250000000000 : ℝ)^13 := by
    have hnat : (4180370087 : ℕ)^17*6250000000000^13 ≤ 1997769761887^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4180370087 10000000000 1997769761887 6250000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (524260511/2000000000 : ℝ)^17 ≤ (17361983976233/100000000000000 : ℝ)^13 := by
    have hnat : (524260511 : ℕ)^17*100000000000000^13 ≤ 17361983976233^13*2000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      524260511 2000000000 17361983976233 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5946282371/10000000000 : ℝ)^17 ≤ (50673699821671/100000000000000 : ℝ)^13 := by
    have hnat : (5946282371 : ℕ)^17*100000000000000^13 ≤ 50673699821671^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5946282371 10000000000 50673699821671 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4180370087/10000000000 : ℝ), (-524260511/2000000000 : ℝ), (-5946282371/10000000000 : ℝ)] ![(1997769761887/6250000000000 : ℝ), (17361983976233/100000000000000 : ℝ), (50673699821671/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4180370087/10000000000 : ℝ)|^17 ≤ (1997769761887/6250000000000 : ℝ)^13
        have hw : |(4180370087/10000000000 : ℝ)|=(4180370087/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-524260511/2000000000 : ℝ)|^17 ≤ (17361983976233/100000000000000 : ℝ)^13
        have hw : |(-524260511/2000000000 : ℝ)|=(524260511/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-5946282371/10000000000 : ℝ)|^17 ≤ (50673699821671/100000000000000 : ℝ)^13
        have hw : |(-5946282371/10000000000 : ℝ)|=(5946282371/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307069_s0_13 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-2312250033/10000000000 : ℝ)*x 0 + (-1482560651/2000000000 : ℝ)*x 1 + (2655660129/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2312250033/10000000000 : ℝ)^17 ≤ (14735103563373/100000000000000 : ℝ)^13 := by
    have hnat : (2312250033 : ℕ)^17*100000000000000^13 ≤ 14735103563373^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2312250033 10000000000 14735103563373 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1482560651/2000000000 : ℝ)^17 ≤ (8450591214313/12500000000000 : ℝ)^13 := by
    have hnat : (1482560651 : ℕ)^17*12500000000000^13 ≤ 8450591214313^13*2000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1482560651 2000000000 8450591214313 12500000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2655660129/10000000000 : ℝ)^17 ≤ (4415041677377/25000000000000 : ℝ)^13 := by
    have hnat : (2655660129 : ℕ)^17*25000000000000^13 ≤ 4415041677377^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2655660129 10000000000 4415041677377 25000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2312250033/10000000000 : ℝ), (-1482560651/2000000000 : ℝ), (2655660129/10000000000 : ℝ)] ![(14735103563373/100000000000000 : ℝ), (8450591214313/12500000000000 : ℝ), (4415041677377/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2312250033/10000000000 : ℝ)|^17 ≤ (14735103563373/100000000000000 : ℝ)^13
        have hw : |(-2312250033/10000000000 : ℝ)|=(2312250033/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1482560651/2000000000 : ℝ)|^17 ≤ (8450591214313/12500000000000 : ℝ)^13
        have hw : |(-1482560651/2000000000 : ℝ)|=(1482560651/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2655660129/10000000000 : ℝ)|^17 ≤ (4415041677377/25000000000000 : ℝ)^13
        have hw : |(2655660129/10000000000 : ℝ)|=(2655660129/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307069_s0_14 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (589284791/1000000000 : ℝ)*x 0 + (504099837/2000000000 : ℝ)*x 1 + (4325865567/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (589284791/1000000000 : ℝ)^17 ≤ (1564970281723/3125000000000 : ℝ)^13 := by
    have hnat : (589284791 : ℕ)^17*3125000000000^13 ≤ 1564970281723^13*1000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      589284791 1000000000 1564970281723 3125000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (504099837/2000000000 : ℝ)^17 ≤ (16494098365263/100000000000000 : ℝ)^13 := by
    have hnat : (504099837 : ℕ)^17*100000000000000^13 ≤ 16494098365263^13*2000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      504099837 2000000000 16494098365263 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4325865567/10000000000 : ℝ)^17 ≤ (33426852600847/100000000000000 : ℝ)^13 := by
    have hnat : (4325865567 : ℕ)^17*100000000000000^13 ≤ 33426852600847^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4325865567 10000000000 33426852600847 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(589284791/1000000000 : ℝ), (504099837/2000000000 : ℝ), (4325865567/10000000000 : ℝ)] ![(1564970281723/3125000000000 : ℝ), (16494098365263/100000000000000 : ℝ), (33426852600847/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(589284791/1000000000 : ℝ)|^17 ≤ (1564970281723/3125000000000 : ℝ)^13
        have hw : |(589284791/1000000000 : ℝ)|=(589284791/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(504099837/2000000000 : ℝ)|^17 ≤ (16494098365263/100000000000000 : ℝ)^13
        have hw : |(504099837/2000000000 : ℝ)|=(504099837/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4325865567/10000000000 : ℝ)|^17 ≤ (33426852600847/100000000000000 : ℝ)^13
        have hw : |(4325865567/10000000000 : ℝ)|=(4325865567/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307069_s0_15 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (1871189313/5000000000 : ℝ)*x 0 + (-98338899/312500000 : ℝ)*x 1 + (-2956110877/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1871189313/5000000000 : ℝ)^17 ≤ (13828611207693/50000000000000 : ℝ)^13 := by
    have hnat : (1871189313 : ℕ)^17*50000000000000^13 ≤ 13828611207693^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1871189313 5000000000 13828611207693 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (98338899/312500000 : ℝ)^17 ≤ (22048315682521/100000000000000 : ℝ)^13 := by
    have hnat : (98338899 : ℕ)^17*100000000000000^13 ≤ 22048315682521^13*312500000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      98338899 312500000 22048315682521 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2956110877/5000000000 : ℝ)^17 ≤ (1257361547187/2500000000000 : ℝ)^13 := by
    have hnat : (2956110877 : ℕ)^17*2500000000000^13 ≤ 1257361547187^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2956110877 5000000000 1257361547187 2500000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1871189313/5000000000 : ℝ), (-98338899/312500000 : ℝ), (-2956110877/5000000000 : ℝ)] ![(13828611207693/50000000000000 : ℝ), (22048315682521/100000000000000 : ℝ), (1257361547187/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1871189313/5000000000 : ℝ)|^17 ≤ (13828611207693/50000000000000 : ℝ)^13
        have hw : |(1871189313/5000000000 : ℝ)|=(1871189313/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-98338899/312500000 : ℝ)|^17 ≤ (22048315682521/100000000000000 : ℝ)^13
        have hw : |(-98338899/312500000 : ℝ)|=(98338899/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2956110877/5000000000 : ℝ)|^17 ≤ (1257361547187/2500000000000 : ℝ)^13
        have hw : |(-2956110877/5000000000 : ℝ)|=(2956110877/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307069_s0_19 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (589284791/1000000000 : ℝ)*x 0 + (-1815714787/5000000000 : ℝ)*x 1 + (3285908577/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (589284791/1000000000 : ℝ)^17 ≤ (1564970281723/3125000000000 : ℝ)^13 := by
    have hnat : (589284791 : ℕ)^17*3125000000000^13 ≤ 1564970281723^13*1000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      589284791 1000000000 1564970281723 3125000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1815714787/5000000000 : ℝ)^17 ≤ (2658991173367/10000000000000 : ℝ)^13 := by
    have hnat : (1815714787 : ℕ)^17*10000000000000^13 ≤ 2658991173367^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1815714787 5000000000 2658991173367 10000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3285908577/10000000000 : ℝ)^17 ≤ (933241569377/4000000000000 : ℝ)^13 := by
    have hnat : (3285908577 : ℕ)^17*4000000000000^13 ≤ 933241569377^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3285908577 10000000000 933241569377 4000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(589284791/1000000000 : ℝ), (-1815714787/5000000000 : ℝ), (3285908577/10000000000 : ℝ)] ![(1564970281723/3125000000000 : ℝ), (2658991173367/10000000000000 : ℝ), (933241569377/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(589284791/1000000000 : ℝ)|^17 ≤ (1564970281723/3125000000000 : ℝ)^13
        have hw : |(589284791/1000000000 : ℝ)|=(589284791/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1815714787/5000000000 : ℝ)|^17 ≤ (2658991173367/10000000000000 : ℝ)^13
        have hw : |(-1815714787/5000000000 : ℝ)|=(1815714787/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3285908577/10000000000 : ℝ)|^17 ≤ (933241569377/4000000000000 : ℝ)^13
        have hw : |(3285908577/10000000000 : ℝ)|=(3285908577/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307069_s0_20 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-256938869/2000000000 : ℝ)*x 0 + (-205228631/250000000 : ℝ)*x 1 + (490441969/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (256938869/2000000000 : ℝ)^17 ≤ (3416287205363/50000000000000 : ℝ)^13 := by
    have hnat : (256938869 : ℕ)^17*50000000000000^13 ≤ 3416287205363^13*2000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      256938869 2000000000 3416287205363 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (205228631/250000000 : ℝ)^17 ≤ (38627631443291/50000000000000 : ℝ)^13 := by
    have hnat : (205228631 : ℕ)^17*50000000000000^13 ≤ 38627631443291^13*250000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      205228631 250000000 38627631443291 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (490441969/2000000000 : ℝ)^17 ≤ (1989020337089/12500000000000 : ℝ)^13 := by
    have hnat : (490441969 : ℕ)^17*12500000000000^13 ≤ 1989020337089^13*2000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      490441969 2000000000 1989020337089 12500000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-256938869/2000000000 : ℝ), (-205228631/250000000 : ℝ), (490441969/2000000000 : ℝ)] ![(3416287205363/50000000000000 : ℝ), (38627631443291/50000000000000 : ℝ), (1989020337089/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-256938869/2000000000 : ℝ)|^17 ≤ (3416287205363/50000000000000 : ℝ)^13
        have hw : |(-256938869/2000000000 : ℝ)|=(256938869/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-205228631/250000000 : ℝ)|^17 ≤ (38627631443291/50000000000000 : ℝ)^13
        have hw : |(-205228631/250000000 : ℝ)|=(205228631/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(490441969/2000000000 : ℝ)|^17 ≤ (1989020337089/12500000000000 : ℝ)^13
        have hw : |(490441969/2000000000 : ℝ)|=(490441969/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307069_s0_21 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (3466683047/5000000000 : ℝ)*x 0 + (1081467259/5000000000 : ℝ)*x 1 + (427076643/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3466683047/5000000000 : ℝ)^17 ≤ (12388931766033/20000000000000 : ℝ)^13 := by
    have hnat : (3466683047 : ℕ)^17*20000000000000^13 ≤ 12388931766033^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3466683047 5000000000 12388931766033 20000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1081467259/5000000000 : ℝ)^17 ≤ (421979500477/3125000000000 : ℝ)^13 := by
    have hnat : (1081467259 : ℕ)^17*3125000000000^13 ≤ 421979500477^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1081467259 5000000000 421979500477 3125000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (427076643/1250000000 : ℝ)^17 ≤ (982079885883/4000000000000 : ℝ)^13 := by
    have hnat : (427076643 : ℕ)^17*4000000000000^13 ≤ 982079885883^13*1250000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      427076643 1250000000 982079885883 4000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3466683047/5000000000 : ℝ), (1081467259/5000000000 : ℝ), (427076643/1250000000 : ℝ)] ![(12388931766033/20000000000000 : ℝ), (421979500477/3125000000000 : ℝ), (982079885883/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3466683047/5000000000 : ℝ)|^17 ≤ (12388931766033/20000000000000 : ℝ)^13
        have hw : |(3466683047/5000000000 : ℝ)|=(3466683047/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1081467259/5000000000 : ℝ)|^17 ≤ (421979500477/3125000000000 : ℝ)^13
        have hw : |(1081467259/5000000000 : ℝ)|=(1081467259/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(427076643/1250000000 : ℝ)|^17 ≤ (982079885883/4000000000000 : ℝ)^13
        have hw : |(427076643/1250000000 : ℝ)|=(427076643/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307069_s0_22 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (1618018807/5000000000 : ℝ)*x 0 + (-3344000737/10000000000 : ℝ)*x 1 + (-6176911517/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1618018807/5000000000 : ℝ)^17 ≤ (4573813989421/20000000000000 : ℝ)^13 := by
    have hnat : (1618018807 : ℕ)^17*20000000000000^13 ≤ 4573813989421^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1618018807 5000000000 4573813989421 20000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3344000737/10000000000 : ℝ)^17 ≤ (2983986110697/12500000000000 : ℝ)^13 := by
    have hnat : (3344000737 : ℕ)^17*12500000000000^13 ≤ 2983986110697^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3344000737 10000000000 2983986110697 12500000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6176911517/10000000000 : ℝ)^17 ≤ (26629520574737/50000000000000 : ℝ)^13 := by
    have hnat : (6176911517 : ℕ)^17*50000000000000^13 ≤ 26629520574737^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6176911517 10000000000 26629520574737 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1618018807/5000000000 : ℝ), (-3344000737/10000000000 : ℝ), (-6176911517/10000000000 : ℝ)] ![(4573813989421/20000000000000 : ℝ), (2983986110697/12500000000000 : ℝ), (26629520574737/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1618018807/5000000000 : ℝ)|^17 ≤ (4573813989421/20000000000000 : ℝ)^13
        have hw : |(1618018807/5000000000 : ℝ)|=(1618018807/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3344000737/10000000000 : ℝ)|^17 ≤ (2983986110697/12500000000000 : ℝ)^13
        have hw : |(-3344000737/10000000000 : ℝ)|=(3344000737/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-6176911517/10000000000 : ℝ)|^17 ≤ (26629520574737/50000000000000 : ℝ)^13
        have hw : |(-6176911517/10000000000 : ℝ)|=(6176911517/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307069_s0_25 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (3466683047/5000000000 : ℝ)*x 0 + (-1081467259/5000000000 : ℝ)*x 1 + (427076643/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3466683047/5000000000 : ℝ)^17 ≤ (12388931766033/20000000000000 : ℝ)^13 := by
    have hnat : (3466683047 : ℕ)^17*20000000000000^13 ≤ 12388931766033^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3466683047 5000000000 12388931766033 20000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1081467259/5000000000 : ℝ)^17 ≤ (421979500477/3125000000000 : ℝ)^13 := by
    have hnat : (1081467259 : ℕ)^17*3125000000000^13 ≤ 421979500477^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1081467259 5000000000 421979500477 3125000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (427076643/1250000000 : ℝ)^17 ≤ (982079885883/4000000000000 : ℝ)^13 := by
    have hnat : (427076643 : ℕ)^17*4000000000000^13 ≤ 982079885883^13*1250000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      427076643 1250000000 982079885883 4000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3466683047/5000000000 : ℝ), (-1081467259/5000000000 : ℝ), (427076643/1250000000 : ℝ)] ![(12388931766033/20000000000000 : ℝ), (421979500477/3125000000000 : ℝ), (982079885883/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3466683047/5000000000 : ℝ)|^17 ≤ (12388931766033/20000000000000 : ℝ)^13
        have hw : |(3466683047/5000000000 : ℝ)|=(3466683047/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1081467259/5000000000 : ℝ)|^17 ≤ (421979500477/3125000000000 : ℝ)^13
        have hw : |(-1081467259/5000000000 : ℝ)|=(1081467259/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(427076643/1250000000 : ℝ)|^17 ≤ (982079885883/4000000000000 : ℝ)^13
        have hw : |(427076643/1250000000 : ℝ)|=(427076643/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307069_s1_0 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-3356531243/10000000000 : ℝ)*x 0 + (-5481316403/10000000000 : ℝ)*x 1 + (4028615519/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3356531243/10000000000 : ℝ)^17 ≤ (23988931677889/100000000000000 : ℝ)^13 := by
    have hnat : (3356531243 : ℕ)^17*100000000000000^13 ≤ 23988931677889^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3356531243 10000000000 23988931677889 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5481316403/10000000000 : ℝ)^17 ≤ (1822223935683/4000000000000 : ℝ)^13 := by
    have hnat : (5481316403 : ℕ)^17*4000000000000^13 ≤ 1822223935683^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5481316403 10000000000 1822223935683 4000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4028615519/10000000000 : ℝ)^17 ≤ (30455469916409/100000000000000 : ℝ)^13 := by
    have hnat : (4028615519 : ℕ)^17*100000000000000^13 ≤ 30455469916409^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4028615519 10000000000 30455469916409 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-3356531243/10000000000 : ℝ), (-5481316403/10000000000 : ℝ), (4028615519/10000000000 : ℝ)] ![(23988931677889/100000000000000 : ℝ), (1822223935683/4000000000000 : ℝ), (30455469916409/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-3356531243/10000000000 : ℝ)|^17 ≤ (23988931677889/100000000000000 : ℝ)^13
        have hw : |(-3356531243/10000000000 : ℝ)|=(3356531243/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-5481316403/10000000000 : ℝ)|^17 ≤ (1822223935683/4000000000000 : ℝ)^13
        have hw : |(-5481316403/10000000000 : ℝ)|=(5481316403/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4028615519/10000000000 : ℝ)|^17 ≤ (30455469916409/100000000000000 : ℝ)^13
        have hw : |(4028615519/10000000000 : ℝ)|=(4028615519/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307069_s1_1 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (1047582399/2000000000 : ℝ)*x 0 + (862099897/2500000000 : ℝ)*x 1 + (4205958123/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1047582399/2000000000 : ℝ)^17 ≤ (670757227561/1562500000000 : ℝ)^13 := by
    have hnat : (1047582399 : ℕ)^17*1562500000000^13 ≤ 670757227561^13*2000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1047582399 2000000000 670757227561 1562500000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (862099897/2500000000 : ℝ)^17 ≤ (4970225208731/20000000000000 : ℝ)^13 := by
    have hnat : (862099897 : ℕ)^17*20000000000000^13 ≤ 4970225208731^13*2500000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      862099897 2500000000 4970225208731 20000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4205958123/10000000000 : ℝ)^17 ≤ (32220411374687/100000000000000 : ℝ)^13 := by
    have hnat : (4205958123 : ℕ)^17*100000000000000^13 ≤ 32220411374687^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4205958123 10000000000 32220411374687 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1047582399/2000000000 : ℝ), (862099897/2500000000 : ℝ), (4205958123/10000000000 : ℝ)] ![(670757227561/1562500000000 : ℝ), (4970225208731/20000000000000 : ℝ), (32220411374687/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1047582399/2000000000 : ℝ)|^17 ≤ (670757227561/1562500000000 : ℝ)^13
        have hw : |(1047582399/2000000000 : ℝ)|=(1047582399/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(862099897/2500000000 : ℝ)|^17 ≤ (4970225208731/20000000000000 : ℝ)^13
        have hw : |(862099897/2500000000 : ℝ)|=(862099897/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4205958123/10000000000 : ℝ)|^17 ≤ (32220411374687/100000000000000 : ℝ)^13
        have hw : |(4205958123/10000000000 : ℝ)|=(4205958123/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307069_s1_2 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (2034793553/5000000000 : ℝ)*x 0 + (-994566507/2500000000 : ℝ)*x 1 + (-2442223919/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2034793553/5000000000 : ℝ)^17 ≤ (30861142105483/100000000000000 : ℝ)^13 := by
    have hnat : (2034793553 : ℕ)^17*100000000000000^13 ≤ 30861142105483^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2034793553 5000000000 30861142105483 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (994566507/2500000000 : ℝ)^17 ≤ (29958681041491/100000000000000 : ℝ)^13 := by
    have hnat : (994566507 : ℕ)^17*100000000000000^13 ≤ 29958681041491^13*2500000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      994566507 2500000000 29958681041491 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2442223919/5000000000 : ℝ)^17 ≤ (9795044207701/25000000000000 : ℝ)^13 := by
    have hnat : (2442223919 : ℕ)^17*25000000000000^13 ≤ 9795044207701^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2442223919 5000000000 9795044207701 25000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2034793553/5000000000 : ℝ), (-994566507/2500000000 : ℝ), (-2442223919/5000000000 : ℝ)] ![(30861142105483/100000000000000 : ℝ), (29958681041491/100000000000000 : ℝ), (9795044207701/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2034793553/5000000000 : ℝ)|^17 ≤ (30861142105483/100000000000000 : ℝ)^13
        have hw : |(2034793553/5000000000 : ℝ)|=(2034793553/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-994566507/2500000000 : ℝ)|^17 ≤ (29958681041491/100000000000000 : ℝ)^13
        have hw : |(-994566507/2500000000 : ℝ)|=(994566507/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2442223919/5000000000 : ℝ)|^17 ≤ (9795044207701/25000000000000 : ℝ)^13
        have hw : |(-2442223919/5000000000 : ℝ)|=(2442223919/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307069_s1_6 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (599379291/1250000000 : ℝ)*x 0 + (-2144258067/5000000000 : ℝ)*x 1 + (3850334561/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (599379291/1250000000 : ℝ)^17 ≤ (38244922795963/100000000000000 : ℝ)^13 := by
    have hnat : (599379291 : ℕ)^17*100000000000000^13 ≤ 38244922795963^13*1250000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      599379291 1250000000 38244922795963 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2144258067/5000000000 : ℝ)^17 ≤ (8262486523369/25000000000000 : ℝ)^13 := by
    have hnat : (2144258067 : ℕ)^17*25000000000000^13 ≤ 8262486523369^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2144258067 5000000000 8262486523369 25000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3850334561/10000000000 : ℝ)^17 ≤ (28705131091929/100000000000000 : ℝ)^13 := by
    have hnat : (3850334561 : ℕ)^17*100000000000000^13 ≤ 28705131091929^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3850334561 10000000000 28705131091929 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(599379291/1250000000 : ℝ), (-2144258067/5000000000 : ℝ), (3850334561/10000000000 : ℝ)] ![(38244922795963/100000000000000 : ℝ), (8262486523369/25000000000000 : ℝ), (28705131091929/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(599379291/1250000000 : ℝ)|^17 ≤ (38244922795963/100000000000000 : ℝ)^13
        have hw : |(599379291/1250000000 : ℝ)|=(599379291/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2144258067/5000000000 : ℝ)|^17 ≤ (8262486523369/25000000000000 : ℝ)^13
        have hw : |(-2144258067/5000000000 : ℝ)|=(2144258067/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3850334561/10000000000 : ℝ)|^17 ≤ (28705131091929/100000000000000 : ℝ)^13
        have hw : |(3850334561/10000000000 : ℝ)|=(3850334561/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c307069 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (19431/12500 : ℝ) (92559/50000 : ℝ) (4817/6250 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, false], ![true, false, true]]) : False := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (4817/6250 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (4817/6250 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (4817/6250 : ℝ)*P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (4817/6250 : ℝ)*P 1 ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 0+X 2 0)) ∧ ((-1 : ℝ)*(X 0 0+X 2 0)) ≤ ((-1 : ℝ)*(X 0 2+X 2 2)) ∧ ((-1 : ℝ)*(X 0 2+X 2 2)) ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 0) ∧ ((-1 : ℝ)*pair X 1 0) ≤ ((-1 : ℝ)*pair X 1 2) ∧ ((-1 : ℝ)*pair X 1 2) ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (4817/6250 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (4817/6250 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((-1 : ℝ)*(X 0 1+X 1 1)) ∧ ((-1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((-1 : ℝ)*pair X 2 1) ∧ ((-1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base3 : ((1 : ℝ)*N 1+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 1]
  have base15 : ((1 : ℝ)*X 1 0+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 0).2]
  have base22 : ((-1 : ℝ)*X 2 1+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 1).1]
  have base33 : ((-1 : ℝ)*N 1+(-1 : ℝ)*N 2+(1 : ℝ)*P 0) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 0,f.sum]
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base49 : ((1 : ℝ)*X 0 0+(1 : ℝ)*X 2 0) ≤ (0 : ℝ) := by
    linarith only [order1.1]
  have base50 : ((-1 : ℝ)*X 0 0+(1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 0+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.2.1]
  have base59 : ((1 : ℝ)*X 0 1+(1 : ℝ)*X 1 1) ≤ (0 : ℝ) := by
    linarith only [order2.1]
  have base60 : ((-1 : ℝ)*X 0 0+(-1 : ℝ)*X 0 1+(-1 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1) ≤ (0 : ℝ) := by
    linarith only [order2.2.1]
  have base62 : ((-1 : ℝ)*X 0 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 0).1]
  have base63 : ((1 : ℝ)*X 0 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 0).2]
  have base64 : ((-1 : ℝ)*X 0 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 1).1]
  have base65 : ((1 : ℝ)*X 0 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 1).2]
  have base66 : ((-1 : ℝ)*X 0 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 2).1]
  have base67 : ((1 : ℝ)*X 0 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 2).2]
  have base68 : ((-1 : ℝ)*X 1 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 0).1]
  have base69 : ((1 : ℝ)*X 1 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 0).2]
  have base70 : ((-1 : ℝ)*X 1 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 1).1]
  have base71 : ((1 : ℝ)*X 1 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 1).2]
  have base72 : ((-1 : ℝ)*X 1 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 2).1]
  have base73 : ((1 : ℝ)*X 1 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 2).2]
  have base74 : ((-1 : ℝ)*X 2 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 0).1]
  have base75 : ((1 : ℝ)*X 2 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 0).2]
  have base76 : ((-1 : ℝ)*X 2 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 1).1]
  have base77 : ((1 : ℝ)*X 2 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 1).2]
  have base78 : ((-1 : ℝ)*X 2 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 2).1]
  have base79 : ((1 : ℝ)*X 2 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 2).2]
  have base80 : ((-1 : ℝ)*N 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 0).1]
  have base81 : ((1 : ℝ)*N 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 0).2]
  have base82 : ((-1 : ℝ)*N 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 1).1]
  have base83 : ((1 : ℝ)*N 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 1).2]
  have base84 : ((-1 : ℝ)*N 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 2).1]
  have base85 : ((1 : ℝ)*N 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 2).2]
  have base86 : ((-1 : ℝ)*P 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 0).1]
  have base87 : ((1 : ℝ)*P 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 0).2]
  have base88 : ((-1 : ℝ)*P 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 1).1]
  have base89 : ((1 : ℝ)*P 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 1).2]
  have base90 : ((-1 : ℝ)*P 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 2).1]
  have base91 : ((1 : ℝ)*P 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 2).2]
  have base92 : ((-1 : ℝ)*T) ≤ (3 : ℝ) := by
    linarith only [bounds.2.2.2.1]
  have base93 : ((1 : ℝ)*T) ≤ (3 : ℝ) := by
    linarith only [bounds.2.2.2.2]
  have s0_pow0 : (1 : ℝ) ^ (135/32 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^135 ≤ (1 : ℝ)^32 := by
      have hnat : (1 : ℕ)^135*1^32 ≤ 1^32*1^135 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 135 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 135 32 (by norm_num) hpowers
    exact h
  have s0_corner0a : (2 : ℝ) ≤ (5892848319012779/5000000000000000 : ℝ) ^ (135/32 : ℝ) := by
    have hpowers : (2 : ℝ)^32 ≤ (5892848319012779/5000000000000000 : ℝ)^135 := by
      have hnat : (2 : ℕ)^32*5000000000000000^135 ≤ 5892848319012779^135*1^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 5892848319012779 5000000000000000 32 135 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5892848319012779/5000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 135 32 (by norm_num) hpowers
    exact h
  have s0_corner0b : (3 : ℝ) ≤ (12974642747381843/10000000000000000 : ℝ) ^ (135/32 : ℝ) := by
    have hpowers : (3 : ℝ)^32 ≤ (12974642747381843/10000000000000000 : ℝ)^135 := by
      have hnat : (3 : ℕ)^32*10000000000000000^135 ≤ 12974642747381843^135*1^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 12974642747381843 10000000000000000 32 135 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12974642747381843/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 135 32 (by norm_num) hpowers
    exact h
  have major_s0_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(892848319012779/5000000000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(237789221871257/2000000000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (135/32 : ℝ)) (rho := (1 : ℝ)) (alpha := (892848319012779/5000000000000000 : ℝ)) (beta := (237789221871257/2000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow0,s0_corner0a]) (by linarith only [s0_pow0,s0_corner0b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, false], ![true, false, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (1 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order0.2.2])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(892848319012779/5000000000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(237789221871257/2000000000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow1 : (1 : ℝ) ^ (135/32 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^135 ≤ (1 : ℝ)^32 := by
      have hnat : (1 : ℕ)^135*1^32 ≤ 1^32*1^135 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 135 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 135 32 (by norm_num) hpowers
    exact h
  have s0_corner1a : (2 : ℝ) ≤ (5892848319012779/5000000000000000 : ℝ) ^ (135/32 : ℝ) := by
    have hpowers : (2 : ℝ)^32 ≤ (5892848319012779/5000000000000000 : ℝ)^135 := by
      have hnat : (2 : ℕ)^32*5000000000000000^135 ≤ 5892848319012779^135*1^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 5892848319012779 5000000000000000 32 135 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5892848319012779/5000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 135 32 (by norm_num) hpowers
    exact h
  have s0_corner1b : (3 : ℝ) ≤ (12974642747381843/10000000000000000 : ℝ) ^ (135/32 : ℝ) := by
    have hpowers : (3 : ℝ)^32 ≤ (12974642747381843/10000000000000000 : ℝ)^135 := by
      have hnat : (3 : ℕ)^32*10000000000000000^135 ≤ 12974642747381843^135*1^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 12974642747381843 10000000000000000 32 135 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12974642747381843/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 135 32 (by norm_num) hpowers
    exact h
  have major_s0_1 : P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1))+(892848319012779/5000000000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2))+(237789221871257/2000000000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 2 0)) := by
    have hh := chart_majorant (a := (135/32 : ℝ)) (rho := (1 : ℝ)) (alpha := (892848319012779/5000000000000000 : ℝ)) (beta := (237789221871257/2000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow1,s0_corner1a]) (by linarith only [s0_pow1,s0_corner1b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, false], ![true, false, true]] hX 1 (by
        change ((-1 : ℝ)*pair X 1 2) ≤ (1 : ℝ)*((-1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order1.2.2])
    change lpNorm p (pair X 1) ≤ ((-1 : ℝ)*pair X 1 1)+(892848319012779/5000000000000000 : ℝ)*((-1 : ℝ)*pair X 1 2)+(237789221871257/2000000000000000 : ℝ)*((-1 : ℝ)*pair X 1 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow2 : (1 : ℝ) ^ (135/32 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^135 ≤ (1 : ℝ)^32 := by
      have hnat : (1 : ℕ)^135*1^32 ≤ 1^32*1^135 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 135 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 135 32 (by norm_num) hpowers
    exact h
  have s0_corner2a : (2 : ℝ) ≤ (5892848319012779/5000000000000000 : ℝ) ^ (135/32 : ℝ) := by
    have hpowers : (2 : ℝ)^32 ≤ (5892848319012779/5000000000000000 : ℝ)^135 := by
      have hnat : (2 : ℕ)^32*5000000000000000^135 ≤ 5892848319012779^135*1^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 5892848319012779 5000000000000000 32 135 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5892848319012779/5000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 135 32 (by norm_num) hpowers
    exact h
  have s0_corner2b : (3 : ℝ) ≤ (12974642747381843/10000000000000000 : ℝ) ^ (135/32 : ℝ) := by
    have hpowers : (3 : ℝ)^32 ≤ (12974642747381843/10000000000000000 : ℝ)^135 := by
      have hnat : (3 : ℕ)^32*10000000000000000^135 ≤ 12974642747381843^135*1^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 12974642747381843 10000000000000000 32 135 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12974642747381843/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 135 32 (by norm_num) hpowers
    exact h
  have major_s0_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(892848319012779/5000000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(237789221871257/2000000000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (135/32 : ℝ)) (rho := (1 : ℝ)) (alpha := (892848319012779/5000000000000000 : ℝ)) (beta := (237789221871257/2000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow2,s0_corner2a]) (by linarith only [s0_pow2,s0_corner2b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, false], ![true, false, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (1 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order2.2.2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(892848319012779/5000000000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(237789221871257/2000000000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s0_0 : ((-508340979/2500000000 : ℝ)*X 0 0+(-7446597477/10000000000 : ℝ)*X 0 1+(2868844329/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c307069_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_4 : ((-1 : ℝ)*X 0 1+(-1 : ℝ)*X 2 1+(-1 : ℝ)*P 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c307069_s0_4 p hpa hpb (pair X 1)
    change _ ≤ P 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_6 : ((1174143319/2000000000 : ℝ)*X 0 0+(-541476127/2000000000 : ℝ)*X 0 1+(261842761/625000000 : ℝ)*X 0 2+(1174143319/2000000000 : ℝ)*X 1 0+(-541476127/2000000000 : ℝ)*X 1 1+(261842761/625000000 : ℝ)*X 1 2+(1174143319/2000000000 : ℝ)*X 2 0+(-541476127/2000000000 : ℝ)*X 2 1+(261842761/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c307069_s0_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_7 : ((-1534045307/10000000000 : ℝ)*X 0 0+(-2061797369/2500000000 : ℝ)*X 0 1+(1091035767/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c307069_s0_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_8 : ((5662064363/10000000000 : ℝ)*X 1 0+(2627368869/10000000000 : ℝ)*X 1 1+(4486139/10000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c307069_s0_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_9 : ((4180370087/10000000000 : ℝ)*X 2 0+(-524260511/2000000000 : ℝ)*X 2 1+(-5946282371/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c307069_s0_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_13 : ((-2312250033/10000000000 : ℝ)*X 0 0+(-1482560651/2000000000 : ℝ)*X 0 1+(2655660129/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c307069_s0_13 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_14 : ((589284791/1000000000 : ℝ)*X 1 0+(504099837/2000000000 : ℝ)*X 1 1+(4325865567/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c307069_s0_14 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_15 : ((1871189313/5000000000 : ℝ)*X 2 0+(-98338899/312500000 : ℝ)*X 2 1+(-2956110877/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c307069_s0_15 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_19 : ((589284791/1000000000 : ℝ)*X 0 0+(-1815714787/5000000000 : ℝ)*X 0 1+(3285908577/10000000000 : ℝ)*X 0 2+(589284791/1000000000 : ℝ)*X 1 0+(-1815714787/5000000000 : ℝ)*X 1 1+(3285908577/10000000000 : ℝ)*X 1 2+(589284791/1000000000 : ℝ)*X 2 0+(-1815714787/5000000000 : ℝ)*X 2 1+(3285908577/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c307069_s0_19 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_20 : ((-256938869/2000000000 : ℝ)*X 0 0+(-205228631/250000000 : ℝ)*X 0 1+(490441969/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c307069_s0_20 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_21 : ((3466683047/5000000000 : ℝ)*X 1 0+(1081467259/5000000000 : ℝ)*X 1 1+(427076643/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c307069_s0_21 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_22 : ((1618018807/5000000000 : ℝ)*X 2 0+(-3344000737/10000000000 : ℝ)*X 2 1+(-6176911517/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c307069_s0_22 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_25 : ((3466683047/5000000000 : ℝ)*X 0 0+(-1081467259/5000000000 : ℝ)*X 0 1+(427076643/1250000000 : ℝ)*X 0 2+(3466683047/5000000000 : ℝ)*X 1 0+(-1081467259/5000000000 : ℝ)*X 1 1+(427076643/1250000000 : ℝ)*X 1 2+(3466683047/5000000000 : ℝ)*X 2 0+(-1081467259/5000000000 : ℝ)*X 2 1+(427076643/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c307069_s0_25 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s0_0 : (0 : ℝ) ≤ ((18907/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(18907/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (17999451330271369889889/2500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2635070738047/1000000000000 : ℝ)*(base3) + (453992428127/500000000000 : ℝ)*(base40) + (201667560077/1000000000000 : ℝ)*(base50) + (352443/125000000000 : ℝ)*(base60) + (4096164760879/1000000000000 : ℝ)*(major_s0_0) + (600742756123/40000000000 : ℝ)*(major_s0_1) + (4096164760879/1000000000000 : ℝ)*(major_s0_2) + (4461701/1000000000000 : ℝ)*(sp_s0_0) + (10922404142197/1000000000000 : ℝ)*(sp_s0_4) + (555714092899/100000000000 : ℝ)*(sp_s0_7) + (327693084873/40000000000 : ℝ)*(sp_s0_8) + (5557178280901/1000000000000 : ℝ)*(sp_s0_9) + (78102877/1000000000000 : ℝ)*(sp_s0_15) + (110993087/1000000000000 : ℝ)*(sp_s0_20) + (2635070738047/1000000000000 : ℝ)*(f.failure) + (2778628191889/500000000000 : ℝ)*(f.sum) + (7833921014469107/10000000000000000000000000000 : ℝ)*base63 + (1803092371245097/2000000000000000000000000000 : ℝ)*base65 + (42115966424183/200000000000000000000000000 : ℝ)*base67 + (3350990642772741/5000000000000000000000000000 : ℝ)*base69 + (3614006194770967/10000000000000000000000000000 : ℝ)*base71 + (504171328154903/2000000000000000000000000000 : ℝ)*base73 + (60416622431389/80000000000000000000000000 : ℝ)*base75 + (3273101675772741/5000000000000000000000000000 : ℝ)*base77 + (532746341003267/2000000000000000000000000000 : ℝ)*base78 + (3757/12500000000000000 : ℝ)*base87 + (16257/12500000000000000 : ℝ)*base89 + (3757/12500000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s0_1 : (0 : ℝ) ≤ ((-2261/50000 : ℝ)*X 0 1+(1 : ℝ)*X 0 2+(-2261/50000 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (15323929270380360355929/1000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (202208119499/200000000000 : ℝ)*(base3) + (2897507/500000000000 : ℝ)*(base39) + (150425797883/200000000000 : ℝ)*(base40) + (116103573403/200000000000 : ℝ)*(base49) + (534755812309/200000000000 : ℝ)*(major_s0_0) + (534755812309/200000000000 : ℝ)*(major_s0_1) + (534755812309/200000000000 : ℝ)*(major_s0_2) + (20633419/250000000000 : ℝ)*(sp_s0_6) + (36549213/500000000000 : ℝ)*(sp_s0_9) + (113359554911/31250000000 : ℝ)*(sp_s0_13) + (579818294331/125000000000 : ℝ)*(sp_s0_14) + (1813716329363/500000000000 : ℝ)*(sp_s0_15) + (354445670421/500000000000 : ℝ)*(sp_s0_19) + (16392971/500000000000 : ℝ)*(sp_s0_25) + (344009451591/200000000000 : ℝ)*(f.failure) + (113359554911/31250000000 : ℝ)*(f.sum) + (725235670918643/2000000000000000000000000000 : ℝ)*base62 + (132241997457587/400000000000000000000000000 : ℝ)*base65 + (428395803096711/1000000000000000000000000000 : ℝ)*base66 + (938709870303289/1000000000000000000000000000 : ℝ)*base68 + (950797852281357/2000000000000000000000000000 : ℝ)*base71 + (265995541057587/400000000000000000000000000 : ℝ)*base72 + (162326754942413/400000000000000000000000000 : ℝ)*base74 + (706852648696711/1000000000000000000000000000 : ℝ)*base77 + (749508125081357/2000000000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base83 + (2221/2500000000000000 : ℝ)*base87 + (2221/2500000000000000 : ℝ)*base89 + (2221/2500000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s0_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(35071/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(35071/100000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (7888355547727035191001/1250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2976607202323/1000000000000 : ℝ)*(base3) + (1742354039113/1000000000000 : ℝ)*(base40) + (740690860663/1000000000000 : ℝ)*(base49) + (480532048079/100000000000 : ℝ)*(major_s0_0) + (7886982794387/500000000000 : ℝ)*(major_s0_1) + (480532048079/100000000000 : ℝ)*(major_s0_2) + (9929407/500000000000 : ℝ)*(sp_s0_0) + (685540319249/62500000000 : ℝ)*(sp_s0_4) + (140981551/1000000000000 : ℝ)*(sp_s0_7) + (13533999/500000000000 : ℝ)*(sp_s0_19) + (162980150727/25000000000 : ℝ)*(sp_s0_20) + (1186996758971/125000000000 : ℝ)*(sp_s0_21) + (1629841717361/250000000000 : ℝ)*(sp_s0_22) + (14329714781/125000000000 : ℝ)*(sp_s0_25) + (3091271988569/1000000000000 : ℝ)*(f.failure) + (1629841717361/250000000000 : ℝ)*(f.sum) + (111062659468623/1000000000000000000000000000 : ℝ)*base63 + (115801049234697/200000000000000000000000000 : ℝ)*base65 + (1040588131971473/2500000000000000000000000000 : ℝ)*base66 + (348166840798459/500000000000000000000000000 : ℝ)*base68 + (149501924823433/1000000000000000000000000000 : ℝ)*base70 + (29612710834697/200000000000000000000000000 : ℝ)*base72 + (136955572965541/1000000000000000000000000000 : ℝ)*base75 + (100819879398459/500000000000000000000000000 : ℝ)*base76 + (1713442365810371/5000000000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base81 + (1/1000000000000 : ℝ)*base83 + (9239/12500000000000000 : ℝ)*base87 + (9239/12500000000000000 : ℝ)*base89 + (9239/12500000000000000 : ℝ)*base91 + hcertificate_margin
  have s1_pow0 : (18907/100000 : ℝ) ^ (135/32 : ℝ) ≤ (3550681253243623/4000000000000000000 : ℝ) := by
    have hpowers : (18907/100000 : ℝ)^135 ≤ (3550681253243623/4000000000000000000 : ℝ)^32 := by
      have hnat : (18907 : ℕ)^135*4000000000000000000^32 ≤ 3550681253243623^32*100000^135 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        18907 100000 3550681253243623 4000000000000000000 135 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (18907/100000 : ℝ)) (X := (3550681253243623/4000000000000000000 : ℝ)) (by norm_num) (by norm_num) 135 32 (by norm_num) hpowers
    exact h
  have s1_corner0a : (4003550681253243623/4000000000000000000 : ℝ) ≤ (5001051697633669/5000000000000000 : ℝ) ^ (135/32 : ℝ) := by
    have hpowers : (4003550681253243623/4000000000000000000 : ℝ)^32 ≤ (5001051697633669/5000000000000000 : ℝ)^135 := by
      have hnat : (4003550681253243623 : ℕ)^32*5000000000000000^135 ≤ 5001051697633669^135*4000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4003550681253243623 4000000000000000000 5001051697633669 5000000000000000 32 135 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5001051697633669/5000000000000000 : ℝ)) (X := (4003550681253243623/4000000000000000000 : ℝ)) (by norm_num) 135 32 (by norm_num) hpowers
    exact h
  have s1_corner0b : (2003550681253243623/2000000000000000000 : ℝ) ≤ (625262835483417/625000000000000 : ℝ) ^ (135/32 : ℝ) := by
    have hpowers : (2003550681253243623/2000000000000000000 : ℝ)^32 ≤ (625262835483417/625000000000000 : ℝ)^135 := by
      have hnat : (2003550681253243623 : ℕ)^32*625000000000000^135 ≤ 625262835483417^135*2000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2003550681253243623 2000000000000000000 625262835483417 625000000000000 32 135 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (625262835483417/625000000000000 : ℝ)) (X := (2003550681253243623/2000000000000000000 : ℝ)) (by norm_num) 135 32 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(1051697633669/945350000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(1050986233667/945350000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (135/32 : ℝ)) (rho := (18907/100000 : ℝ)) (alpha := (1051697633669/945350000000000 : ℝ)) (beta := (1050986233667/945350000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, false], ![true, false, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (18907/100000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(1051697633669/945350000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(1050986233667/945350000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (2261/50000 : ℝ) ^ (135/32 : ℝ) ≤ (42482081449983/20000000000000000000 : ℝ) := by
    have hpowers : (2261/50000 : ℝ)^135 ≤ (42482081449983/20000000000000000000 : ℝ)^32 := by
      have hnat : (2261 : ℕ)^135*20000000000000000000^32 ≤ 42482081449983^32*50000^135 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2261 50000 42482081449983 20000000000000000000 135 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2261/50000 : ℝ)) (X := (42482081449983/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 135 32 (by norm_num) hpowers
    exact h
  have s1_corner1a : (20000042482081449983/20000000000000000000 : ℝ) ≤ (5000002517454639/5000000000000000 : ℝ) ^ (135/32 : ℝ) := by
    have hpowers : (20000042482081449983/20000000000000000000 : ℝ)^32 ≤ (5000002517454639/5000000000000000 : ℝ)^135 := by
      have hnat : (20000042482081449983 : ℕ)^32*5000000000000000^135 ≤ 5000002517454639^135*20000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20000042482081449983 20000000000000000000 5000002517454639 5000000000000000 32 135 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000002517454639/5000000000000000 : ℝ)) (X := (20000042482081449983/20000000000000000000 : ℝ)) (by norm_num) 135 32 (by norm_num) hpowers
    exact h
  have s1_corner1b : (10000042482081449983/10000000000000000000 : ℝ) ≤ (2000002013962079/2000000000000000 : ℝ) ^ (135/32 : ℝ) := by
    have hpowers : (10000042482081449983/10000000000000000000 : ℝ)^32 ≤ (2000002013962079/2000000000000000 : ℝ)^135 := by
      have hnat : (10000042482081449983 : ℕ)^32*2000000000000000^135 ≤ 2000002013962079^135*10000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10000042482081449983 10000000000000000000 2000002013962079 2000000000000000 32 135 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000002013962079/2000000000000000 : ℝ)) (X := (10000042482081449983/10000000000000000000 : ℝ)) (by norm_num) 135 32 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1))+(21155081/1900000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2))+(5034901117/452200000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 2 0)) := by
    have hh := chart_majorant (a := (135/32 : ℝ)) (rho := (2261/50000 : ℝ)) (alpha := (21155081/1900000000000 : ℝ)) (beta := (5034901117/452200000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, false], ![true, false, true]] hX 1 (by
        change ((-1 : ℝ)*pair X 1 2) ≤ (2261/50000 : ℝ)*((-1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((-1 : ℝ)*pair X 1 1)+(21155081/1900000000000 : ℝ)*((-1 : ℝ)*pair X 1 2)+(5034901117/452200000000000 : ℝ)*((-1 : ℝ)*pair X 1 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (35071/100000 : ℝ) ^ (135/32 : ℝ) ≤ (1202956726954215867/100000000000000000000 : ℝ) := by
    have hpowers : (35071/100000 : ℝ)^135 ≤ (1202956726954215867/100000000000000000000 : ℝ)^32 := by
      have hnat : (35071 : ℕ)^135*100000000000000000000^32 ≤ 1202956726954215867^32*100000^135 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        35071 100000 1202956726954215867 100000000000000000000 135 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (35071/100000 : ℝ)) (X := (1202956726954215867/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 135 32 (by norm_num) hpowers
    exact h
  have s1_corner2a : (101202956726954215867/100000000000000000000 : ℝ) ≤ (5014192296221069/5000000000000000 : ℝ) ^ (135/32 : ℝ) := by
    have hpowers : (101202956726954215867/100000000000000000000 : ℝ)^32 ≤ (5014192296221069/5000000000000000 : ℝ)^135 := by
      have hnat : (101202956726954215867 : ℕ)^32*5000000000000000^135 ≤ 5014192296221069^135*100000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        101202956726954215867 100000000000000000000 5014192296221069 5000000000000000 32 135 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5014192296221069/5000000000000000 : ℝ)) (X := (101202956726954215867/100000000000000000000 : ℝ)) (by norm_num) 135 32 (by norm_num) hpowers
    exact h
  have s1_corner2b : (51202956726954215867/50000000000000000000 : ℝ) ≤ (10056512919961593/10000000000000000 : ℝ) ^ (135/32 : ℝ) := by
    have hpowers : (51202956726954215867/50000000000000000000 : ℝ)^32 ≤ (10056512919961593/10000000000000000 : ℝ)^135 := by
      have hnat : (51202956726954215867 : ℕ)^32*10000000000000000^135 ≤ 10056512919961593^135*50000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        51202956726954215867 50000000000000000000 10056512919961593 10000000000000000 32 135 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10056512919961593/10000000000000000 : ℝ)) (X := (51202956726954215867/50000000000000000000 : ℝ)) (by norm_num) 135 32 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(14192296221069/1753550000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(5625665503891/701420000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (135/32 : ℝ)) (rho := (35071/100000 : ℝ)) (alpha := (14192296221069/1753550000000000 : ℝ)) (beta := (5625665503891/701420000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, false], ![true, false, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (35071/100000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(14192296221069/1753550000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(5625665503891/701420000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-3356531243/10000000000 : ℝ)*X 0 0+(-5481316403/10000000000 : ℝ)*X 0 1+(4028615519/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c307069_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_1 : ((1047582399/2000000000 : ℝ)*X 1 0+(862099897/2500000000 : ℝ)*X 1 1+(4205958123/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c307069_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((2034793553/5000000000 : ℝ)*X 2 0+(-994566507/2500000000 : ℝ)*X 2 1+(-2442223919/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c307069_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_6 : ((599379291/1250000000 : ℝ)*X 0 0+(-2144258067/5000000000 : ℝ)*X 0 1+(3850334561/10000000000 : ℝ)*X 0 2+(599379291/1250000000 : ℝ)*X 1 0+(-2144258067/5000000000 : ℝ)*X 1 1+(3850334561/10000000000 : ℝ)*X 1 2+(599379291/1250000000 : ℝ)*X 2 0+(-2144258067/5000000000 : ℝ)*X 2 1+(3850334561/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c307069_s1_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have hsep : (-39543/6250 : ℝ) < ((-19431/12500 : ℝ)*P 0+(-19431/12500 : ℝ)*P 1+(-19431/12500 : ℝ)*P 2+(1 : ℝ)*T) := by
    have hcertificate_margin : (-39543/6250 : ℝ) < (-115406623741102018243690470904899/18527441975000000000000000000000 : ℝ) := by norm_num
    linear_combination (63209/250000000000 : ℝ)*(base15) + (279921/1000000000000 : ℝ)*(base22) + (219883/1000000000000 : ℝ)*(base33) + (82453/500000000000 : ℝ)*(base39) + (297884131587/1000000000000 : ℝ)*(base40) + (22517740359/40000000000 : ℝ)*(base49) + (83240063679/250000000000 : ℝ)*(base50) + (54691/1000000000000 : ℝ)*(base59) + (1554479780117/1000000000000 : ℝ)*(major_s1_0) + (19431/12500 : ℝ)*(major_s1_1) + (19431/12500 : ℝ)*(major_s1_2) + (207631871859/100000000000 : ℝ)*(sp_s1_0) + (207631824587/100000000000 : ℝ)*(sp_s1_1) + (1038159109393/500000000000 : ℝ)*(sp_s1_2) + (1 : ℝ)*(sp_s1_6) + (207631871859/100000000000 : ℝ)*(f.sum) + (18377691172677/274379000000000000000000000 : ℝ)*base62 + (937794954151/2063000000000000000000000 : ℝ)*base65 + (677616599/19000000000000000000000 : ℝ)*base66 + (180920428581/412600000000000000000000 : ℝ)*base69 + (1562869262700380399/1950257050000000000000000000000 : ℝ)*base71 + (505492016916311/945350000000000000000000000 : ℝ)*base72 + (77784062757/332500000000000000000000 : ℝ)*base74 + (527676457785553/945350000000000000000000000 : ℝ)*base77 + (8099980073920039/17961650000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base82 + hcertificate_margin
  linarith only [hsep,f.failure]

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
namespace HlawkaSchatten.DiagonalCutoff4
theorem coarse_distinct_p007_b032 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ))
    (c : Fin 88) (hlo : 69 ≤ c.val) (hhi : c.val < 70)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (19431/12500 : ℝ) (92559/50000 : ℝ) (4817/6250 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  have hc : c=69 := by omega
  rcases hc with rfl
  · exact collision_c307069 p hpa (by linarith only [hpb]) X hX

end HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ))
    (c : Fin 88) (hlo : 69 ≤ c.val) (hhi : c.val < 70)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (19431/12500 : ℝ) (92559/50000 : ℝ) (4817/6250 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  exact HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p007_b032 p hpa hpb c hlo hhi hn63 hn87 X hX

#print axioms solution
