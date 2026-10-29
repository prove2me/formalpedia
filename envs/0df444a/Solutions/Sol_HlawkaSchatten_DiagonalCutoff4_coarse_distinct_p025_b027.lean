-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p025_b027
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T02:02:50.548099+00:00
-- url     : https://prove2.me/submissions/68eafb2d-6e35-46b7-877c-9bc61114e6aa

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
theorem collision_support_c325051_s0_0 (p : ℝ) (hpa : (85/16 : ℝ) ≤ p) (hpb : p ≤ (87/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-81318779/250000000 : ℝ)*x 0 + (1626375419/5000000000 : ℝ)*x 1 + (28162943/50000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (81318779/250000000 : ℝ)^87 ≤ (25254311725021/100000000000000 : ℝ)^71 := by
    have hnat : (81318779 : ℕ)^87*100000000000000^71 ≤ 25254311725021^71*250000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      81318779 250000000 25254311725021 100000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1626375419/5000000000 : ℝ)^87 ≤ (25254308661637/100000000000000 : ℝ)^71 := by
    have hnat : (1626375419 : ℕ)^87*100000000000000^71 ≤ 25254308661637^71*5000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1626375419 5000000000 25254308661637 100000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (28162943/50000000 : ℝ)^87 ≤ (24745689798677/50000000000000 : ℝ)^71 := by
    have hnat : (28162943 : ℕ)^87*50000000000000^71 ≤ 24745689798677^71*50000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      28162943 50000000 24745689798677 50000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (87/16 : ℝ)) 87 71 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-81318779/250000000 : ℝ), (1626375419/5000000000 : ℝ), (28162943/50000000 : ℝ)] ![(25254311725021/100000000000000 : ℝ), (25254308661637/100000000000000 : ℝ), (24745689798677/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-81318779/250000000 : ℝ)|^87 ≤ (25254311725021/100000000000000 : ℝ)^71
        have hw : |(-81318779/250000000 : ℝ)|=(81318779/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1626375419/5000000000 : ℝ)|^87 ≤ (25254308661637/100000000000000 : ℝ)^71
        have hw : |(1626375419/5000000000 : ℝ)|=(1626375419/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(28162943/50000000 : ℝ)|^87 ≤ (24745689798677/50000000000000 : ℝ)^71
        have hw : |(28162943/50000000 : ℝ)|=(28162943/50000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c325051_s0_1 (p : ℝ) (hpa : (85/16 : ℝ) ≤ p) (hpb : p ≤ (87/16 : ℝ)) (x : Fin 3 → ℝ) :
    (296711547/1250000000 : ℝ)*x 0 + (-237369211/1000000000 : ℝ)*x 1 + (7094820153/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (296711547/1250000000 : ℝ)^87 ≤ (17166233347707/100000000000000 : ℝ)^71 := by
    have hnat : (296711547 : ℕ)^87*100000000000000^71 ≤ 17166233347707^71*1250000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      296711547 1250000000 17166233347707 100000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (237369211/1000000000 : ℝ)^87 ≤ (686649239621/4000000000000 : ℝ)^71 := by
    have hnat : (237369211 : ℕ)^87*4000000000000^71 ≤ 686649239621^71*1000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      237369211 1000000000 686649239621 4000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (7094820153/10000000000 : ℝ)^87 ≤ (65667535648623/100000000000000 : ℝ)^71 := by
    have hnat : (7094820153 : ℕ)^87*100000000000000^71 ≤ 65667535648623^71*10000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7094820153 10000000000 65667535648623 100000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (87/16 : ℝ)) 87 71 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(296711547/1250000000 : ℝ), (-237369211/1000000000 : ℝ), (7094820153/10000000000 : ℝ)] ![(17166233347707/100000000000000 : ℝ), (686649239621/4000000000000 : ℝ), (65667535648623/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(296711547/1250000000 : ℝ)|^87 ≤ (17166233347707/100000000000000 : ℝ)^71
        have hw : |(296711547/1250000000 : ℝ)|=(296711547/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-237369211/1000000000 : ℝ)|^87 ≤ (686649239621/4000000000000 : ℝ)^71
        have hw : |(-237369211/1000000000 : ℝ)|=(237369211/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(7094820153/10000000000 : ℝ)|^87 ≤ (65667535648623/100000000000000 : ℝ)^71
        have hw : |(7094820153/10000000000 : ℝ)|=(7094820153/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c325051_s0_7 (p : ℝ) (hpa : (85/16 : ℝ) ≤ p) (hpb : p ≤ (87/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-68172631/250000000 : ℝ)*x 0 + (821341433/5000000000 : ℝ)*x 1 + (1840690499/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (68172631/250000000 : ℝ)^87 ≤ (2034684605401/10000000000000 : ℝ)^71 := by
    have hnat : (68172631 : ℕ)^87*10000000000000^71 ≤ 2034684605401^71*250000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      68172631 250000000 2034684605401 10000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (821341433/5000000000 : ℝ)^87 ≤ (5466975237217/50000000000000 : ℝ)^71 := by
    have hnat : (821341433 : ℕ)^87*50000000000000^71 ≤ 5466975237217^71*5000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      821341433 5000000000 5466975237217 50000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1840690499/2500000000 : ℝ)^87 ≤ (68719203450423/100000000000000 : ℝ)^71 := by
    have hnat : (1840690499 : ℕ)^87*100000000000000^71 ≤ 68719203450423^71*2500000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1840690499 2500000000 68719203450423 100000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (87/16 : ℝ)) 87 71 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-68172631/250000000 : ℝ), (821341433/5000000000 : ℝ), (1840690499/2500000000 : ℝ)] ![(2034684605401/10000000000000 : ℝ), (5466975237217/50000000000000 : ℝ), (68719203450423/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-68172631/250000000 : ℝ)|^87 ≤ (2034684605401/10000000000000 : ℝ)^71
        have hw : |(-68172631/250000000 : ℝ)|=(68172631/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(821341433/5000000000 : ℝ)|^87 ≤ (5466975237217/50000000000000 : ℝ)^71
        have hw : |(821341433/5000000000 : ℝ)|=(821341433/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1840690499/2500000000 : ℝ)|^87 ≤ (68719203450423/100000000000000 : ℝ)^71
        have hw : |(1840690499/2500000000 : ℝ)|=(1840690499/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c325051_s0_8 (p : ℝ) (hpa : (85/16 : ℝ) ≤ p) (hpb : p ≤ (87/16 : ℝ)) (x : Fin 3 → ℝ) :
    (353818477/2500000000 : ℝ)*x 0 + (-769156451/10000000000 : ℝ)*x 1 + (4445084037/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (353818477/2500000000 : ℝ)^87 ≤ (910920787201/10000000000000 : ℝ)^71 := by
    have hnat : (353818477 : ℕ)^87*10000000000000^71 ≤ 910920787201^71*2500000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      353818477 2500000000 910920787201 10000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (769156451/10000000000 : ℝ)^87 ≤ (4314949755827/100000000000000 : ℝ)^71 := by
    have hnat : (769156451 : ℕ)^87*100000000000000^71 ≤ 4314949755827^71*10000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      769156451 10000000000 4314949755827 100000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4445084037/5000000000 : ℝ)^87 ≤ (86575842361851/100000000000000 : ℝ)^71 := by
    have hnat : (4445084037 : ℕ)^87*100000000000000^71 ≤ 86575842361851^71*5000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4445084037 5000000000 86575842361851 100000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (87/16 : ℝ)) 87 71 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(353818477/2500000000 : ℝ), (-769156451/10000000000 : ℝ), (4445084037/5000000000 : ℝ)] ![(910920787201/10000000000000 : ℝ), (4314949755827/100000000000000 : ℝ), (86575842361851/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(353818477/2500000000 : ℝ)|^87 ≤ (910920787201/10000000000000 : ℝ)^71
        have hw : |(353818477/2500000000 : ℝ)|=(353818477/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-769156451/10000000000 : ℝ)|^87 ≤ (4314949755827/100000000000000 : ℝ)^71
        have hw : |(-769156451/10000000000 : ℝ)|=(769156451/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4445084037/5000000000 : ℝ)|^87 ≤ (86575842361851/100000000000000 : ℝ)^71
        have hw : |(4445084037/5000000000 : ℝ)|=(4445084037/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c325051_s0_9 (p : ℝ) (hpa : (85/16 : ℝ) ≤ p) (hpb : p ≤ (87/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1018980649/2500000000 : ℝ)*x 0 + (13910897/19531250 : ℝ)*x 1 + (-179197089/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1018980649/2500000000 : ℝ)^87 ≤ (16647902420469/50000000000000 : ℝ)^71 := by
    have hnat : (1018980649 : ℕ)^87*50000000000000^71 ≤ 16647902420469^71*2500000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1018980649 2500000000 16647902420469 50000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (13910897/19531250 : ℝ)^87 ≤ (13196046755871/20000000000000 : ℝ)^71 := by
    have hnat : (13910897 : ℕ)^87*20000000000000^71 ≤ 13196046755871^71*19531250^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      13910897 19531250 13196046755871 20000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (179197089/10000000000 : ℝ)^87 ≤ (723961364543/100000000000000 : ℝ)^71 := by
    have hnat : (179197089 : ℕ)^87*100000000000000^71 ≤ 723961364543^71*10000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      179197089 10000000000 723961364543 100000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (87/16 : ℝ)) 87 71 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1018980649/2500000000 : ℝ), (13910897/19531250 : ℝ), (-179197089/10000000000 : ℝ)] ![(16647902420469/50000000000000 : ℝ), (13196046755871/20000000000000 : ℝ), (723961364543/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1018980649/2500000000 : ℝ)|^87 ≤ (16647902420469/50000000000000 : ℝ)^71
        have hw : |(1018980649/2500000000 : ℝ)|=(1018980649/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(13910897/19531250 : ℝ)|^87 ≤ (13196046755871/20000000000000 : ℝ)^71
        have hw : |(13910897/19531250 : ℝ)|=(13910897/19531250 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-179197089/10000000000 : ℝ)|^87 ≤ (723961364543/100000000000000 : ℝ)^71
        have hw : |(-179197089/10000000000 : ℝ)|=(179197089/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c325051_s0_13 (p : ℝ) (hpa : (85/16 : ℝ) ≤ p) (hpb : p ≤ (87/16 : ℝ)) (x : Fin 3 → ℝ) :
    (276992761/1000000000 : ℝ)*x 0 + (1026513749/1250000000 : ℝ)*x 1 + (2735329/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (276992761/1000000000 : ℝ)^87 ≤ (20740895322027/100000000000000 : ℝ)^71 := by
    have hnat : (276992761 : ℕ)^87*100000000000000^71 ≤ 20740895322027^71*1000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      276992761 1000000000 20740895322027 100000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1026513749/1250000000 : ℝ)^87 ≤ (78555564991867/100000000000000 : ℝ)^71 := by
    have hnat : (1026513749 : ℕ)^87*100000000000000^71 ≤ 78555564991867^71*1250000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1026513749 1250000000 78555564991867 100000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2735329/156250000 : ℝ)^87 ≤ (703539678593/100000000000000 : ℝ)^71 := by
    have hnat : (2735329 : ℕ)^87*100000000000000^71 ≤ 703539678593^71*156250000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2735329 156250000 703539678593 100000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (87/16 : ℝ)) 87 71 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(276992761/1000000000 : ℝ), (1026513749/1250000000 : ℝ), (2735329/156250000 : ℝ)] ![(20740895322027/100000000000000 : ℝ), (78555564991867/100000000000000 : ℝ), (703539678593/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(276992761/1000000000 : ℝ)|^87 ≤ (20740895322027/100000000000000 : ℝ)^71
        have hw : |(276992761/1000000000 : ℝ)|=(276992761/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1026513749/1250000000 : ℝ)|^87 ≤ (78555564991867/100000000000000 : ℝ)^71
        have hw : |(1026513749/1250000000 : ℝ)|=(1026513749/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2735329/156250000 : ℝ)|^87 ≤ (703539678593/100000000000000 : ℝ)^71
        have hw : |(2735329/156250000 : ℝ)|=(2735329/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c325051_s0_14 (p : ℝ) (hpa : (85/16 : ℝ) ≤ p) (hpb : p ≤ (87/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-1776711687/10000000000 : ℝ)*x 0 + (2782449343/10000000000 : ℝ)*x 1 + (7221504509/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1776711687/10000000000 : ℝ)^87 ≤ (2407390548677/20000000000000 : ℝ)^71 := by
    have hnat : (1776711687 : ℕ)^87*20000000000000^71 ≤ 2407390548677^71*10000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1776711687 10000000000 2407390548677 20000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2782449343/10000000000 : ℝ)^87 ≤ (20855844355303/100000000000000 : ℝ)^71 := by
    have hnat : (2782449343 : ℕ)^87*100000000000000^71 ≤ 20855844355303^71*10000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2782449343 10000000000 20855844355303 100000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (7221504509/10000000000 : ℝ)^87 ≤ (67107202892467/100000000000000 : ℝ)^71 := by
    have hnat : (7221504509 : ℕ)^87*100000000000000^71 ≤ 67107202892467^71*10000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7221504509 10000000000 67107202892467 100000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (87/16 : ℝ)) 87 71 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1776711687/10000000000 : ℝ), (2782449343/10000000000 : ℝ), (7221504509/10000000000 : ℝ)] ![(2407390548677/20000000000000 : ℝ), (20855844355303/100000000000000 : ℝ), (67107202892467/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1776711687/10000000000 : ℝ)|^87 ≤ (2407390548677/20000000000000 : ℝ)^71
        have hw : |(-1776711687/10000000000 : ℝ)|=(1776711687/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2782449343/10000000000 : ℝ)|^87 ≤ (20855844355303/100000000000000 : ℝ)^71
        have hw : |(2782449343/10000000000 : ℝ)|=(2782449343/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(7221504509/10000000000 : ℝ)|^87 ≤ (67107202892467/100000000000000 : ℝ)^71
        have hw : |(7221504509/10000000000 : ℝ)|=(7221504509/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c325051_s0_15 (p : ℝ) (hpa : (85/16 : ℝ) ≤ p) (hpb : p ≤ (87/16 : ℝ)) (x : Fin 3 → ℝ) :
    (490131759/5000000000 : ℝ)*x 0 + (-307861953/2000000000 : ℝ)*x 1 + (1736341721/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (490131759/5000000000 : ℝ)^87 ≤ (1452044167529/25000000000000 : ℝ)^71 := by
    have hnat : (490131759 : ℕ)^87*25000000000000^71 ≤ 1452044167529^71*5000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      490131759 5000000000 1452044167529 25000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (307861953/2000000000 : ℝ)^87 ≤ (2524226000379/25000000000000 : ℝ)^71 := by
    have hnat : (307861953 : ℕ)^87*25000000000000^71 ≤ 2524226000379^71*2000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      307861953 2000000000 2524226000379 25000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1736341721/2000000000 : ℝ)^87 ≤ (16818983862747/20000000000000 : ℝ)^71 := by
    have hnat : (1736341721 : ℕ)^87*20000000000000^71 ≤ 16818983862747^71*2000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1736341721 2000000000 16818983862747 20000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (87/16 : ℝ)) 87 71 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(490131759/5000000000 : ℝ), (-307861953/2000000000 : ℝ), (1736341721/2000000000 : ℝ)] ![(1452044167529/25000000000000 : ℝ), (2524226000379/25000000000000 : ℝ), (16818983862747/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(490131759/5000000000 : ℝ)|^87 ≤ (1452044167529/25000000000000 : ℝ)^71
        have hw : |(490131759/5000000000 : ℝ)|=(490131759/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-307861953/2000000000 : ℝ)|^87 ≤ (2524226000379/25000000000000 : ℝ)^71
        have hw : |(-307861953/2000000000 : ℝ)|=(307861953/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1736341721/2000000000 : ℝ)|^87 ≤ (16818983862747/20000000000000 : ℝ)^71
        have hw : |(1736341721/2000000000 : ℝ)|=(1736341721/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c325051_s0_16 (p : ℝ) (hpa : (85/16 : ℝ) ≤ p) (hpb : p ≤ (87/16 : ℝ)) (x : Fin 3 → ℝ) :
    (938639131/1250000000 : ℝ)*x 0 + (182986647/500000000 : ℝ)*x 1 + (-23169563/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (938639131/1250000000 : ℝ)^87 ≤ (70396696634321/100000000000000 : ℝ)^71 := by
    have hnat : (938639131 : ℕ)^87*100000000000000^71 ≤ 70396696634321^71*1250000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      938639131 1250000000 70396696634321 100000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (182986647/500000000 : ℝ)^87 ≤ (5835818675893/20000000000000 : ℝ)^71 := by
    have hnat : (182986647 : ℕ)^87*20000000000000^71 ≤ 5835818675893^71*500000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      182986647 500000000 5835818675893 20000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (23169563/2000000000 : ℝ)^87 ≤ (212104990679/50000000000000 : ℝ)^71 := by
    have hnat : (23169563 : ℕ)^87*50000000000000^71 ≤ 212104990679^71*2000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      23169563 2000000000 212104990679 50000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (87/16 : ℝ)) 87 71 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(938639131/1250000000 : ℝ), (182986647/500000000 : ℝ), (-23169563/2000000000 : ℝ)] ![(70396696634321/100000000000000 : ℝ), (5835818675893/20000000000000 : ℝ), (212104990679/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(938639131/1250000000 : ℝ)|^87 ≤ (70396696634321/100000000000000 : ℝ)^71
        have hw : |(938639131/1250000000 : ℝ)|=(938639131/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(182986647/500000000 : ℝ)|^87 ≤ (5835818675893/20000000000000 : ℝ)^71
        have hw : |(182986647/500000000 : ℝ)|=(182986647/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-23169563/2000000000 : ℝ)|^87 ≤ (212104990679/50000000000000 : ℝ)^71
        have hw : |(-23169563/2000000000 : ℝ)|=(23169563/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c325051_s0_20 (p : ℝ) (hpa : (85/16 : ℝ) ≤ p) (hpb : p ≤ (87/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3725761189/5000000000 : ℝ)*x 0 + (3692950633/10000000000 : ℝ)*x 1 + (46628527/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3725761189/5000000000 : ℝ)^87 ≤ (69735698150519/100000000000000 : ℝ)^71 := by
    have hnat : (3725761189 : ℕ)^87*100000000000000^71 ≤ 69735698150519^71*5000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3725761189 5000000000 69735698150519 100000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3692950633/10000000000 : ℝ)^87 ≤ (14751976474149/50000000000000 : ℝ)^71 := by
    have hnat : (3692950633 : ℕ)^87*50000000000000^71 ≤ 14751976474149^71*10000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3692950633 10000000000 14751976474149 50000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (46628527/2500000000 : ℝ)^87 ≤ (760348884209/100000000000000 : ℝ)^71 := by
    have hnat : (46628527 : ℕ)^87*100000000000000^71 ≤ 760348884209^71*2500000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      46628527 2500000000 760348884209 100000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (87/16 : ℝ)) 87 71 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3725761189/5000000000 : ℝ), (3692950633/10000000000 : ℝ), (46628527/2500000000 : ℝ)] ![(69735698150519/100000000000000 : ℝ), (14751976474149/50000000000000 : ℝ), (760348884209/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3725761189/5000000000 : ℝ)|^87 ≤ (69735698150519/100000000000000 : ℝ)^71
        have hw : |(3725761189/5000000000 : ℝ)|=(3725761189/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3692950633/10000000000 : ℝ)|^87 ≤ (14751976474149/50000000000000 : ℝ)^71
        have hw : |(3692950633/10000000000 : ℝ)|=(3692950633/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(46628527/2500000000 : ℝ)|^87 ≤ (760348884209/100000000000000 : ℝ)^71
        have hw : |(46628527/2500000000 : ℝ)|=(46628527/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c325051_s0_21 (p : ℝ) (hpa : (85/16 : ℝ) ≤ p) (hpb : p ≤ (87/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-2465951249/5000000000 : ℝ)*x 0 + (259797567/625000000 : ℝ)*x 1 + (1551471143/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2465951249/5000000000 : ℝ)^87 ≤ (5257080897963/12500000000000 : ℝ)^71 := by
    have hnat : (2465951249 : ℕ)^87*12500000000000^71 ≤ 5257080897963^71*5000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2465951249 5000000000 5257080897963 12500000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (259797567/625000000 : ℝ)^87 ≤ (34106779231397/100000000000000 : ℝ)^71 := by
    have hnat : (259797567 : ℕ)^87*100000000000000^71 ≤ 34106779231397^71*625000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      259797567 625000000 34106779231397 100000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1551471143/5000000000 : ℝ)^87 ≤ (5959143390443/25000000000000 : ℝ)^71 := by
    have hnat : (1551471143 : ℕ)^87*25000000000000^71 ≤ 5959143390443^71*5000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1551471143 5000000000 5959143390443 25000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (87/16 : ℝ)) 87 71 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2465951249/5000000000 : ℝ), (259797567/625000000 : ℝ), (1551471143/5000000000 : ℝ)] ![(5257080897963/12500000000000 : ℝ), (34106779231397/100000000000000 : ℝ), (5959143390443/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2465951249/5000000000 : ℝ)|^87 ≤ (5257080897963/12500000000000 : ℝ)^71
        have hw : |(-2465951249/5000000000 : ℝ)|=(2465951249/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(259797567/625000000 : ℝ)|^87 ≤ (34106779231397/100000000000000 : ℝ)^71
        have hw : |(259797567/625000000 : ℝ)|=(259797567/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1551471143/5000000000 : ℝ)|^87 ≤ (5959143390443/25000000000000 : ℝ)^71
        have hw : |(1551471143/5000000000 : ℝ)|=(1551471143/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c325051_s0_22 (p : ℝ) (hpa : (85/16 : ℝ) ≤ p) (hpb : p ≤ (87/16 : ℝ)) (x : Fin 3 → ℝ) :
    (971954939/10000000000 : ℝ)*x 0 + (-349420241/2000000000 : ℝ)*x 1 + (8543758131/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (971954939/10000000000 : ℝ)^87 ≤ (2873955585173/50000000000000 : ℝ)^71 := by
    have hnat : (971954939 : ℕ)^87*50000000000000^71 ≤ 2873955585173^71*10000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      971954939 10000000000 2873955585173 50000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (349420241/2000000000 : ℝ)^87 ≤ (1473950338173/12500000000000 : ℝ)^71 := by
    have hnat : (349420241 : ℕ)^87*12500000000000^71 ≤ 1473950338173^71*2000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      349420241 2000000000 1473950338173 12500000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (8543758131/10000000000 : ℝ)^87 ≤ (1649209722051/2000000000000 : ℝ)^71 := by
    have hnat : (8543758131 : ℕ)^87*2000000000000^71 ≤ 1649209722051^71*10000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8543758131 10000000000 1649209722051 2000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (87/16 : ℝ)) 87 71 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(971954939/10000000000 : ℝ), (-349420241/2000000000 : ℝ), (8543758131/10000000000 : ℝ)] ![(2873955585173/50000000000000 : ℝ), (1473950338173/12500000000000 : ℝ), (1649209722051/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(971954939/10000000000 : ℝ)|^87 ≤ (2873955585173/50000000000000 : ℝ)^71
        have hw : |(971954939/10000000000 : ℝ)|=(971954939/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-349420241/2000000000 : ℝ)|^87 ≤ (1473950338173/12500000000000 : ℝ)^71
        have hw : |(-349420241/2000000000 : ℝ)|=(349420241/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(8543758131/10000000000 : ℝ)|^87 ≤ (1649209722051/2000000000000 : ℝ)^71
        have hw : |(8543758131/10000000000 : ℝ)|=(8543758131/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c325051_s0_23 (p : ℝ) (hpa : (85/16 : ℝ) ≤ p) (hpb : p ≤ (87/16 : ℝ)) (x : Fin 3 → ℝ) :
    (6782544291/10000000000 : ℝ)*x 0 + (2246462469/5000000000 : ℝ)*x 1 + (-19321199/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6782544291/10000000000 : ℝ)^87 ≤ (62143629310059/100000000000000 : ℝ)^71 := by
    have hnat : (6782544291 : ℕ)^87*100000000000000^71 ≤ 62143629310059^71*10000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6782544291 10000000000 62143629310059 100000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2246462469/5000000000 : ℝ)^87 ≤ (37516807578463/100000000000000 : ℝ)^71 := by
    have hnat : (2246462469 : ℕ)^87*100000000000000^71 ≤ 37516807578463^71*5000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2246462469 5000000000 37516807578463 100000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (19321199/2000000000 : ℝ)^87 ≤ (67912620011/20000000000000 : ℝ)^71 := by
    have hnat : (19321199 : ℕ)^87*20000000000000^71 ≤ 67912620011^71*2000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      19321199 2000000000 67912620011 20000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (87/16 : ℝ)) 87 71 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6782544291/10000000000 : ℝ), (2246462469/5000000000 : ℝ), (-19321199/2000000000 : ℝ)] ![(62143629310059/100000000000000 : ℝ), (37516807578463/100000000000000 : ℝ), (67912620011/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6782544291/10000000000 : ℝ)|^87 ≤ (62143629310059/100000000000000 : ℝ)^71
        have hw : |(6782544291/10000000000 : ℝ)|=(6782544291/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2246462469/5000000000 : ℝ)|^87 ≤ (37516807578463/100000000000000 : ℝ)^71
        have hw : |(2246462469/5000000000 : ℝ)|=(2246462469/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-19321199/2000000000 : ℝ)|^87 ≤ (67912620011/20000000000000 : ℝ)^71
        have hw : |(-19321199/2000000000 : ℝ)|=(19321199/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c325051_s0_27 (p : ℝ) (hpa : (85/16 : ℝ) ≤ p) (hpb : p ≤ (87/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1301899589/5000000000 : ℝ)*x 0 + (8372588953/10000000000 : ℝ)*x 1 + (94887693/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1301899589/5000000000 : ℝ)^87 ≤ (19227082854679/100000000000000 : ℝ)^71 := by
    have hnat : (1301899589 : ℕ)^87*100000000000000^71 ≤ 19227082854679^71*5000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1301899589 5000000000 19227082854679 100000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (8372588953/10000000000 : ℝ)^87 ≤ (40220369947097/50000000000000 : ℝ)^71 := by
    have hnat : (8372588953 : ℕ)^87*50000000000000^71 ≤ 40220369947097^71*10000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8372588953 10000000000 40220369947097 50000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (94887693/10000000000 : ℝ)^87 ≤ (166088616249/50000000000000 : ℝ)^71 := by
    have hnat : (94887693 : ℕ)^87*50000000000000^71 ≤ 166088616249^71*10000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      94887693 10000000000 166088616249 50000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (87/16 : ℝ)) 87 71 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1301899589/5000000000 : ℝ), (8372588953/10000000000 : ℝ), (94887693/10000000000 : ℝ)] ![(19227082854679/100000000000000 : ℝ), (40220369947097/50000000000000 : ℝ), (166088616249/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1301899589/5000000000 : ℝ)|^87 ≤ (19227082854679/100000000000000 : ℝ)^71
        have hw : |(1301899589/5000000000 : ℝ)|=(1301899589/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(8372588953/10000000000 : ℝ)|^87 ≤ (40220369947097/50000000000000 : ℝ)^71
        have hw : |(8372588953/10000000000 : ℝ)|=(8372588953/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(94887693/10000000000 : ℝ)|^87 ≤ (166088616249/50000000000000 : ℝ)^71
        have hw : |(94887693/10000000000 : ℝ)|=(94887693/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c325051_s1_0 (p : ℝ) (hpa : (85/16 : ℝ) ≤ p) (hpb : p ≤ (87/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-896960491/2500000000 : ℝ)*x 0 + (895972289/2500000000 : ℝ)*x 1 + (1005959483/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (896960491/2500000000 : ℝ)^87 ≤ (28478299295051/100000000000000 : ℝ)^71 := by
    have hnat : (896960491 : ℕ)^87*100000000000000^71 ≤ 28478299295051^71*2500000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      896960491 2500000000 28478299295051 100000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (895972289/2500000000 : ℝ)^87 ≤ (7109964601187/25000000000000 : ℝ)^71 := by
    have hnat : (895972289 : ℕ)^87*25000000000000^71 ≤ 7109964601187^71*2500000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      895972289 2500000000 7109964601187 25000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1005959483/2000000000 : ℝ)^87 ≤ (43081842282229/100000000000000 : ℝ)^71 := by
    have hnat : (1005959483 : ℕ)^87*100000000000000^71 ≤ 43081842282229^71*2000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1005959483 2000000000 43081842282229 100000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (87/16 : ℝ)) 87 71 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-896960491/2500000000 : ℝ), (895972289/2500000000 : ℝ), (1005959483/2000000000 : ℝ)] ![(28478299295051/100000000000000 : ℝ), (7109964601187/25000000000000 : ℝ), (43081842282229/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-896960491/2500000000 : ℝ)|^87 ≤ (28478299295051/100000000000000 : ℝ)^71
        have hw : |(-896960491/2500000000 : ℝ)|=(896960491/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(895972289/2500000000 : ℝ)|^87 ≤ (7109964601187/25000000000000 : ℝ)^71
        have hw : |(895972289/2500000000 : ℝ)|=(895972289/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1005959483/2000000000 : ℝ)|^87 ≤ (43081842282229/100000000000000 : ℝ)^71
        have hw : |(1005959483/2000000000 : ℝ)|=(1005959483/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c325051_s1_1 (p : ℝ) (hpa : (85/16 : ℝ) ≤ p) (hpb : p ≤ (87/16 : ℝ)) (x : Fin 3 → ℝ) :
    (738825037/2500000000 : ℝ)*x 0 + (-1476022113/5000000000 : ℝ)*x 1 + (6150279277/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (738825037/2500000000 : ℝ)^87 ≤ (22454353043107/100000000000000 : ℝ)^71 := by
    have hnat : (738825037 : ℕ)^87*100000000000000^71 ≤ 22454353043107^71*2500000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      738825037 2500000000 22454353043107 100000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1476022113/5000000000 : ℝ)^87 ≤ (22424043463261/100000000000000 : ℝ)^71 := by
    have hnat : (1476022113 : ℕ)^87*100000000000000^71 ≤ 22424043463261^71*5000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1476022113 5000000000 22424043463261 100000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6150279277/10000000000 : ℝ)^87 ≤ (13780400866981/25000000000000 : ℝ)^71 := by
    have hnat : (6150279277 : ℕ)^87*25000000000000^71 ≤ 13780400866981^71*10000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6150279277 10000000000 13780400866981 25000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (87/16 : ℝ)) 87 71 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(738825037/2500000000 : ℝ), (-1476022113/5000000000 : ℝ), (6150279277/10000000000 : ℝ)] ![(22454353043107/100000000000000 : ℝ), (22424043463261/100000000000000 : ℝ), (13780400866981/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(738825037/2500000000 : ℝ)|^87 ≤ (22454353043107/100000000000000 : ℝ)^71
        have hw : |(738825037/2500000000 : ℝ)|=(738825037/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1476022113/5000000000 : ℝ)|^87 ≤ (22424043463261/100000000000000 : ℝ)^71
        have hw : |(-1476022113/5000000000 : ℝ)|=(1476022113/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6150279277/10000000000 : ℝ)|^87 ≤ (13780400866981/25000000000000 : ℝ)^71
        have hw : |(6150279277/10000000000 : ℝ)|=(6150279277/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c325051_s1_2 (p : ℝ) (hpa : (85/16 : ℝ) ≤ p) (hpb : p ≤ (87/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2606472669/5000000000 : ℝ)*x 0 + (2609207727/5000000000 : ℝ)*x 1 + (-758528141/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2606472669/5000000000 : ℝ)^87 ≤ (9002378352877/20000000000000 : ℝ)^71 := by
    have hnat : (2606472669 : ℕ)^87*20000000000000^71 ≤ 9002378352877^71*5000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2606472669 5000000000 9002378352877 20000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2609207727/5000000000 : ℝ)^87 ≤ (45069775008917/100000000000000 : ℝ)^71 := by
    have hnat : (2609207727 : ℕ)^87*100000000000000^71 ≤ 45069775008917^71*5000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2609207727 5000000000 45069775008917 100000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (758528141/5000000000 : ℝ)^87 ≤ (396733328387/4000000000000 : ℝ)^71 := by
    have hnat : (758528141 : ℕ)^87*4000000000000^71 ≤ 396733328387^71*5000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      758528141 5000000000 396733328387 4000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (87/16 : ℝ)) 87 71 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2606472669/5000000000 : ℝ), (2609207727/5000000000 : ℝ), (-758528141/5000000000 : ℝ)] ![(9002378352877/20000000000000 : ℝ), (45069775008917/100000000000000 : ℝ), (396733328387/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2606472669/5000000000 : ℝ)|^87 ≤ (9002378352877/20000000000000 : ℝ)^71
        have hw : |(2606472669/5000000000 : ℝ)|=(2606472669/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2609207727/5000000000 : ℝ)|^87 ≤ (45069775008917/100000000000000 : ℝ)^71
        have hw : |(2609207727/5000000000 : ℝ)|=(2609207727/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-758528141/5000000000 : ℝ)|^87 ≤ (396733328387/4000000000000 : ℝ)^71
        have hw : |(-758528141/5000000000 : ℝ)|=(758528141/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c325051_s1_6 (p : ℝ) (hpa : (85/16 : ℝ) ≤ p) (hpb : p ≤ (87/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4964121797/10000000000 : ℝ)*x 0 + (993866163/2000000000 : ℝ)*x 1 + (268069261/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4964121797/10000000000 : ℝ)^87 ≤ (10598389738307/25000000000000 : ℝ)^71 := by
    have hnat : (4964121797 : ℕ)^87*25000000000000^71 ≤ 10598389738307^71*10000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4964121797 10000000000 10598389738307 25000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (993866163/2000000000 : ℝ)^87 ≤ (42448075149007/100000000000000 : ℝ)^71 := by
    have hnat : (993866163 : ℕ)^87*100000000000000^71 ≤ 42448075149007^71*2000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      993866163 2000000000 42448075149007 100000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (268069261/1250000000 : ℝ)^87 ≤ (15158365873199/100000000000000 : ℝ)^71 := by
    have hnat : (268069261 : ℕ)^87*100000000000000^71 ≤ 15158365873199^71*1250000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      268069261 1250000000 15158365873199 100000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (87/16 : ℝ)) 87 71 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4964121797/10000000000 : ℝ), (993866163/2000000000 : ℝ), (268069261/1250000000 : ℝ)] ![(10598389738307/25000000000000 : ℝ), (42448075149007/100000000000000 : ℝ), (15158365873199/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4964121797/10000000000 : ℝ)|^87 ≤ (10598389738307/25000000000000 : ℝ)^71
        have hw : |(4964121797/10000000000 : ℝ)|=(4964121797/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(993866163/2000000000 : ℝ)|^87 ≤ (42448075149007/100000000000000 : ℝ)^71
        have hw : |(993866163/2000000000 : ℝ)|=(993866163/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(268069261/1250000000 : ℝ)|^87 ≤ (15158365873199/100000000000000 : ℝ)^71
        have hw : |(268069261/1250000000 : ℝ)|=(268069261/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c325051 (p : ℝ) (hpa : (85/16 : ℝ) ≤ p) (hpb : p ≤ (87/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (200939/100000 : ℝ) (33069/20000 : ℝ) (81317/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![false, true, true]]) : False := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (81317/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (81317/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (81317/100000 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (81317/100000 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 2+X 2 2)) ∧ ((-1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 2) ∧ ((-1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (81317/100000 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (81317/100000 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((-1 : ℝ)*(X 0 0+X 1 0)) ∧ ((-1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((-1 : ℝ)*pair X 2 0) ∧ ((-1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base5 : ((1 : ℝ)*N 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 2]
  have base7 : ((1 : ℝ)*T) ≤ (33069/20000 : ℝ) := by
    linarith only [f.Tcap]
  have base8 : ((-1 : ℝ)*X 0 0+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 0).1]
  have base11 : ((1 : ℝ)*X 0 1+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 1).2]
  have base15 : ((1 : ℝ)*X 1 0+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 0).2]
  have base19 : ((1 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 2).2]
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base43 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 2+(1 : ℝ)*P 1) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 1,f.sum]
  have base44 : ((-1 : ℝ)*N 1+(1 : ℝ)*P 1+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ptotal 1]
  have base49 : ((1 : ℝ)*X 0 2+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.1]
  have base50 : ((-1 : ℝ)*X 0 0+(-1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 0+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.2.1]
  have base59 : ((-1 : ℝ)*X 0 1+(-1 : ℝ)*X 1 1) ≤ (0 : ℝ) := by
    linarith only [order2.1]
  have base60 : ((1 : ℝ)*X 0 0+(1 : ℝ)*X 0 1+(1 : ℝ)*X 1 0+(1 : ℝ)*X 1 1) ≤ (0 : ℝ) := by
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
  have s0_pow0 : (1 : ℝ) ^ (85/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^85 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^85*1^16 ≤ 1^16*1^85 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 85 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 85 16 (by norm_num) hpowers
    exact h
  have s0_corner0a : (2 : ℝ) ≤ (11393691857257931/10000000000000000 : ℝ) ^ (85/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (11393691857257931/10000000000000000 : ℝ)^85 := by
      have hnat : (2 : ℕ)^16*10000000000000000^85 ≤ 11393691857257931^85*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 11393691857257931 10000000000000000 16 85 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11393691857257931/10000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 85 16 (by norm_num) hpowers
    exact h
  have s0_corner0b : (3 : ℝ) ≤ (6148668287254881/5000000000000000 : ℝ) ^ (85/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (6148668287254881/5000000000000000 : ℝ)^85 := by
      have hnat : (3 : ℕ)^16*5000000000000000^85 ≤ 6148668287254881^85*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 6148668287254881 5000000000000000 16 85 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (6148668287254881/5000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 85 16 (by norm_num) hpowers
    exact h
  have major_s0_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(1393691857257931/10000000000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(903644717251831/10000000000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (85/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (1393691857257931/10000000000000000 : ℝ)) (beta := (903644717251831/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow0,s0_corner0a]) (by linarith only [s0_pow0,s0_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![false, true, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (1 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order0.2.2])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(1393691857257931/10000000000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(903644717251831/10000000000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow1 : (1 : ℝ) ^ (85/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^85 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^85*1^16 ≤ 1^16*1^85 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 85 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 85 16 (by norm_num) hpowers
    exact h
  have s0_corner1a : (2 : ℝ) ≤ (11393691857257931/10000000000000000 : ℝ) ^ (85/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (11393691857257931/10000000000000000 : ℝ)^85 := by
      have hnat : (2 : ℕ)^16*10000000000000000^85 ≤ 11393691857257931^85*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 11393691857257931 10000000000000000 16 85 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11393691857257931/10000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 85 16 (by norm_num) hpowers
    exact h
  have s0_corner1b : (3 : ℝ) ≤ (6148668287254881/5000000000000000 : ℝ) ^ (85/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (6148668287254881/5000000000000000 : ℝ)^85 := by
      have hnat : (3 : ℕ)^16*5000000000000000^85 ≤ 6148668287254881^85*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 6148668287254881 5000000000000000 16 85 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (6148668287254881/5000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 85 16 (by norm_num) hpowers
    exact h
  have major_s0_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(1393691857257931/10000000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(903644717251831/10000000000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (85/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (1393691857257931/10000000000000000 : ℝ)) (beta := (903644717251831/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow1,s0_corner1a]) (by linarith only [s0_pow1,s0_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![false, true, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (1 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order1.2.2])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(1393691857257931/10000000000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(903644717251831/10000000000000000 : ℝ)*((-1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow2 : (1 : ℝ) ^ (85/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^85 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^85*1^16 ≤ 1^16*1^85 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 85 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 85 16 (by norm_num) hpowers
    exact h
  have s0_corner2a : (2 : ℝ) ≤ (11393691857257931/10000000000000000 : ℝ) ^ (85/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (11393691857257931/10000000000000000 : ℝ)^85 := by
      have hnat : (2 : ℕ)^16*10000000000000000^85 ≤ 11393691857257931^85*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 11393691857257931 10000000000000000 16 85 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11393691857257931/10000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 85 16 (by norm_num) hpowers
    exact h
  have s0_corner2b : (3 : ℝ) ≤ (6148668287254881/5000000000000000 : ℝ) ^ (85/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (6148668287254881/5000000000000000 : ℝ)^85 := by
      have hnat : (3 : ℕ)^16*5000000000000000^85 ≤ 6148668287254881^85*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 6148668287254881 5000000000000000 16 85 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (6148668287254881/5000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 85 16 (by norm_num) hpowers
    exact h
  have major_s0_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(1393691857257931/10000000000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 1 0))+(903644717251831/10000000000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (85/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (1393691857257931/10000000000000000 : ℝ)) (beta := (903644717251831/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow2,s0_corner2a]) (by linarith only [s0_pow2,s0_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![false, true, true]] hX 2 (by
        change ((-1 : ℝ)*pair X 2 0) ≤ (1 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order2.2.2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(1393691857257931/10000000000000000 : ℝ)*((-1 : ℝ)*pair X 2 0)+(903644717251831/10000000000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s0_0 : ((-81318779/250000000 : ℝ)*X 0 0+(1626375419/5000000000 : ℝ)*X 0 1+(28162943/50000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c325051_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_1 : ((296711547/1250000000 : ℝ)*X 1 0+(-237369211/1000000000 : ℝ)*X 1 1+(7094820153/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c325051_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_7 : ((-68172631/250000000 : ℝ)*X 0 0+(821341433/5000000000 : ℝ)*X 0 1+(1840690499/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c325051_s0_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_8 : ((353818477/2500000000 : ℝ)*X 1 0+(-769156451/10000000000 : ℝ)*X 1 1+(4445084037/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c325051_s0_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_9 : ((1018980649/2500000000 : ℝ)*X 2 0+(13910897/19531250 : ℝ)*X 2 1+(-179197089/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c325051_s0_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_13 : ((276992761/1000000000 : ℝ)*X 0 0+(1026513749/1250000000 : ℝ)*X 0 1+(2735329/156250000 : ℝ)*X 0 2+(276992761/1000000000 : ℝ)*X 1 0+(1026513749/1250000000 : ℝ)*X 1 1+(2735329/156250000 : ℝ)*X 1 2+(276992761/1000000000 : ℝ)*X 2 0+(1026513749/1250000000 : ℝ)*X 2 1+(2735329/156250000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c325051_s0_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_14 : ((-1776711687/10000000000 : ℝ)*X 0 0+(2782449343/10000000000 : ℝ)*X 0 1+(7221504509/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c325051_s0_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_15 : ((490131759/5000000000 : ℝ)*X 1 0+(-307861953/2000000000 : ℝ)*X 1 1+(1736341721/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c325051_s0_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_16 : ((938639131/1250000000 : ℝ)*X 2 0+(182986647/500000000 : ℝ)*X 2 1+(-23169563/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c325051_s0_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_20 : ((3725761189/5000000000 : ℝ)*X 0 0+(3692950633/10000000000 : ℝ)*X 0 1+(46628527/2500000000 : ℝ)*X 0 2+(3725761189/5000000000 : ℝ)*X 1 0+(3692950633/10000000000 : ℝ)*X 1 1+(46628527/2500000000 : ℝ)*X 1 2+(3725761189/5000000000 : ℝ)*X 2 0+(3692950633/10000000000 : ℝ)*X 2 1+(46628527/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c325051_s0_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_21 : ((-2465951249/5000000000 : ℝ)*X 0 0+(259797567/625000000 : ℝ)*X 0 1+(1551471143/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c325051_s0_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_22 : ((971954939/10000000000 : ℝ)*X 1 0+(-349420241/2000000000 : ℝ)*X 1 1+(8543758131/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c325051_s0_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_23 : ((6782544291/10000000000 : ℝ)*X 2 0+(2246462469/5000000000 : ℝ)*X 2 1+(-19321199/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c325051_s0_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_27 : ((1301899589/5000000000 : ℝ)*X 0 0+(8372588953/10000000000 : ℝ)*X 0 1+(94887693/10000000000 : ℝ)*X 0 2+(1301899589/5000000000 : ℝ)*X 1 0+(8372588953/10000000000 : ℝ)*X 1 1+(94887693/10000000000 : ℝ)*X 1 2+(1301899589/5000000000 : ℝ)*X 2 0+(8372588953/10000000000 : ℝ)*X 2 1+(94887693/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c325051_s0_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s0_0 : (0 : ℝ) ≤ ((63371/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(63371/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (9906803147920610890443/500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (471693596763/500000000000 : ℝ)*(base7) + (915533/250000000000 : ℝ)*(base19) + (1225996443/200000000000 : ℝ)*(base49) + (37002271967/500000000000 : ℝ)*(base60) + (175520405183/100000000000 : ℝ)*(major_s0_0) + (175520405183/100000000000 : ℝ)*(major_s0_1) + (175520405183/100000000000 : ℝ)*(major_s0_2) + (188129/250000000000 : ℝ)*(sp_s0_0) + (2116882859047/1000000000000 : ℝ)*(sp_s0_7) + (1058474523131/500000000000 : ℝ)*(sp_s0_8) + (1058476354197/500000000000 : ℝ)*(sp_s0_9) + (227088542817/125000000000 : ℝ)*(sp_s0_13) + (539819/7812500000 : ℝ)*(sp_s0_14) + (35957999/200000000000 : ℝ)*(sp_s0_27) + (436750469503/500000000000 : ℝ)*(f.failure) + (1058476354197/500000000000 : ℝ)*(f.sum) + (4344628677/5000000000000000000000 : ℝ)*base63 + (1209595025340073/1000000000000000000000000000 : ℝ)*base65 + (336529413740073/1000000000000000000000000000 : ℝ)*base66 + (931054043143627/1000000000000000000000000000 : ℝ)*base69 + (593027475198223/500000000000000000000000000 : ℝ)*base71 + (579512474740073/1000000000000000000000000000 : ℝ)*base73 + (609757070856373/1000000000000000000000000000 : ℝ)*base75 + (1189299763956373/1000000000000000000000000000 : ℝ)*base77 + (268248897/2000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base81 + (36683/50000000000000000 : ℝ)*base86 + (36683/50000000000000000 : ℝ)*base88 + (36683/50000000000000000 : ℝ)*base90 + (1/1000000000000 : ℝ)*base92 + hcertificate_margin
  have ratio_s0_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(62713/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(62713/100000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (29849209673630340757953/2500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (248286777029/1000000000000 : ℝ)*(base5) + (924445590291/1000000000000 : ℝ)*(base7) + (2493/500000000000 : ℝ)*(base49) + (51393561103/250000000000 : ℝ)*(base60) + (1925306471829/1000000000000 : ℝ)*(major_s0_0) + (1925306471829/1000000000000 : ℝ)*(major_s0_1) + (1925306471829/1000000000000 : ℝ)*(major_s0_2) + (8485983/1000000000000 : ℝ)*(sp_s0_0) + (11967987/250000000000 : ℝ)*(sp_s0_7) + (2382889719139/1000000000000 : ℝ)*(sp_s0_14) + (74465196269/31250000000 : ℝ)*(sp_s0_15) + (2631232854099/1000000000000 : ℝ)*(sp_s0_16) + (817156756431/500000000000 : ℝ)*(sp_s0_20) + (29898231/500000000000 : ℝ)*(sp_s0_22) + (2395386749/2500000000 : ℝ)*(f.failure) + (238294607707/100000000000 : ℝ)*(f.sum) + (4322249457/10000000000000000000000 : ℝ)*base63 + (8039267455168899/10000000000000000000000000000 : ℝ)*base65 + (4613931644831101/10000000000000000000000000000 : ℝ)*base67 + (7633869363674201/10000000000000000000000000000 : ℝ)*base69 + (2086691861247349/5000000000000000000000000000 : ℝ)*base71 + (5898810042168899/10000000000000000000000000000 : ℝ)*base73 + (4008410450325799/10000000000000000000000000000 : ℝ)*base75 + (3572557332325799/10000000000000000000000000000 : ℝ)*base77 + (219513411/10000000000000000000000 : ℝ)*base78 + (61/250000000000000 : ℝ)*base87 + (61/250000000000000 : ℝ)*base89 + (61/250000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s0_2 : (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(6217/25000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(6217/25000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (379783681183574850393/39062500000000000000000000 : ℝ) := by norm_num
    linear_combination (3144949/1000000000000 : ℝ)*(base5) + (28476275333/200000000000 : ℝ)*(base7) + (66405516373/125000000000 : ℝ)*(base39) + (697063/500000000000 : ℝ)*(base44) + (546363824493/1000000000000 : ℝ)*(base49) + (54989299227/31250000000 : ℝ)*(major_s0_0) + (879828090569/500000000000 : ℝ)*(major_s0_1) + (54989299227/31250000000 : ℝ)*(major_s0_2) + (35114361/1000000000000 : ℝ)*(sp_s0_1) + (9515373/125000000000 : ℝ)*(sp_s0_13) + (2565121119019/1000000000000 : ℝ)*(sp_s0_21) + (2565084610533/1000000000000 : ℝ)*(sp_s0_22) + (80160133249/31250000000 : ℝ)*(sp_s0_23) + (1018018009539/1000000000000 : ℝ)*(sp_s0_27) + (218929323733/250000000000 : ℝ)*(f.failure) + (2565121119019/1000000000000 : ℝ)*(f.sum) + (837164645156653/5000000000000000000000000000 : ℝ)*base62 + (80796876209113/312500000000000000000000000 : ℝ)*base64 + (924362118418161/5000000000000000000000000000 : ℝ)*base67 + (33993584325587/312500000000000000000000000 : ℝ)*base68 + (13162881285513/156250000000000000000000000 : ℝ)*base70 + (264447455084113/312500000000000000000000000 : ℝ)*base72 + (950258926552739/5000000000000000000000000000 : ℝ)*base75 + (58051546424413/312500000000000000000000000 : ℝ)*base76 + (1853121522427647/5000000000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base83 + (14713/25000000000000000 : ℝ)*base86 + (14713/25000000000000000 : ℝ)*base88 + (14713/25000000000000000 : ℝ)*base90 + (1/1000000000000 : ℝ)*base93 + hcertificate_margin
  have s1_pow0 : (63371/100000 : ℝ) ^ (85/16 : ℝ) ≤ (8862241938127576853/100000000000000000000 : ℝ) := by
    have hpowers : (63371/100000 : ℝ)^85 ≤ (8862241938127576853/100000000000000000000 : ℝ)^16 := by
      have hnat : (63371 : ℕ)^85*100000000000000000000^16 ≤ 8862241938127576853^16*100000^85 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        63371 100000 8862241938127576853 100000000000000000000 85 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (63371/100000 : ℝ)) (X := (8862241938127576853/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 85 16 (by norm_num) hpowers
    exact h
  have s1_corner0a : (108862241938127576853/100000000000000000000 : ℝ) ≤ (1016112056703333/1000000000000000 : ℝ) ^ (85/16 : ℝ) := by
    have hpowers : (108862241938127576853/100000000000000000000 : ℝ)^16 ≤ (1016112056703333/1000000000000000 : ℝ)^85 := by
      have hnat : (108862241938127576853 : ℕ)^16*1000000000000000^85 ≤ 1016112056703333^85*100000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        108862241938127576853 100000000000000000000 1016112056703333 1000000000000000 16 85 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1016112056703333/1000000000000000 : ℝ)) (X := (108862241938127576853/100000000000000000000 : ℝ)) (by norm_num) 85 16 (by norm_num) hpowers
    exact h
  have s1_corner0b : (58862241938127576853/50000000000000000000 : ℝ) ≤ (5155961150663689/5000000000000000 : ℝ) ^ (85/16 : ℝ) := by
    have hpowers : (58862241938127576853/50000000000000000000 : ℝ)^16 ≤ (5155961150663689/5000000000000000 : ℝ)^85 := by
      have hnat : (58862241938127576853 : ℕ)^16*5000000000000000^85 ≤ 5155961150663689^85*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        58862241938127576853 50000000000000000000 5155961150663689 5000000000000000 16 85 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5155961150663689/5000000000000000 : ℝ)) (X := (58862241938127576853/50000000000000000000 : ℝ)) (by norm_num) 85 16 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(16112056703333/633710000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(4712554196689/198034375000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (85/16 : ℝ)) (rho := (63371/100000 : ℝ)) (alpha := (16112056703333/633710000000000 : ℝ)) (beta := (4712554196689/198034375000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![false, true, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (63371/100000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(16112056703333/633710000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(4712554196689/198034375000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (62713/100000 : ℝ) ^ (85/16 : ℝ) ≤ (1048026197221209413/12500000000000000000 : ℝ) := by
    have hpowers : (62713/100000 : ℝ)^85 ≤ (1048026197221209413/12500000000000000000 : ℝ)^16 := by
      have hnat : (62713 : ℕ)^85*12500000000000000000^16 ≤ 1048026197221209413^16*100000^85 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        62713 100000 1048026197221209413 12500000000000000000 85 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (62713/100000 : ℝ)) (X := (1048026197221209413/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 85 16 (by norm_num) hpowers
    exact h
  have s1_corner1a : (13548026197221209413/12500000000000000000 : ℝ) ≤ (2538176663141011/2500000000000000 : ℝ) ^ (85/16 : ℝ) := by
    have hpowers : (13548026197221209413/12500000000000000000 : ℝ)^16 ≤ (2538176663141011/2500000000000000 : ℝ)^85 := by
      have hnat : (13548026197221209413 : ℕ)^16*2500000000000000^85 ≤ 2538176663141011^85*12500000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        13548026197221209413 12500000000000000000 2538176663141011 2500000000000000 16 85 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2538176663141011/2500000000000000 : ℝ)) (X := (13548026197221209413/12500000000000000000 : ℝ)) (by norm_num) 85 16 (by norm_num) hpowers
    exact h
  have s1_corner1b : (7298026197221209413/6250000000000000000 : ℝ) ≤ (10296106273676893/10000000000000000 : ℝ) ^ (85/16 : ℝ) := by
    have hpowers : (7298026197221209413/6250000000000000000 : ℝ)^16 ≤ (10296106273676893/10000000000000000 : ℝ)^85 := by
      have hnat : (7298026197221209413 : ℕ)^16*10000000000000000^85 ≤ 10296106273676893^85*6250000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7298026197221209413 6250000000000000000 10296106273676893 10000000000000000 16 85 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10296106273676893/10000000000000000 : ℝ)) (X := (7298026197221209413/6250000000000000000 : ℝ)) (by norm_num) 85 16 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(38176663141011/1567825000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(143399621112849/6271300000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (85/16 : ℝ)) (rho := (62713/100000 : ℝ)) (alpha := (38176663141011/1567825000000000 : ℝ)) (beta := (143399621112849/6271300000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![false, true, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (62713/100000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(38176663141011/1567825000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(143399621112849/6271300000000000 : ℝ)*((-1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (6217/25000 : ℝ) ^ (85/16 : ℝ) ≤ (61566159315346991/100000000000000000000 : ℝ) := by
    have hpowers : (6217/25000 : ℝ)^85 ≤ (61566159315346991/100000000000000000000 : ℝ)^16 := by
      have hnat : (6217 : ℕ)^85*100000000000000000000^16 ≤ 61566159315346991^16*25000^85 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6217 25000 61566159315346991 100000000000000000000 85 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (6217/25000 : ℝ)) (X := (61566159315346991/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 85 16 (by norm_num) hpowers
    exact h
  have s1_corner2a : (100061566159315346991/100000000000000000000 : ℝ) ≤ (2500289650731769/2500000000000000 : ℝ) ^ (85/16 : ℝ) := by
    have hpowers : (100061566159315346991/100000000000000000000 : ℝ)^16 ≤ (2500289650731769/2500000000000000 : ℝ)^85 := by
      have hnat : (100061566159315346991 : ℕ)^16*2500000000000000^85 ≤ 2500289650731769^85*100000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100061566159315346991 100000000000000000000 2500289650731769 2500000000000000 16 85 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500289650731769/2500000000000000 : ℝ)) (X := (100061566159315346991/100000000000000000000 : ℝ)) (by norm_num) 85 16 (by norm_num) hpowers
    exact h
  have s1_corner2b : (50061566159315346991/50000000000000000000 : ℝ) ≤ (5001158313658577/5000000000000000 : ℝ) ^ (85/16 : ℝ) := by
    have hpowers : (50061566159315346991/50000000000000000000 : ℝ)^16 ≤ (5001158313658577/5000000000000000 : ℝ)^85 := by
      have hnat : (50061566159315346991 : ℕ)^16*5000000000000000^85 ≤ 5001158313658577^85*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50061566159315346991 50000000000000000000 5001158313658577 5000000000000000 16 85 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5001158313658577/5000000000000000 : ℝ)) (X := (50061566159315346991/50000000000000000000 : ℝ)) (by norm_num) 85 16 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(289650731769/621700000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 1 0))+(579012195039/1243400000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (85/16 : ℝ)) (rho := (6217/25000 : ℝ)) (alpha := (289650731769/621700000000000 : ℝ)) (beta := (579012195039/1243400000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![false, true, true]] hX 2 (by
        change ((-1 : ℝ)*pair X 2 0) ≤ (6217/25000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(289650731769/621700000000000 : ℝ)*((-1 : ℝ)*pair X 2 0)+(579012195039/1243400000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-896960491/2500000000 : ℝ)*X 0 0+(895972289/2500000000 : ℝ)*X 0 1+(1005959483/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c325051_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_1 : ((738825037/2500000000 : ℝ)*X 1 0+(-1476022113/5000000000 : ℝ)*X 1 1+(6150279277/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c325051_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((2606472669/5000000000 : ℝ)*X 2 0+(2609207727/5000000000 : ℝ)*X 2 1+(-758528141/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c325051_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_6 : ((4964121797/10000000000 : ℝ)*X 0 0+(993866163/2000000000 : ℝ)*X 0 1+(268069261/1250000000 : ℝ)*X 0 2+(4964121797/10000000000 : ℝ)*X 1 0+(993866163/2000000000 : ℝ)*X 1 1+(268069261/1250000000 : ℝ)*X 1 2+(4964121797/10000000000 : ℝ)*X 2 0+(993866163/2000000000 : ℝ)*X 2 1+(268069261/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c325051_s1_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have hsep : (-452817/50000 : ℝ) < ((-200939/100000 : ℝ)*P 0+(-200939/100000 : ℝ)*P 1+(-200939/100000 : ℝ)*P 2+(1 : ℝ)*T) := by
    have hcertificate_margin : (-452817/50000 : ℝ) < (-1586332132535878312946935091413208259/176482224260650000000000000000000000 : ℝ) := by norm_num
    linear_combination (1079/1000000000000 : ℝ)*(base8) + (10427/1000000000000 : ℝ)*(base11) + (341/500000000000 : ℝ)*(base15) + (7187/1000000000000 : ℝ)*(base43) + (241956154557/1000000000000 : ℝ)*(base49) + (269/125000000000 : ℝ)*(base50) + (186987340417/1000000000000 : ℝ)*(base59) + (19580386663/31250000000 : ℝ)*(base60) + (200939/100000 : ℝ)*(major_s1_0) + (2009389992813/1000000000000 : ℝ)*(major_s1_1) + (200939/100000 : ℝ)*(major_s1_2) + (2996207558169/1000000000000 : ℝ)*(sp_s1_0) + (2996207576179/1000000000000 : ℝ)*(sp_s1_1) + (119848302787/40000000000 : ℝ)*(sp_s1_2) + (1 : ℝ)*(sp_s1_6) + (1498103788431/500000000000 : ℝ)*(f.sum) + (1116193956582194603/1392452575000000000000000000000 : ℝ)*base63 + (9931560970503/15542500000000000000000000 : ℝ)*base65 + (112003309870459/895900000000000000000000000 : ℝ)*base67 + (11934056895809/15542500000000000000000000 : ℝ)*base69 + (669494922242966089/1969887535000000000000000000000 : ℝ)*base71 + (175168845972707/633710000000000000000000000 : ℝ)*base73 + (2760005108069/55993750000000000000000000 : ℝ)*base74 + (739486027279/12674200000000000000000000 : ℝ)*base76 + (8099846907395773939/56774078900000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base82 + hcertificate_margin
  linarith only [hsep,f.failure]

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
namespace HlawkaSchatten.DiagonalCutoff4
theorem coarse_distinct_p025_b027 (p : ℝ) (hpa : (85/16 : ℝ) ≤ p) (hpb : p ≤ (87/16 : ℝ))
    (c : Fin 88) (hlo : 51 ≤ c.val) (hhi : c.val < 52)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (200939/100000 : ℝ) (33069/20000 : ℝ) (81317/100000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  have hc : c=51 := by omega
  rcases hc with rfl
  · exact collision_c325051 p hpa (by linarith only [hpb]) X hX

end HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p : ℝ) (hpa : (85/16 : ℝ) ≤ p) (hpb : p ≤ (87/16 : ℝ))
    (c : Fin 88) (hlo : 51 ≤ c.val) (hhi : c.val < 52)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (200939/100000 : ℝ) (33069/20000 : ℝ) (81317/100000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  exact HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p025_b027 p hpa hpb c hlo hhi hn63 hn87 X hX

#print axioms solution
