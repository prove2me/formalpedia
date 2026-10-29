-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p028_b030
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T02:21:57.453881+00:00
-- url     : https://prove2.me/submissions/2b710144-ac3a-4652-a39f-d5b95e9df3ad

import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c328061_s0
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c328061_s1
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c328061_s2
import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c328062_s0
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c328062_s1
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c328062_s2
import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_FiniteCharts
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
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4
theorem HlawkaSchatten.DiagonalCutoff4.collision_c328061 (p : ℝ) (hpa : (91/16 : ℝ) ≤ p) (hpb : p ≤ (93/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (8679/4000 : ℝ) (80697/50000 : ℝ) (82433/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, true]]) : False := by
  have h0 := collision_c328061_s0 p hpa hpb X hX
  have h1 := collision_c328061_s1 p hpa hpb X hX h0
  exact collision_c328061_s2 p hpa hpb X hX h1

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4
theorem HlawkaSchatten.DiagonalCutoff4.collision_c328062 (p : ℝ) (hpa : (91/16 : ℝ) ≤ p) (hpb : p ≤ (93/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (8679/4000 : ℝ) (80697/50000 : ℝ) (82433/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, false]]) : False := by
  have h0 := collision_c328062_s0 p hpa hpb X hX
  have h1 := collision_c328062_s1 p hpa hpb X hX h0
  exact collision_c328062_s2 p hpa hpb X hX h1

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
theorem collision_support_c328060_s0_0 (p : ℝ) (hpa : (91/16 : ℝ) ≤ p) (hpb : p ≤ (93/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-986273/8000000 : ℝ)*x 0 + (2242896169/5000000000 : ℝ)*x 1 + (-3004035157/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (986273/8000000 : ℝ)^93 ≤ (7980034119637/100000000000000 : ℝ)^77 := by
    have hnat : (986273 : ℕ)^93*100000000000000^77 ≤ 7980034119637^77*8000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      986273 8000000 7980034119637 100000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2242896169/5000000000 : ℝ)^93 ≤ (37974674167073/100000000000000 : ℝ)^77 := by
    have hnat : (2242896169 : ℕ)^93*100000000000000^77 ≤ 37974674167073^77*5000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2242896169 5000000000 37974674167073 100000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3004035157/5000000000 : ℝ)^93 ≤ (13511322925177/25000000000000 : ℝ)^77 := by
    have hnat : (3004035157 : ℕ)^93*25000000000000^77 ≤ 13511322925177^77*5000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3004035157 5000000000 13511322925177 25000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (93/16 : ℝ)) 93 77 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-986273/8000000 : ℝ), (2242896169/5000000000 : ℝ), (-3004035157/5000000000 : ℝ)] ![(7980034119637/100000000000000 : ℝ), (37974674167073/100000000000000 : ℝ), (13511322925177/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-986273/8000000 : ℝ)|^93 ≤ (7980034119637/100000000000000 : ℝ)^77
        have hw : |(-986273/8000000 : ℝ)|=(986273/8000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2242896169/5000000000 : ℝ)|^93 ≤ (37974674167073/100000000000000 : ℝ)^77
        have hw : |(2242896169/5000000000 : ℝ)|=(2242896169/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3004035157/5000000000 : ℝ)|^93 ≤ (13511322925177/25000000000000 : ℝ)^77
        have hw : |(-3004035157/5000000000 : ℝ)|=(3004035157/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c328060_s0_1 (p : ℝ) (hpa : (91/16 : ℝ) ≤ p) (hpb : p ≤ (93/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2242896229/5000000000 : ℝ)*x 0 + (-1232841047/10000000000 : ℝ)*x 1 + (-6008070347/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2242896229/5000000000 : ℝ)^93 ≤ (37974675394027/100000000000000 : ℝ)^77 := by
    have hnat : (2242896229 : ℕ)^93*100000000000000^77 ≤ 37974675394027^77*5000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2242896229 5000000000 37974675394027 100000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1232841047/10000000000 : ℝ)^93 ≤ (1995008133151/25000000000000 : ℝ)^77 := by
    have hnat : (1232841047 : ℕ)^93*25000000000000^77 ≤ 1995008133151^77*10000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1232841047 10000000000 1995008133151 25000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6008070347/10000000000 : ℝ)^93 ≤ (54045292059241/100000000000000 : ℝ)^77 := by
    have hnat : (6008070347 : ℕ)^93*100000000000000^77 ≤ 54045292059241^77*10000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6008070347 10000000000 54045292059241 100000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (93/16 : ℝ)) 93 77 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2242896229/5000000000 : ℝ), (-1232841047/10000000000 : ℝ), (-6008070347/10000000000 : ℝ)] ![(37974675394027/100000000000000 : ℝ), (1995008133151/25000000000000 : ℝ), (54045292059241/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2242896229/5000000000 : ℝ)|^93 ≤ (37974675394027/100000000000000 : ℝ)^77
        have hw : |(2242896229/5000000000 : ℝ)|=(2242896229/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1232841047/10000000000 : ℝ)|^93 ≤ (1995008133151/25000000000000 : ℝ)^77
        have hw : |(-1232841047/10000000000 : ℝ)|=(1232841047/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-6008070347/10000000000 : ℝ)|^93 ≤ (54045292059241/100000000000000 : ℝ)^77
        have hw : |(-6008070347/10000000000 : ℝ)|=(6008070347/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c328060_s0_7 (p : ℝ) (hpa : (91/16 : ℝ) ≤ p) (hpb : p ≤ (93/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-866048933/5000000000 : ℝ)*x 0 + (1435027549/10000000000 : ℝ)*x 1 + (-510847359/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (866048933/5000000000 : ℝ)^93 ≤ (12032440148269/100000000000000 : ℝ)^77 := by
    have hnat : (866048933 : ℕ)^93*100000000000000^77 ≤ 12032440148269^77*5000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      866048933 5000000000 12032440148269 100000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1435027549/10000000000 : ℝ)^93 ≤ (383462021447/4000000000000 : ℝ)^77 := by
    have hnat : (1435027549 : ℕ)^93*4000000000000^77 ≤ 383462021447^77*10000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1435027549 10000000000 383462021447 4000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (510847359/625000000 : ℝ)^93 ≤ (9797626162919/12500000000000 : ℝ)^77 := by
    have hnat : (510847359 : ℕ)^93*12500000000000^77 ≤ 9797626162919^77*625000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      510847359 625000000 9797626162919 12500000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (93/16 : ℝ)) 93 77 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-866048933/5000000000 : ℝ), (1435027549/10000000000 : ℝ), (-510847359/625000000 : ℝ)] ![(12032440148269/100000000000000 : ℝ), (383462021447/4000000000000 : ℝ), (9797626162919/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-866048933/5000000000 : ℝ)|^93 ≤ (12032440148269/100000000000000 : ℝ)^77
        have hw : |(-866048933/5000000000 : ℝ)|=(866048933/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1435027549/10000000000 : ℝ)|^93 ≤ (383462021447/4000000000000 : ℝ)^77
        have hw : |(1435027549/10000000000 : ℝ)|=(1435027549/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-510847359/625000000 : ℝ)|^93 ≤ (9797626162919/12500000000000 : ℝ)^77
        have hw : |(-510847359/625000000 : ℝ)|=(510847359/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c328060_s0_8 (p : ℝ) (hpa : (91/16 : ℝ) ≤ p) (hpb : p ≤ (93/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2452478397/10000000000 : ℝ)*x 0 + (-148571051/2500000000 : ℝ)*x 1 + (-204339013/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2452478397/10000000000 : ℝ)^93 ≤ (3662687793527/20000000000000 : ℝ)^77 := by
    have hnat : (2452478397 : ℕ)^93*20000000000000^77 ≤ 3662687793527^77*10000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2452478397 10000000000 3662687793527 20000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (148571051/2500000000 : ℝ)^93 ≤ (1652759783289/50000000000000 : ℝ)^77 := by
    have hnat : (148571051 : ℕ)^93*50000000000000^77 ≤ 1652759783289^77*2500000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      148571051 2500000000 1652759783289 50000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (204339013/250000000 : ℝ)^93 ≤ (15676208291121/20000000000000 : ℝ)^77 := by
    have hnat : (204339013 : ℕ)^93*20000000000000^77 ≤ 15676208291121^77*250000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      204339013 250000000 15676208291121 20000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (93/16 : ℝ)) 93 77 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2452478397/10000000000 : ℝ), (-148571051/2500000000 : ℝ), (-204339013/250000000 : ℝ)] ![(3662687793527/20000000000000 : ℝ), (1652759783289/50000000000000 : ℝ), (15676208291121/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2452478397/10000000000 : ℝ)|^93 ≤ (3662687793527/20000000000000 : ℝ)^77
        have hw : |(2452478397/10000000000 : ℝ)|=(2452478397/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-148571051/2500000000 : ℝ)|^93 ≤ (1652759783289/50000000000000 : ℝ)^77
        have hw : |(-148571051/2500000000 : ℝ)|=(148571051/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-204339013/250000000 : ℝ)|^93 ≤ (15676208291121/20000000000000 : ℝ)^77
        have hw : |(-204339013/250000000 : ℝ)|=(204339013/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c328060_s0_9 (p : ℝ) (hpa : (91/16 : ℝ) ≤ p) (hpb : p ≤ (93/16 : ℝ)) (x : Fin 3 → ℝ) :
    (214996739/1000000000 : ℝ)*x 0 + (3975698411/5000000000 : ℝ)*x 1 + (1307018889/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (214996739/1000000000 : ℝ)^93 ≤ (7810636418113/50000000000000 : ℝ)^77 := by
    have hnat : (214996739 : ℕ)^93*50000000000000^77 ≤ 7810636418113^77*1000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      214996739 1000000000 7810636418113 50000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3975698411/5000000000 : ℝ)^93 ≤ (15163042198823/20000000000000 : ℝ)^77 := by
    have hnat : (3975698411 : ℕ)^93*20000000000000^77 ≤ 15163042198823^77*5000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3975698411 5000000000 15163042198823 20000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1307018889/10000000000 : ℝ)^93 ≤ (8563516157837/100000000000000 : ℝ)^77 := by
    have hnat : (1307018889 : ℕ)^93*100000000000000^77 ≤ 8563516157837^77*10000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1307018889 10000000000 8563516157837 100000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (93/16 : ℝ)) 93 77 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(214996739/1000000000 : ℝ), (3975698411/5000000000 : ℝ), (1307018889/10000000000 : ℝ)] ![(7810636418113/50000000000000 : ℝ), (15163042198823/20000000000000 : ℝ), (8563516157837/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(214996739/1000000000 : ℝ)|^93 ≤ (7810636418113/50000000000000 : ℝ)^77
        have hw : |(214996739/1000000000 : ℝ)|=(214996739/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3975698411/5000000000 : ℝ)|^93 ≤ (15163042198823/20000000000000 : ℝ)^77
        have hw : |(3975698411/5000000000 : ℝ)|=(3975698411/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1307018889/10000000000 : ℝ)|^93 ≤ (8563516157837/100000000000000 : ℝ)^77
        have hw : |(1307018889/10000000000 : ℝ)|=(1307018889/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c328060_s0_13 (p : ℝ) (hpa : (91/16 : ℝ) ≤ p) (hpb : p ≤ (93/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4197462651/10000000000 : ℝ)*x 0 + (874449191/1250000000 : ℝ)*x 1 + (-1889393/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4197462651/10000000000 : ℝ)^93 ≤ (7009328906741/20000000000000 : ℝ)^77 := by
    have hnat : (4197462651 : ℕ)^93*20000000000000^77 ≤ 7009328906741^77*10000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4197462651 10000000000 7009328906741 20000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (874449191/1250000000 : ℝ)^93 ≤ (16237543599377/25000000000000 : ℝ)^77 := by
    have hnat : (874449191 : ℕ)^93*25000000000000^77 ≤ 16237543599377^77*1250000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      874449191 1250000000 16237543599377 25000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1889393/10000000000 : ℝ)^93 ≤ (318105437/10000000000000 : ℝ)^77 := by
    have hnat : (1889393 : ℕ)^93*10000000000000^77 ≤ 318105437^77*10000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1889393 10000000000 318105437 10000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (93/16 : ℝ)) 93 77 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4197462651/10000000000 : ℝ), (874449191/1250000000 : ℝ), (-1889393/10000000000 : ℝ)] ![(7009328906741/20000000000000 : ℝ), (16237543599377/25000000000000 : ℝ), (318105437/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4197462651/10000000000 : ℝ)|^93 ≤ (7009328906741/20000000000000 : ℝ)^77
        have hw : |(4197462651/10000000000 : ℝ)|=(4197462651/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(874449191/1250000000 : ℝ)|^93 ≤ (16237543599377/25000000000000 : ℝ)^77
        have hw : |(874449191/1250000000 : ℝ)|=(874449191/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1889393/10000000000 : ℝ)|^93 ≤ (318105437/10000000000000 : ℝ)^77
        have hw : |(-1889393/10000000000 : ℝ)|=(1889393/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c328060_s0_14 (p : ℝ) (hpa : (91/16 : ℝ) ≤ p) (hpb : p ≤ (93/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-167522951/2000000000 : ℝ)*x 0 + (521557281/2500000000 : ℝ)*x 1 + (-8307326931/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (167522951/2000000000 : ℝ)^93 ≤ (312709689087/6250000000000 : ℝ)^77 := by
    have hnat : (167522951 : ℕ)^93*6250000000000^77 ≤ 312709689087^77*2000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      167522951 2000000000 312709689087 6250000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (521557281/2500000000 : ℝ)^93 ≤ (15063667883407/100000000000000 : ℝ)^77 := by
    have hnat : (521557281 : ℕ)^93*100000000000000^77 ≤ 15063667883407^77*2500000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      521557281 2500000000 15063667883407 100000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (8307326931/10000000000 : ℝ)^93 ≤ (79932977080591/100000000000000 : ℝ)^77 := by
    have hnat : (8307326931 : ℕ)^93*100000000000000^77 ≤ 79932977080591^77*10000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8307326931 10000000000 79932977080591 100000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (93/16 : ℝ)) 93 77 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-167522951/2000000000 : ℝ), (521557281/2500000000 : ℝ), (-8307326931/10000000000 : ℝ)] ![(312709689087/6250000000000 : ℝ), (15063667883407/100000000000000 : ℝ), (79932977080591/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-167522951/2000000000 : ℝ)|^93 ≤ (312709689087/6250000000000 : ℝ)^77
        have hw : |(-167522951/2000000000 : ℝ)|=(167522951/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(521557281/2500000000 : ℝ)|^93 ≤ (15063667883407/100000000000000 : ℝ)^77
        have hw : |(521557281/2500000000 : ℝ)|=(521557281/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-8307326931/10000000000 : ℝ)|^93 ≤ (79932977080591/100000000000000 : ℝ)^77
        have hw : |(-8307326931/10000000000 : ℝ)|=(8307326931/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c328060_s0_15 (p : ℝ) (hpa : (91/16 : ℝ) ≤ p) (hpb : p ≤ (93/16 : ℝ)) (x : Fin 3 → ℝ) :
    (940644603/10000000000 : ℝ)*x 0 + (-499890973/2500000000 : ℝ)*x 1 + (-8307325133/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (940644603/10000000000 : ℝ)^93 ≤ (5755875616981/100000000000000 : ℝ)^77 := by
    have hnat : (940644603 : ℕ)^93*100000000000000^77 ≤ 5755875616981^77*10000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      940644603 10000000000 5755875616981 100000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (499890973/2500000000 : ℝ)^93 ≤ (3577792044019/25000000000000 : ℝ)^77 := by
    have hnat : (499890973 : ℕ)^93*25000000000000^77 ≤ 3577792044019^77*2500000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      499890973 2500000000 3577792044019 25000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (8307325133/10000000000 : ℝ)^93 ≤ (19983239046347/25000000000000 : ℝ)^77 := by
    have hnat : (8307325133 : ℕ)^93*25000000000000^77 ≤ 19983239046347^77*10000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8307325133 10000000000 19983239046347 25000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (93/16 : ℝ)) 93 77 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(940644603/10000000000 : ℝ), (-499890973/2500000000 : ℝ), (-8307325133/10000000000 : ℝ)] ![(5755875616981/100000000000000 : ℝ), (3577792044019/25000000000000 : ℝ), (19983239046347/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(940644603/10000000000 : ℝ)|^93 ≤ (5755875616981/100000000000000 : ℝ)^77
        have hw : |(940644603/10000000000 : ℝ)|=(940644603/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-499890973/2500000000 : ℝ)|^93 ≤ (3577792044019/25000000000000 : ℝ)^77
        have hw : |(-499890973/2500000000 : ℝ)|=(499890973/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-8307325133/10000000000 : ℝ)|^93 ≤ (19983239046347/25000000000000 : ℝ)^77
        have hw : |(-8307325133/10000000000 : ℝ)|=(8307325133/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c328060_s0_16 (p : ℝ) (hpa : (91/16 : ℝ) ≤ p) (hpb : p ≤ (93/16 : ℝ)) (x : Fin 3 → ℝ) :
    (6621654931/10000000000 : ℝ)*x 0 + (3586388103/10000000000 : ℝ)*x 1 + (1515317289/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6621654931/10000000000 : ℝ)^93 ≤ (60780572729009/100000000000000 : ℝ)^77 := by
    have hnat : (6621654931 : ℕ)^93*100000000000000^77 ≤ 60780572729009^77*10000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6621654931 10000000000 60780572729009 100000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3586388103/10000000000 : ℝ)^93 ≤ (28981345160751/100000000000000 : ℝ)^77 := by
    have hnat : (3586388103 : ℕ)^93*100000000000000^77 ≤ 28981345160751^77*10000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3586388103 10000000000 28981345160751 100000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1515317289/10000000000 : ℝ)^93 ≤ (5119041046871/50000000000000 : ℝ)^77 := by
    have hnat : (1515317289 : ℕ)^93*50000000000000^77 ≤ 5119041046871^77*10000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1515317289 10000000000 5119041046871 50000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (93/16 : ℝ)) 93 77 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6621654931/10000000000 : ℝ), (3586388103/10000000000 : ℝ), (1515317289/10000000000 : ℝ)] ![(60780572729009/100000000000000 : ℝ), (28981345160751/100000000000000 : ℝ), (5119041046871/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6621654931/10000000000 : ℝ)|^93 ≤ (60780572729009/100000000000000 : ℝ)^77
        have hw : |(6621654931/10000000000 : ℝ)|=(6621654931/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3586388103/10000000000 : ℝ)|^93 ≤ (28981345160751/100000000000000 : ℝ)^77
        have hw : |(3586388103/10000000000 : ℝ)|=(3586388103/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1515317289/10000000000 : ℝ)|^93 ≤ (5119041046871/50000000000000 : ℝ)^77
        have hw : |(1515317289/10000000000 : ℝ)|=(1515317289/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c328060_s0_20 (p : ℝ) (hpa : (91/16 : ℝ) ≤ p) (hpb : p ≤ (93/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4221314681/5000000000 : ℝ)*x 0 + (308996163/1250000000 : ℝ)*x 1 + (-320137/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4221314681/5000000000 : ℝ)^93 ≤ (40754012288929/50000000000000 : ℝ)^77 := by
    have hnat : (4221314681 : ℕ)^93*50000000000000^77 ≤ 40754012288929^77*5000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4221314681 5000000000 40754012288929 50000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (308996163/1250000000 : ℝ)^93 ≤ (18489371717323/100000000000000 : ℝ)^77 := by
    have hnat : (308996163 : ℕ)^93*100000000000000^77 ≤ 18489371717323^77*1250000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      308996163 1250000000 18489371717323 100000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (320137/2000000000 : ℝ)^93 ≤ (2603695623/100000000000000 : ℝ)^77 := by
    have hnat : (320137 : ℕ)^93*100000000000000^77 ≤ 2603695623^77*2000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      320137 2000000000 2603695623 100000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (93/16 : ℝ)) 93 77 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4221314681/5000000000 : ℝ), (308996163/1250000000 : ℝ), (-320137/2000000000 : ℝ)] ![(40754012288929/50000000000000 : ℝ), (18489371717323/100000000000000 : ℝ), (2603695623/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4221314681/5000000000 : ℝ)|^93 ≤ (40754012288929/50000000000000 : ℝ)^77
        have hw : |(4221314681/5000000000 : ℝ)|=(4221314681/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(308996163/1250000000 : ℝ)|^93 ≤ (18489371717323/100000000000000 : ℝ)^77
        have hw : |(308996163/1250000000 : ℝ)|=(308996163/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-320137/2000000000 : ℝ)|^93 ≤ (2603695623/100000000000000 : ℝ)^77
        have hw : |(-320137/2000000000 : ℝ)|=(320137/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c328060_s0_21 (p : ℝ) (hpa : (91/16 : ℝ) ≤ p) (hpb : p ≤ (93/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-122170207/2500000000 : ℝ)*x 0 + (6282646637/10000000000 : ℝ)*x 1 + (-471666301/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (122170207/2500000000 : ℝ)^93 ≤ (130492327781/5000000000000 : ℝ)^77 := by
    have hnat : (122170207 : ℕ)^93*5000000000000^77 ≤ 130492327781^77*2500000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      122170207 2500000000 130492327781 5000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6282646637/10000000000 : ℝ)^93 ≤ (57042459935431/100000000000000 : ℝ)^77 := by
    have hnat : (6282646637 : ℕ)^93*100000000000000^77 ≤ 57042459935431^77*10000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6282646637 10000000000 57042459935431 100000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (471666301/1000000000 : ℝ)^93 ≤ (40347693499573/100000000000000 : ℝ)^77 := by
    have hnat : (471666301 : ℕ)^93*100000000000000^77 ≤ 40347693499573^77*1000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      471666301 1000000000 40347693499573 100000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (93/16 : ℝ)) 93 77 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-122170207/2500000000 : ℝ), (6282646637/10000000000 : ℝ), (-471666301/1000000000 : ℝ)] ![(130492327781/5000000000000 : ℝ), (57042459935431/100000000000000 : ℝ), (40347693499573/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-122170207/2500000000 : ℝ)|^93 ≤ (130492327781/5000000000000 : ℝ)^77
        have hw : |(-122170207/2500000000 : ℝ)|=(122170207/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6282646637/10000000000 : ℝ)|^93 ≤ (57042459935431/100000000000000 : ℝ)^77
        have hw : |(6282646637/10000000000 : ℝ)|=(6282646637/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-471666301/1000000000 : ℝ)|^93 ≤ (40347693499573/100000000000000 : ℝ)^77
        have hw : |(-471666301/1000000000 : ℝ)|=(471666301/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c328060_s0_22 (p : ℝ) (hpa : (91/16 : ℝ) ≤ p) (hpb : p ≤ (93/16 : ℝ)) (x : Fin 3 → ℝ) :
    (6661214751/10000000000 : ℝ)*x 0 + (-433624707/5000000000 : ℝ)*x 1 + (-404976023/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6661214751/10000000000 : ℝ)^93 ≤ (30609710219121/50000000000000 : ℝ)^77 := by
    have hnat : (6661214751 : ℕ)^93*50000000000000^77 ≤ 30609710219121^77*10000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6661214751 10000000000 30609710219121 50000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (433624707/5000000000 : ℝ)^93 ≤ (40765112571/781250000000 : ℝ)^77 := by
    have hnat : (433624707 : ℕ)^93*781250000000^77 ≤ 40765112571^77*5000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      433624707 5000000000 40765112571 781250000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (404976023/1000000000 : ℝ)^93 ≤ (33562645129497/100000000000000 : ℝ)^77 := by
    have hnat : (404976023 : ℕ)^93*100000000000000^77 ≤ 33562645129497^77*1000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      404976023 1000000000 33562645129497 100000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (93/16 : ℝ)) 93 77 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6661214751/10000000000 : ℝ), (-433624707/5000000000 : ℝ), (-404976023/1000000000 : ℝ)] ![(30609710219121/50000000000000 : ℝ), (40765112571/781250000000 : ℝ), (33562645129497/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6661214751/10000000000 : ℝ)|^93 ≤ (30609710219121/50000000000000 : ℝ)^77
        have hw : |(6661214751/10000000000 : ℝ)|=(6661214751/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-433624707/5000000000 : ℝ)|^93 ≤ (40765112571/781250000000 : ℝ)^77
        have hw : |(-433624707/5000000000 : ℝ)|=(433624707/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-404976023/1000000000 : ℝ)|^93 ≤ (33562645129497/100000000000000 : ℝ)^77
        have hw : |(-404976023/1000000000 : ℝ)|=(404976023/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c328060_s0_23 (p : ℝ) (hpa : (91/16 : ℝ) ≤ p) (hpb : p ≤ (93/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1281859203/10000000000 : ℝ)*x 0 + (8033011277/10000000000 : ℝ)*x 1 + (206504189/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1281859203/10000000000 : ℝ)^93 ≤ (2091204505687/25000000000000 : ℝ)^77 := by
    have hnat : (1281859203 : ℕ)^93*25000000000000^77 ≤ 2091204505687^77*10000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1281859203 10000000000 2091204505687 25000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (8033011277/10000000000 : ℝ)^93 ≤ (76756090194607/100000000000000 : ℝ)^77 := by
    have hnat : (8033011277 : ℕ)^93*100000000000000^77 ≤ 76756090194607^77*10000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8033011277 10000000000 76756090194607 100000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (206504189/1000000000 : ℝ)^93 ≤ (2975818354259/20000000000000 : ℝ)^77 := by
    have hnat : (206504189 : ℕ)^93*20000000000000^77 ≤ 2975818354259^77*1000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      206504189 1000000000 2975818354259 20000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (93/16 : ℝ)) 93 77 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1281859203/10000000000 : ℝ), (8033011277/10000000000 : ℝ), (206504189/1000000000 : ℝ)] ![(2091204505687/25000000000000 : ℝ), (76756090194607/100000000000000 : ℝ), (2975818354259/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1281859203/10000000000 : ℝ)|^93 ≤ (2091204505687/25000000000000 : ℝ)^77
        have hw : |(1281859203/10000000000 : ℝ)|=(1281859203/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(8033011277/10000000000 : ℝ)|^93 ≤ (76756090194607/100000000000000 : ℝ)^77
        have hw : |(8033011277/10000000000 : ℝ)|=(8033011277/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(206504189/1000000000 : ℝ)|^93 ≤ (2975818354259/20000000000000 : ℝ)^77
        have hw : |(206504189/1000000000 : ℝ)|=(206504189/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c328060_s0_27 (p : ℝ) (hpa : (91/16 : ℝ) ≤ p) (hpb : p ≤ (93/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4596652619/5000000000 : ℝ)*x 0 + (358155367/2500000000 : ℝ)*x 1 + (-6158539/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4596652619/5000000000 : ℝ)^93 ≤ (45170134522013/50000000000000 : ℝ)^77 := by
    have hnat : (4596652619 : ℕ)^93*50000000000000^77 ≤ 45170134522013^77*5000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4596652619 5000000000 45170134522013 50000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (358155367/2500000000 : ℝ)^93 ≤ (4783570192897/50000000000000 : ℝ)^77 := by
    have hnat : (358155367 : ℕ)^93*50000000000000^77 ≤ 4783570192897^77*2500000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      358155367 2500000000 4783570192897 50000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6158539/2000000000 : ℝ)^93 ≤ (92590558347/100000000000000 : ℝ)^77 := by
    have hnat : (6158539 : ℕ)^93*100000000000000^77 ≤ 92590558347^77*2000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6158539 2000000000 92590558347 100000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (93/16 : ℝ)) 93 77 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4596652619/5000000000 : ℝ), (358155367/2500000000 : ℝ), (-6158539/2000000000 : ℝ)] ![(45170134522013/50000000000000 : ℝ), (4783570192897/50000000000000 : ℝ), (92590558347/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4596652619/5000000000 : ℝ)|^93 ≤ (45170134522013/50000000000000 : ℝ)^77
        have hw : |(4596652619/5000000000 : ℝ)|=(4596652619/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(358155367/2500000000 : ℝ)|^93 ≤ (4783570192897/50000000000000 : ℝ)^77
        have hw : |(358155367/2500000000 : ℝ)|=(358155367/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-6158539/2000000000 : ℝ)|^93 ≤ (92590558347/100000000000000 : ℝ)^77
        have hw : |(-6158539/2000000000 : ℝ)|=(6158539/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c328060_s1_0 (p : ℝ) (hpa : (91/16 : ℝ) ≤ p) (hpb : p ≤ (93/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-190211489/1000000000 : ℝ)*x 0 + (3819984623/10000000000 : ℝ)*x 1 + (-6118784799/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (190211489/1000000000 : ℝ)^93 ≤ (13473106952021/100000000000000 : ℝ)^77 := by
    have hnat : (190211489 : ℕ)^93*100000000000000^77 ≤ 13473106952021^77*1000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      190211489 1000000000 13473106952021 100000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3819984623/10000000000 : ℝ)^93 ≤ (15638218584961/50000000000000 : ℝ)^77 := by
    have hnat : (3819984623 : ℕ)^93*50000000000000^77 ≤ 15638218584961^77*10000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3819984623 10000000000 15638218584961 50000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6118784799/10000000000 : ℝ)^93 ≤ (11050091172269/20000000000000 : ℝ)^77 := by
    have hnat : (6118784799 : ℕ)^93*20000000000000^77 ≤ 11050091172269^77*10000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6118784799 10000000000 11050091172269 20000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (93/16 : ℝ)) 93 77 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-190211489/1000000000 : ℝ), (3819984623/10000000000 : ℝ), (-6118784799/10000000000 : ℝ)] ![(13473106952021/100000000000000 : ℝ), (15638218584961/50000000000000 : ℝ), (11050091172269/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-190211489/1000000000 : ℝ)|^93 ≤ (13473106952021/100000000000000 : ℝ)^77
        have hw : |(-190211489/1000000000 : ℝ)|=(190211489/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3819984623/10000000000 : ℝ)|^93 ≤ (15638218584961/50000000000000 : ℝ)^77
        have hw : |(3819984623/10000000000 : ℝ)|=(3819984623/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-6118784799/10000000000 : ℝ)|^93 ≤ (11050091172269/20000000000000 : ℝ)^77
        have hw : |(-6118784799/10000000000 : ℝ)|=(6118784799/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c328060_s1_1 (p : ℝ) (hpa : (91/16 : ℝ) ≤ p) (hpb : p ≤ (93/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4506504627/10000000000 : ℝ)*x 0 + (-2587153331/10000000000 : ℝ)*x 1 + (-612849049/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4506504627/10000000000 : ℝ)^93 ≤ (381865508907/1000000000000 : ℝ)^77 := by
    have hnat : (4506504627 : ℕ)^93*1000000000000^77 ≤ 381865508907^77*10000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4506504627 10000000000 381865508907 1000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2587153331/10000000000 : ℝ)^93 ≤ (19534899916261/100000000000000 : ℝ)^77 := by
    have hnat : (2587153331 : ℕ)^93*100000000000000^77 ≤ 19534899916261^77*10000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2587153331 10000000000 19534899916261 100000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (612849049/1250000000 : ℝ)^93 ≤ (338228393367/800000000000 : ℝ)^77 := by
    have hnat : (612849049 : ℕ)^93*800000000000^77 ≤ 338228393367^77*1250000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      612849049 1250000000 338228393367 800000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (93/16 : ℝ)) 93 77 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4506504627/10000000000 : ℝ), (-2587153331/10000000000 : ℝ), (-612849049/1250000000 : ℝ)] ![(381865508907/1000000000000 : ℝ), (19534899916261/100000000000000 : ℝ), (338228393367/800000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4506504627/10000000000 : ℝ)|^93 ≤ (381865508907/1000000000000 : ℝ)^77
        have hw : |(4506504627/10000000000 : ℝ)|=(4506504627/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2587153331/10000000000 : ℝ)|^93 ≤ (19534899916261/100000000000000 : ℝ)^77
        have hw : |(-2587153331/10000000000 : ℝ)|=(2587153331/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-612849049/1250000000 : ℝ)|^93 ≤ (338228393367/800000000000 : ℝ)^77
        have hw : |(-612849049/1250000000 : ℝ)|=(612849049/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c328060_s1_2 (p : ℝ) (hpa : (91/16 : ℝ) ≤ p) (hpb : p ≤ (93/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4575638319/10000000000 : ℝ)*x 0 + (173089627/312500000 : ℝ)*x 1 + (217740857/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4575638319/10000000000 : ℝ)^93 ≤ (7779043332623/20000000000000 : ℝ)^77 := by
    have hnat : (4575638319 : ℕ)^93*20000000000000^77 ≤ 7779043332623^77*10000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4575638319 10000000000 7779043332623 20000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (173089627/312500000 : ℝ)^93 ≤ (4898982721381/10000000000000 : ℝ)^77 := by
    have hnat : (173089627 : ℕ)^93*10000000000000^77 ≤ 4898982721381^77*312500000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      173089627 312500000 4898982721381 10000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (217740857/1250000000 : ℝ)^93 ≤ (6057478057237/50000000000000 : ℝ)^77 := by
    have hnat : (217740857 : ℕ)^93*50000000000000^77 ≤ 6057478057237^77*1250000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      217740857 1250000000 6057478057237 50000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (93/16 : ℝ)) 93 77 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4575638319/10000000000 : ℝ), (173089627/312500000 : ℝ), (217740857/1250000000 : ℝ)] ![(7779043332623/20000000000000 : ℝ), (4898982721381/10000000000000 : ℝ), (6057478057237/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4575638319/10000000000 : ℝ)|^93 ≤ (7779043332623/20000000000000 : ℝ)^77
        have hw : |(4575638319/10000000000 : ℝ)|=(4575638319/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(173089627/312500000 : ℝ)|^93 ≤ (4898982721381/10000000000000 : ℝ)^77
        have hw : |(173089627/312500000 : ℝ)|=(173089627/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(217740857/1250000000 : ℝ)|^93 ≤ (6057478057237/50000000000000 : ℝ)^77
        have hw : |(217740857/1250000000 : ℝ)|=(217740857/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c328060_s1_6 (p : ℝ) (hpa : (91/16 : ℝ) ≤ p) (hpb : p ≤ (93/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3447869317/5000000000 : ℝ)*x 0 + (36999727/100000000 : ℝ)*x 1 + (-491767301/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3447869317/5000000000 : ℝ)^93 ≤ (63832100922197/100000000000000 : ℝ)^77 := by
    have hnat : (3447869317 : ℕ)^93*100000000000000^77 ≤ 63832100922197^77*5000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3447869317 5000000000 63832100922197 100000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (36999727/100000000 : ℝ)^93 ≤ (120374231659/400000000000 : ℝ)^77 := by
    have hnat : (36999727 : ℕ)^93*400000000000^77 ≤ 120374231659^77*100000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      36999727 100000000 120374231659 400000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (491767301/5000000000 : ℝ)^93 ≤ (6074341157873/100000000000000 : ℝ)^77 := by
    have hnat : (491767301 : ℕ)^93*100000000000000^77 ≤ 6074341157873^77*5000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      491767301 5000000000 6074341157873 100000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (93/16 : ℝ)) 93 77 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3447869317/5000000000 : ℝ), (36999727/100000000 : ℝ), (-491767301/5000000000 : ℝ)] ![(63832100922197/100000000000000 : ℝ), (120374231659/400000000000 : ℝ), (6074341157873/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3447869317/5000000000 : ℝ)|^93 ≤ (63832100922197/100000000000000 : ℝ)^77
        have hw : |(3447869317/5000000000 : ℝ)|=(3447869317/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(36999727/100000000 : ℝ)|^93 ≤ (120374231659/400000000000 : ℝ)^77
        have hw : |(36999727/100000000 : ℝ)|=(36999727/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-491767301/5000000000 : ℝ)|^93 ≤ (6074341157873/100000000000000 : ℝ)^77
        have hw : |(-491767301/5000000000 : ℝ)|=(491767301/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c328060 (p : ℝ) (hpa : (91/16 : ℝ) ≤ p) (hpb : p ≤ (93/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (8679/4000 : ℝ) (80697/50000 : ℝ) (82433/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, false]]) : False := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (82433/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (82433/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (82433/100000 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (82433/100000 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (82433/100000 : ℝ)*P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (82433/100000 : ℝ)*P 2 ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((-1 : ℝ)*(X 0 1+X 1 1)) ∧ ((-1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((-1 : ℝ)*pair X 2 1) ∧ ((-1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base5 : ((1 : ℝ)*N 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 2]
  have base7 : ((1 : ℝ)*T) ≤ (80697/50000 : ℝ) := by
    linarith only [f.Tcap]
  have base11 : ((1 : ℝ)*X 0 1+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 1).2]
  have base12 : ((-1 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 2).1]
  have base21 : ((1 : ℝ)*X 2 0+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 0).2]
  have base25 : ((1 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 2).2]
  have base27 : ((1 : ℝ)*X 0 0+(1 : ℝ)*X 1 0+(1 : ℝ)*X 2 0+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [(f.column 0).2]
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base43 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 2+(1 : ℝ)*P 1) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 1,f.sum]
  have base49 : ((-1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
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
  have s0_pow0 : (1 : ℝ) ^ (91/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^91 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^91*1^16 ≤ 1^16*1^91 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 91 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 91 16 (by norm_num) hpowers
    exact h
  have s0_corner0a : (2 : ℝ) ≤ (11296095383713331/10000000000000000 : ℝ) ^ (91/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (11296095383713331/10000000000000000 : ℝ)^91 := by
      have hnat : (2 : ℕ)^16*10000000000000000^91 ≤ 11296095383713331^91*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 11296095383713331 10000000000000000 16 91 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11296095383713331/10000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 91 16 (by norm_num) hpowers
    exact h
  have s0_corner0b : (3 : ℝ) ≤ (12130800245449181/10000000000000000 : ℝ) ^ (91/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (12130800245449181/10000000000000000 : ℝ)^91 := by
      have hnat : (3 : ℕ)^16*10000000000000000^91 ≤ 12130800245449181^91*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 12130800245449181 10000000000000000 16 91 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12130800245449181/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 91 16 (by norm_num) hpowers
    exact h
  have major_s0_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(1296095383713331/10000000000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(16694097234717/200000000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (91/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (1296095383713331/10000000000000000 : ℝ)) (beta := (16694097234717/200000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow0,s0_corner0a]) (by linarith only [s0_pow0,s0_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, false]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (1 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order0.2.2])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(1296095383713331/10000000000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(16694097234717/200000000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow1 : (1 : ℝ) ^ (91/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^91 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^91*1^16 ≤ 1^16*1^91 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 91 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 91 16 (by norm_num) hpowers
    exact h
  have s0_corner1a : (2 : ℝ) ≤ (11296095383713331/10000000000000000 : ℝ) ^ (91/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (11296095383713331/10000000000000000 : ℝ)^91 := by
      have hnat : (2 : ℕ)^16*10000000000000000^91 ≤ 11296095383713331^91*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 11296095383713331 10000000000000000 16 91 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11296095383713331/10000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 91 16 (by norm_num) hpowers
    exact h
  have s0_corner1b : (3 : ℝ) ≤ (12130800245449181/10000000000000000 : ℝ) ^ (91/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (12130800245449181/10000000000000000 : ℝ)^91 := by
      have hnat : (3 : ℕ)^16*10000000000000000^91 ≤ 12130800245449181^91*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 12130800245449181 10000000000000000 16 91 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12130800245449181/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 91 16 (by norm_num) hpowers
    exact h
  have major_s0_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(1296095383713331/10000000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(16694097234717/200000000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (91/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (1296095383713331/10000000000000000 : ℝ)) (beta := (16694097234717/200000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow1,s0_corner1a]) (by linarith only [s0_pow1,s0_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, false]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (1 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order1.2.2])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(1296095383713331/10000000000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(16694097234717/200000000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow2 : (1 : ℝ) ^ (91/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^91 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^91*1^16 ≤ 1^16*1^91 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 91 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 91 16 (by norm_num) hpowers
    exact h
  have s0_corner2a : (2 : ℝ) ≤ (11296095383713331/10000000000000000 : ℝ) ^ (91/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (11296095383713331/10000000000000000 : ℝ)^91 := by
      have hnat : (2 : ℕ)^16*10000000000000000^91 ≤ 11296095383713331^91*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 11296095383713331 10000000000000000 16 91 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11296095383713331/10000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 91 16 (by norm_num) hpowers
    exact h
  have s0_corner2b : (3 : ℝ) ≤ (12130800245449181/10000000000000000 : ℝ) ^ (91/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (12130800245449181/10000000000000000 : ℝ)^91 := by
      have hnat : (3 : ℕ)^16*10000000000000000^91 ≤ 12130800245449181^91*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 12130800245449181 10000000000000000 16 91 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12130800245449181/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 91 16 (by norm_num) hpowers
    exact h
  have major_s0_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(1296095383713331/10000000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(16694097234717/200000000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (91/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (1296095383713331/10000000000000000 : ℝ)) (beta := (16694097234717/200000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow2,s0_corner2a]) (by linarith only [s0_pow2,s0_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, false]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (1 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order2.2.2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(1296095383713331/10000000000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(16694097234717/200000000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s0_0 : ((-986273/8000000 : ℝ)*X 0 0+(2242896169/5000000000 : ℝ)*X 0 1+(-3004035157/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c328060_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_1 : ((2242896229/5000000000 : ℝ)*X 1 0+(-1232841047/10000000000 : ℝ)*X 1 1+(-6008070347/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c328060_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_7 : ((-866048933/5000000000 : ℝ)*X 0 0+(1435027549/10000000000 : ℝ)*X 0 1+(-510847359/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c328060_s0_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_8 : ((2452478397/10000000000 : ℝ)*X 1 0+(-148571051/2500000000 : ℝ)*X 1 1+(-204339013/250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c328060_s0_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_9 : ((214996739/1000000000 : ℝ)*X 2 0+(3975698411/5000000000 : ℝ)*X 2 1+(1307018889/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c328060_s0_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_13 : ((4197462651/10000000000 : ℝ)*X 0 0+(874449191/1250000000 : ℝ)*X 0 1+(-1889393/10000000000 : ℝ)*X 0 2+(4197462651/10000000000 : ℝ)*X 1 0+(874449191/1250000000 : ℝ)*X 1 1+(-1889393/10000000000 : ℝ)*X 1 2+(4197462651/10000000000 : ℝ)*X 2 0+(874449191/1250000000 : ℝ)*X 2 1+(-1889393/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c328060_s0_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_14 : ((-167522951/2000000000 : ℝ)*X 0 0+(521557281/2500000000 : ℝ)*X 0 1+(-8307326931/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c328060_s0_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_15 : ((940644603/10000000000 : ℝ)*X 1 0+(-499890973/2500000000 : ℝ)*X 1 1+(-8307325133/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c328060_s0_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_16 : ((6621654931/10000000000 : ℝ)*X 2 0+(3586388103/10000000000 : ℝ)*X 2 1+(1515317289/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c328060_s0_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_20 : ((4221314681/5000000000 : ℝ)*X 0 0+(308996163/1250000000 : ℝ)*X 0 1+(-320137/2000000000 : ℝ)*X 0 2+(4221314681/5000000000 : ℝ)*X 1 0+(308996163/1250000000 : ℝ)*X 1 1+(-320137/2000000000 : ℝ)*X 1 2+(4221314681/5000000000 : ℝ)*X 2 0+(308996163/1250000000 : ℝ)*X 2 1+(-320137/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c328060_s0_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_21 : ((-122170207/2500000000 : ℝ)*X 0 0+(6282646637/10000000000 : ℝ)*X 0 1+(-471666301/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c328060_s0_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_22 : ((6661214751/10000000000 : ℝ)*X 1 0+(-433624707/5000000000 : ℝ)*X 1 1+(-404976023/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c328060_s0_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_23 : ((1281859203/10000000000 : ℝ)*X 2 0+(8033011277/10000000000 : ℝ)*X 2 1+(206504189/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c328060_s0_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_27 : ((4596652619/5000000000 : ℝ)*X 0 0+(358155367/2500000000 : ℝ)*X 0 1+(-6158539/2000000000 : ℝ)*X 0 2+(4596652619/5000000000 : ℝ)*X 1 0+(358155367/2500000000 : ℝ)*X 1 1+(-6158539/2000000000 : ℝ)*X 1 2+(4596652619/5000000000 : ℝ)*X 2 0+(358155367/2500000000 : ℝ)*X 2 1+(-6158539/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c328060_s0_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s0_0 : (0 : ℝ) ≤ ((62417/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(62417/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (48625947870235089/2500000000000000000000 : ℝ) := by norm_num
    linear_combination (122682526793/500000000000 : ℝ)*(base5) + (604334697609/500000000000 : ℝ)*(base7) + (2111069/1000000000000 : ℝ)*(base59) + (777748316037/500000000000 : ℝ)*(major_s0_0) + (777748316037/500000000000 : ℝ)*(major_s0_1) + (777748316037/500000000000 : ℝ)*(major_s0_2) + (4224067/500000000000 : ℝ)*(sp_s0_0) + (2026847/250000000000 : ℝ)*(sp_s0_1) + (1743780745727/1000000000000 : ℝ)*(sp_s0_7) + (1743822790451/1000000000000 : ℝ)*(sp_s0_8) + (994605278127/500000000000 : ℝ)*(sp_s0_9) + (210025707301/125000000000 : ℝ)*(sp_s0_13) + (56308807/1000000000000 : ℝ)*(sp_s0_14) + (1460483/100000000000 : ℝ)*(sp_s0_15) + (89612664597/125000000000 : ℝ)*(f.failure) + (435961375667/250000000000 : ℝ)*(f.sum) + (82934637739247/2500000000000000000000000000 : ℝ)*base63 + (57698173326529/100000000000000000000000000 : ℝ)*base64 + (24184100506529/100000000000000000000000000 : ℝ)*base67 + (2748068226510753/5000000000000000000000000000 : ℝ)*base68 + (255740073162797/5000000000000000000000000000 : ℝ)*base71 + (107481853156529/100000000000000000000000000 : ℝ)*base73 + (1779797136010753/5000000000000000000000000000 : ℝ)*base74 + (1073162908010753/5000000000000000000000000000 : ℝ)*base76 + (4007993053471/50000000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base83 + (363/500000000000000 : ℝ)*base87 + (363/500000000000000 : ℝ)*base89 + (363/500000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s0_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(249/400 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(249/400 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (30109529218088171790237/5000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (601114702149/500000000000 : ℝ)*(base7) + (1927/200000000000 : ℝ)*(base21) + (14701/500000000000 : ℝ)*(base39) + (1527/15625000000 : ℝ)*(base49) + (2824287433/40000000000 : ℝ)*(base60) + (1483149576459/1000000000000 : ℝ)*(major_s0_0) + (1483149576459/1000000000000 : ℝ)*(major_s0_1) + (1483149576459/1000000000000 : ℝ)*(major_s0_2) + (1693553/62500000000 : ℝ)*(sp_s0_7) + (817968427721/500000000000 : ℝ)*(sp_s0_14) + (163596395229/100000000000 : ℝ)*(sp_s0_15) + (817981971327/500000000000 : ℝ)*(sp_s0_16) + (188577696121/100000000000 : ℝ)*(sp_s0_20) + (10261481/1000000000000 : ℝ)*(sp_s0_27) + (683557818393/1000000000000 : ℝ)*(f.failure) + (163596395229/100000000000 : ℝ)*(f.sum) + (1403346887925071/5000000000000000000000000000 : ℝ)*base62 + (54724266887103/200000000000000000000000000 : ℝ)*base64 + (76158148092897/200000000000000000000000000 : ℝ)*base66 + (954017045925071/10000000000000000000000000000 : ℝ)*base68 + (3700182982280221/10000000000000000000000000000 : ℝ)*base70 + (73338044972897/200000000000000000000000000 : ℝ)*base72 + (10123646950074929/10000000000000000000000000000 : ℝ)*base75 + (4119342012074929/10000000000000000000000000000 : ℝ)*base77 + (68134687882897/100000000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base84 + (3153/4000000000000000 : ℝ)*base86 + (3153/4000000000000000 : ℝ)*base88 + (3153/4000000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s0_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-51781/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-51781/100000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (6415850882603521105137/1000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (913346248449/1000000000000 : ℝ)*(base7) + (123972163603/1000000000000 : ℝ)*(base39) + (4483811/1000000000000 : ℝ)*(base43) + (966771/1000000000000 : ℝ)*(base50) + (47720692383/31250000000 : ℝ)*(major_s0_0) + (305411534489/200000000000 : ℝ)*(major_s0_1) + (47720692383/31250000000 : ℝ)*(major_s0_2) + (3124781/500000000000 : ℝ)*(sp_s0_0) + (10603543/250000000000 : ℝ)*(sp_s0_9) + (243467/62500000000 : ℝ)*(sp_s0_20) + (1858953063867/1000000000000 : ℝ)*(sp_s0_21) + (1858963797239/1000000000000 : ℝ)*(sp_s0_22) + (1858916899257/1000000000000 : ℝ)*(sp_s0_23) + (202142339361/125000000000 : ℝ)*(sp_s0_27) + (703796361911/1000000000000 : ℝ)*(f.failure) + (1858963797239/1000000000000 : ℝ)*(f.sum) + (519218821886969/10000000000000000000000000000 : ℝ)*base62 + (497273876243/3125000000000000000000000 : ℝ)*base64 + (8434188126613/40000000000000000000000000 : ℝ)*base67 + (143813635476523/312500000000000000000000000 : ℝ)*base69 + (1951681539723/312500000000000000000000000 : ℝ)*base71 + (3961753408139/6250000000000000000000000 : ℝ)*base72 + (43959496227141/2000000000000000000000000000 : ℝ)*base74 + (86379644148477/312500000000000000000000000 : ℝ)*base76 + (46646752947383/200000000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base81 + (1/1000000000000 : ℝ)*base85 + (1569/4000000000000000 : ℝ)*base87 + (1569/4000000000000000 : ℝ)*base89 + (1569/4000000000000000 : ℝ)*base91 + hcertificate_margin
  have s1_pow0 : (62417/100000 : ℝ) ^ (91/16 : ℝ) ≤ (685149259087623491/10000000000000000000 : ℝ) := by
    have hpowers : (62417/100000 : ℝ)^91 ≤ (685149259087623491/10000000000000000000 : ℝ)^16 := by
      have hnat : (62417 : ℕ)^91*10000000000000000000^16 ≤ 685149259087623491^16*100000^91 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        62417 100000 685149259087623491 10000000000000000000 91 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (62417/100000 : ℝ)) (X := (685149259087623491/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 91 16 (by norm_num) hpowers
    exact h
  have s1_corner0a : (10685149259087623491/10000000000000000000 : ℝ) ≤ (1011719973717231/1000000000000000 : ℝ) ^ (91/16 : ℝ) := by
    have hpowers : (10685149259087623491/10000000000000000000 : ℝ)^16 ≤ (1011719973717231/1000000000000000 : ℝ)^91 := by
      have hnat : (10685149259087623491 : ℕ)^16*1000000000000000^91 ≤ 1011719973717231^91*10000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10685149259087623491 10000000000000000000 1011719973717231 1000000000000000 16 91 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1011719973717231/1000000000000000 : ℝ)) (X := (10685149259087623491/10000000000000000000 : ℝ)) (by norm_num) 91 16 (by norm_num) hpowers
    exact h
  have s1_corner0b : (5685149259087623491/5000000000000000000 : ℝ) ≤ (1278545110006653/1250000000000000 : ℝ) ^ (91/16 : ℝ) := by
    have hpowers : (5685149259087623491/5000000000000000000 : ℝ)^16 ≤ (1278545110006653/1250000000000000 : ℝ)^91 := by
      have hnat : (5685149259087623491 : ℕ)^16*1250000000000000^91 ≤ 1278545110006653^91*5000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5685149259087623491 5000000000000000000 1278545110006653 1250000000000000 16 91 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1278545110006653/1250000000000000 : ℝ)) (X := (5685149259087623491/5000000000000000000 : ℝ)) (by norm_num) 91 16 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(11719973717231/624170000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(55580571440457/3120850000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (91/16 : ℝ)) (rho := (62417/100000 : ℝ)) (alpha := (11719973717231/624170000000000 : ℝ)) (beta := (55580571440457/3120850000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, false]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (62417/100000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(11719973717231/624170000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(55580571440457/3120850000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (249/400 : ℝ) ^ (91/16 : ℝ) ≤ (6747883653814005051/100000000000000000000 : ℝ) := by
    have hpowers : (249/400 : ℝ)^91 ≤ (6747883653814005051/100000000000000000000 : ℝ)^16 := by
      have hnat : (249 : ℕ)^91*100000000000000000000^16 ≤ 6747883653814005051^16*400^91 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        249 400 6747883653814005051 100000000000000000000 91 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (249/400 : ℝ)) (X := (6747883653814005051/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 91 16 (by norm_num) hpowers
    exact h
  have s1_corner1a : (106747883653814005051/100000000000000000000 : ℝ) ≤ (10115474180832437/10000000000000000 : ℝ) ^ (91/16 : ℝ) := by
    have hpowers : (106747883653814005051/100000000000000000000 : ℝ)^16 ≤ (10115474180832437/10000000000000000 : ℝ)^91 := by
      have hnat : (106747883653814005051 : ℕ)^16*10000000000000000^91 ≤ 10115474180832437^91*100000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        106747883653814005051 100000000000000000000 10115474180832437 10000000000000000 16 91 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10115474180832437/10000000000000000 : ℝ)) (X := (106747883653814005051/100000000000000000000 : ℝ)) (by norm_num) 91 16 (by norm_num) hpowers
    exact h
  have s1_corner1b : (56747883653814005051/50000000000000000000 : ℝ) ≤ (5112540468217863/5000000000000000 : ℝ) ^ (91/16 : ℝ) := by
    have hpowers : (56747883653814005051/50000000000000000000 : ℝ)^16 ≤ (5112540468217863/5000000000000000 : ℝ)^91 := by
      have hnat : (56747883653814005051 : ℕ)^16*5000000000000000^91 ≤ 5112540468217863^91*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        56747883653814005051 50000000000000000000 5112540468217863 5000000000000000 16 91 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5112540468217863/5000000000000000 : ℝ)) (X := (56747883653814005051/50000000000000000000 : ℝ)) (by norm_num) 91 16 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(115474180832437/6225000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(109606755603289/6225000000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (91/16 : ℝ)) (rho := (249/400 : ℝ)) (alpha := (115474180832437/6225000000000000 : ℝ)) (beta := (109606755603289/6225000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, false]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (249/400 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(115474180832437/6225000000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(109606755603289/6225000000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (51781/100000 : ℝ) ^ (91/16 : ℝ) ≤ (591949077621587461/25000000000000000000 : ℝ) := by
    have hpowers : (51781/100000 : ℝ)^91 ≤ (591949077621587461/25000000000000000000 : ℝ)^16 := by
      have hnat : (51781 : ℕ)^91*25000000000000000000^16 ≤ 591949077621587461^16*100000^91 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        51781 100000 591949077621587461 25000000000000000000 91 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (51781/100000 : ℝ)) (X := (591949077621587461/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 91 16 (by norm_num) hpowers
    exact h
  have s1_corner2a : (25591949077621587461/25000000000000000000 : ℝ) ≤ (1004123111986583/1000000000000000 : ℝ) ^ (91/16 : ℝ) := by
    have hpowers : (25591949077621587461/25000000000000000000 : ℝ)^16 ≤ (1004123111986583/1000000000000000 : ℝ)^91 := by
      have hnat : (25591949077621587461 : ℕ)^16*1000000000000000^91 ≤ 1004123111986583^91*25000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25591949077621587461 25000000000000000000 1004123111986583 1000000000000000 16 91 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1004123111986583/1000000000000000 : ℝ)) (X := (25591949077621587461/25000000000000000000 : ℝ)) (by norm_num) 91 16 (by norm_num) hpowers
    exact h
  have s1_corner2b : (13091949077621587461/12500000000000000000 : ℝ) ≤ (1260210447622519/1250000000000000 : ℝ) ^ (91/16 : ℝ) := by
    have hpowers : (13091949077621587461/12500000000000000000 : ℝ)^16 ≤ (1260210447622519/1250000000000000 : ℝ)^91 := by
      have hnat : (13091949077621587461 : ℕ)^16*1250000000000000^91 ≤ 1260210447622519^91*12500000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        13091949077621587461 12500000000000000000 1260210447622519 1250000000000000 16 91 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1260210447622519/1250000000000000 : ℝ)) (X := (13091949077621587461/12500000000000000000 : ℝ)) (by norm_num) 91 16 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(4123111986583/517810000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(20226230557161/2589050000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (91/16 : ℝ)) (rho := (51781/100000 : ℝ)) (alpha := (4123111986583/517810000000000 : ℝ)) (beta := (20226230557161/2589050000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, false]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (51781/100000 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(4123111986583/517810000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(20226230557161/2589050000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-190211489/1000000000 : ℝ)*X 0 0+(3819984623/10000000000 : ℝ)*X 0 1+(-6118784799/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c328060_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_1 : ((4506504627/10000000000 : ℝ)*X 1 0+(-2587153331/10000000000 : ℝ)*X 1 1+(-612849049/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c328060_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((4575638319/10000000000 : ℝ)*X 2 0+(173089627/312500000 : ℝ)*X 2 1+(217740857/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c328060_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_6 : ((3447869317/5000000000 : ℝ)*X 0 0+(36999727/100000000 : ℝ)*X 0 1+(-491767301/5000000000 : ℝ)*X 0 2+(3447869317/5000000000 : ℝ)*X 1 0+(36999727/100000000 : ℝ)*X 1 1+(-491767301/5000000000 : ℝ)*X 1 2+(3447869317/5000000000 : ℝ)*X 2 0+(36999727/100000000 : ℝ)*X 2 1+(-491767301/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c328060_s1_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have hsep : (-20037/2000 : ℝ) < ((-8679/4000 : ℝ)*P 0+(-8679/4000 : ℝ)*P 1+(-8679/4000 : ℝ)*P 2+(1 : ℝ)*T) := by
    have hcertificate_margin : (-20037/2000 : ℝ) < (-3342689605295255576681174732368174449/335321522738750000000000000000000000 : ℝ) := by norm_num
    linear_combination (14583/500000000000 : ℝ)*(base11) + (65327/1000000000000 : ℝ)*(base12) + (13549/1000000000000 : ℝ)*(base25) + (36937/500000000000 : ℝ)*(base27) + (40362033591/100000000000 : ℝ)*(base39) + (21049/500000000000 : ℝ)*(base40) + (23863/200000000000 : ℝ)*(base43) + (32091928001/62500000000 : ℝ)*(base59) + (8679/4000 : ℝ)*(major_s1_0) + (433949976137/200000000000 : ℝ)*(major_s1_1) + (8679/4000 : ℝ)*(major_s1_2) + (3322869905981/1000000000000 : ℝ)*(sp_s1_0) + (3322870119789/1000000000000 : ℝ)*(sp_s1_1) + (132914799477/40000000000 : ℝ)*(sp_s1_2) + (499999963063/500000000000 : ℝ)*(sp_s1_6) + (3322870119789/1000000000000 : ℝ)*(f.sum) + (9533743371471740311/64467345000000000000000000000000 : ℝ)*base62 + (275779806513497/517810000000000000000000000 : ℝ)*base65 + (242868525254093/1245000000000000000000000000 : ℝ)*base67 + (84065816010447/517810000000000000000000000 : ℝ)*base68 + (11605040064547337243/32320146770000000000000000000000 : ℝ)*base71 + (16296850035369/31208500000000000000000000 : ℝ)*base73 + (205600858839631/1245000000000000000000000000 : ℝ)*base74 + (714099380789/3120850000000000000000000 : ℝ)*base76 + (54720308681977409281/77709165000000000000000000000000 : ℝ)*base79 + hcertificate_margin
  linarith only [hsep,f.failure]

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem collision_support_c328064_s0_0 (p : ℝ) (hpa : (91/16 : ℝ) ≤ p) (hpb : p ≤ (93/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-2893109501/10000000000 : ℝ)*x 0 + (-877354677/2500000000 : ℝ)*x 1 + (-43579319/78125000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2893109501/10000000000 : ℝ)^93 ≤ (2794799790283/12500000000000 : ℝ)^77 := by
    have hnat : (2893109501 : ℕ)^93*12500000000000^77 ≤ 2794799790283^77*10000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2893109501 10000000000 2794799790283 12500000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (877354677/2500000000 : ℝ)^93 ≤ (2823180218531/10000000000000 : ℝ)^77 := by
    have hnat : (877354677 : ℕ)^93*10000000000000^77 ≤ 2823180218531^77*2500000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      877354677 2500000000 2823180218531 10000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (43579319/78125000 : ℝ)^93 ≤ (49409799483773/100000000000000 : ℝ)^77 := by
    have hnat : (43579319 : ℕ)^93*100000000000000^77 ≤ 49409799483773^77*78125000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      43579319 78125000 49409799483773 100000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (93/16 : ℝ)) 93 77 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2893109501/10000000000 : ℝ), (-877354677/2500000000 : ℝ), (-43579319/78125000 : ℝ)] ![(2794799790283/12500000000000 : ℝ), (2823180218531/10000000000000 : ℝ), (49409799483773/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2893109501/10000000000 : ℝ)|^93 ≤ (2794799790283/12500000000000 : ℝ)^77
        have hw : |(-2893109501/10000000000 : ℝ)|=(2893109501/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-877354677/2500000000 : ℝ)|^93 ≤ (2823180218531/10000000000000 : ℝ)^77
        have hw : |(-877354677/2500000000 : ℝ)|=(877354677/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-43579319/78125000 : ℝ)|^93 ≤ (49409799483773/100000000000000 : ℝ)^77
        have hw : |(-43579319/78125000 : ℝ)|=(43579319/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c328064_s0_1 (p : ℝ) (hpa : (91/16 : ℝ) ≤ p) (hpb : p ≤ (93/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3329222231/10000000000 : ℝ)*x 0 + (5192691547/10000000000 : ℝ)*x 1 + (-3505462559/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3329222231/10000000000 : ℝ)^93 ≤ (26490450188443/100000000000000 : ℝ)^77 := by
    have hnat : (3329222231 : ℕ)^93*100000000000000^77 ≤ 26490450188443^77*10000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3329222231 10000000000 26490450188443 100000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5192691547/10000000000 : ℝ)^93 ≤ (22658090889209/50000000000000 : ℝ)^77 := by
    have hnat : (5192691547 : ℕ)^93*50000000000000^77 ≤ 22658090889209^77*10000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5192691547 10000000000 22658090889209 50000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3505462559/10000000000 : ℝ)^93 ≤ (7048342006289/25000000000000 : ℝ)^77 := by
    have hnat : (3505462559 : ℕ)^93*25000000000000^77 ≤ 7048342006289^77*10000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3505462559 10000000000 7048342006289 25000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (93/16 : ℝ)) 93 77 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3329222231/10000000000 : ℝ), (5192691547/10000000000 : ℝ), (-3505462559/10000000000 : ℝ)] ![(26490450188443/100000000000000 : ℝ), (22658090889209/50000000000000 : ℝ), (7048342006289/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3329222231/10000000000 : ℝ)|^93 ≤ (26490450188443/100000000000000 : ℝ)^77
        have hw : |(3329222231/10000000000 : ℝ)|=(3329222231/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5192691547/10000000000 : ℝ)|^93 ≤ (22658090889209/50000000000000 : ℝ)^77
        have hw : |(5192691547/10000000000 : ℝ)|=(5192691547/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3505462559/10000000000 : ℝ)|^93 ≤ (7048342006289/25000000000000 : ℝ)^77
        have hw : |(-3505462559/10000000000 : ℝ)|=(3505462559/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c328064_s0_2 (p : ℝ) (hpa : (91/16 : ℝ) ≤ p) (hpb : p ≤ (93/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3066056807/5000000000 : ℝ)*x 0 + (-3433617611/10000000000 : ℝ)*x 1 + (2317953583/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3066056807/5000000000 : ℝ)^93 ≤ (27697925966467/50000000000000 : ℝ)^77 := by
    have hnat : (3066056807 : ℕ)^93*50000000000000^77 ≤ 27697925966467^77*5000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3066056807 5000000000 27697925966467 50000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3433617611/10000000000 : ℝ)^93 ≤ (13748483608917/50000000000000 : ℝ)^77 := by
    have hnat : (3433617611 : ℕ)^93*50000000000000^77 ≤ 13748483608917^77*10000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3433617611 10000000000 13748483608917 50000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2317953583/10000000000 : ℝ)^93 ≤ (17107180832219/100000000000000 : ℝ)^77 := by
    have hnat : (2317953583 : ℕ)^93*100000000000000^77 ≤ 17107180832219^77*10000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2317953583 10000000000 17107180832219 100000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (93/16 : ℝ)) 93 77 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3066056807/5000000000 : ℝ), (-3433617611/10000000000 : ℝ), (2317953583/10000000000 : ℝ)] ![(27697925966467/50000000000000 : ℝ), (13748483608917/50000000000000 : ℝ), (17107180832219/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3066056807/5000000000 : ℝ)|^93 ≤ (27697925966467/50000000000000 : ℝ)^77
        have hw : |(3066056807/5000000000 : ℝ)|=(3066056807/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3433617611/10000000000 : ℝ)|^93 ≤ (13748483608917/50000000000000 : ℝ)^77
        have hw : |(-3433617611/10000000000 : ℝ)|=(3433617611/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2317953583/10000000000 : ℝ)|^93 ≤ (17107180832219/100000000000000 : ℝ)^77
        have hw : |(2317953583/10000000000 : ℝ)|=(2317953583/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c328064 (p : ℝ) (hpa : (91/16 : ℝ) ≤ p) (hpb : p ≤ (93/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (8679/4000 : ℝ) (80697/50000 : ℝ) (82433/100000 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, false], ![false, false, false]]) : False := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (82433/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (82433/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (82433/100000 : ℝ)*P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (82433/100000 : ℝ)*P 1 ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 0+X 2 0)) ∧ ((-1 : ℝ)*(X 0 0+X 2 0)) ≤ ((-1 : ℝ)*(X 0 2+X 2 2)) ∧ ((-1 : ℝ)*(X 0 2+X 2 2)) ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 0) ∧ ((-1 : ℝ)*pair X 1 0) ≤ ((-1 : ℝ)*pair X 1 2) ∧ ((-1 : ℝ)*pair X 1 2) ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (82433/100000 : ℝ)*P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (82433/100000 : ℝ)*P 2 ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((-1 : ℝ)*(X 0 1+X 1 1)) ∧ ((-1 : ℝ)*(X 0 1+X 1 1)) ≤ ((-1 : ℝ)*(X 0 0+X 1 0)) ∧ ((-1 : ℝ)*(X 0 0+X 1 0)) ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((-1 : ℝ)*pair X 2 1) ∧ ((-1 : ℝ)*pair X 2 1) ≤ ((-1 : ℝ)*pair X 2 0) ∧ ((-1 : ℝ)*pair X 2 0) ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base1 : ((1 : ℝ)*N 0+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 0]
  have base7 : ((1 : ℝ)*T) ≤ (80697/50000 : ℝ) := by
    linarith only [f.Tcap]
  have base17 : ((1 : ℝ)*X 1 1+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 1).2]
  have base18 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 2).1]
  have base21 : ((1 : ℝ)*X 2 0+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 0).2]
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base53 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 1+(1 : ℝ)*P 2) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 2,f.sum]
  have base60 : ((1 : ℝ)*X 0 0+(-1 : ℝ)*X 0 1+(1 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1) ≤ (0 : ℝ) := by
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
  have s0_pow0 : (1 : ℝ) ^ (91/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^91 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^91*1^16 ≤ 1^16*1^91 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 91 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 91 16 (by norm_num) hpowers
    exact h
  have s0_corner0a : (2 : ℝ) ≤ (11296095383713331/10000000000000000 : ℝ) ^ (91/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (11296095383713331/10000000000000000 : ℝ)^91 := by
      have hnat : (2 : ℕ)^16*10000000000000000^91 ≤ 11296095383713331^91*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 11296095383713331 10000000000000000 16 91 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11296095383713331/10000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 91 16 (by norm_num) hpowers
    exact h
  have s0_corner0b : (3 : ℝ) ≤ (12130800245449181/10000000000000000 : ℝ) ^ (91/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (12130800245449181/10000000000000000 : ℝ)^91 := by
      have hnat : (3 : ℕ)^16*10000000000000000^91 ≤ 12130800245449181^91*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 12130800245449181 10000000000000000 16 91 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12130800245449181/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 91 16 (by norm_num) hpowers
    exact h
  have major_s0_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(1296095383713331/10000000000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(16694097234717/200000000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (91/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (1296095383713331/10000000000000000 : ℝ)) (beta := (16694097234717/200000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow0,s0_corner0a]) (by linarith only [s0_pow0,s0_corner0b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, false], ![false, false, false]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (1 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order0.2.2])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(1296095383713331/10000000000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(16694097234717/200000000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow1 : (1 : ℝ) ^ (91/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^91 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^91*1^16 ≤ 1^16*1^91 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 91 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 91 16 (by norm_num) hpowers
    exact h
  have s0_corner1a : (2 : ℝ) ≤ (11296095383713331/10000000000000000 : ℝ) ^ (91/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (11296095383713331/10000000000000000 : ℝ)^91 := by
      have hnat : (2 : ℕ)^16*10000000000000000^91 ≤ 11296095383713331^91*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 11296095383713331 10000000000000000 16 91 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11296095383713331/10000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 91 16 (by norm_num) hpowers
    exact h
  have s0_corner1b : (3 : ℝ) ≤ (12130800245449181/10000000000000000 : ℝ) ^ (91/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (12130800245449181/10000000000000000 : ℝ)^91 := by
      have hnat : (3 : ℕ)^16*10000000000000000^91 ≤ 12130800245449181^91*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 12130800245449181 10000000000000000 16 91 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12130800245449181/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 91 16 (by norm_num) hpowers
    exact h
  have major_s0_1 : P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1))+(1296095383713331/10000000000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2))+(16694097234717/200000000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 2 0)) := by
    have hh := chart_majorant (a := (91/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (1296095383713331/10000000000000000 : ℝ)) (beta := (16694097234717/200000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow1,s0_corner1a]) (by linarith only [s0_pow1,s0_corner1b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, false], ![false, false, false]] hX 1 (by
        change ((-1 : ℝ)*pair X 1 2) ≤ (1 : ℝ)*((-1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order1.2.2])
    change lpNorm p (pair X 1) ≤ ((-1 : ℝ)*pair X 1 1)+(1296095383713331/10000000000000000 : ℝ)*((-1 : ℝ)*pair X 1 2)+(16694097234717/200000000000000 : ℝ)*((-1 : ℝ)*pair X 1 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow2 : (1 : ℝ) ^ (91/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^91 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^91*1^16 ≤ 1^16*1^91 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 91 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 91 16 (by norm_num) hpowers
    exact h
  have s0_corner2a : (2 : ℝ) ≤ (11296095383713331/10000000000000000 : ℝ) ^ (91/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (11296095383713331/10000000000000000 : ℝ)^91 := by
      have hnat : (2 : ℕ)^16*10000000000000000^91 ≤ 11296095383713331^91*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 11296095383713331 10000000000000000 16 91 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11296095383713331/10000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 91 16 (by norm_num) hpowers
    exact h
  have s0_corner2b : (3 : ℝ) ≤ (12130800245449181/10000000000000000 : ℝ) ^ (91/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (12130800245449181/10000000000000000 : ℝ)^91 := by
      have hnat : (3 : ℕ)^16*10000000000000000^91 ≤ 12130800245449181^91*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 12130800245449181 10000000000000000 16 91 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12130800245449181/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 91 16 (by norm_num) hpowers
    exact h
  have major_s0_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(1296095383713331/10000000000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 1 0))+(16694097234717/200000000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (91/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (1296095383713331/10000000000000000 : ℝ)) (beta := (16694097234717/200000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow2,s0_corner2a]) (by linarith only [s0_pow2,s0_corner2b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, false], ![false, false, false]] hX 2 (by
        change ((-1 : ℝ)*pair X 2 0) ≤ (1 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order2.2.2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(1296095383713331/10000000000000000 : ℝ)*((-1 : ℝ)*pair X 2 0)+(16694097234717/200000000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s0_0 : ((-2893109501/10000000000 : ℝ)*X 0 0+(-877354677/2500000000 : ℝ)*X 0 1+(-43579319/78125000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c328064_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_1 : ((3329222231/10000000000 : ℝ)*X 1 0+(5192691547/10000000000 : ℝ)*X 1 1+(-3505462559/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c328064_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_2 : ((3066056807/5000000000 : ℝ)*X 2 0+(-3433617611/10000000000 : ℝ)*X 2 1+(2317953583/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c328064_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have hsep : (-20037/2000 : ℝ) < ((-8679/4000 : ℝ)*P 0+(-8679/4000 : ℝ)*P 1+(-8679/4000 : ℝ)*P 2+(1 : ℝ)*T) := by
    have hcertificate_margin : (-20037/2000 : ℝ) < (-2493122979971019191676584571/250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1150881827439/1000000000000 : ℝ)*(base1) + (150881827439/1000000000000 : ℝ)*(base7) + (31703/200000000000 : ℝ)*(base17) + (73759/200000000000 : ℝ)*(base18) + (64983/1000000000000 : ℝ)*(base21) + (813415452391/500000000000 : ℝ)*(base39) + (775010087129/1000000000000 : ℝ)*(base40) + (653/50000000000 : ℝ)*(base53) + (161773118111/200000000000 : ℝ)*(base60) + (8679/4000 : ℝ)*(major_s0_0) + (8679/4000 : ℝ)*(major_s0_1) + (108487499347/50000000000 : ℝ)*(major_s0_2) + (878774876429/200000000000 : ℝ)*(sp_s0_0) + (3242992027397/1000000000000 : ℝ)*(sp_s0_1) + (3242992502783/1000000000000 : ℝ)*(sp_s0_2) + (1621496283883/500000000000 : ℝ)*(f.sum) + (107525190444857/500000000000000000000000000 : ℝ)*base62 + (1489125430201/10000000000000000000000000 : ℝ)*base65 + (238204739/1000000000000000000000 : ℝ)*base67 + (42384433044857/500000000000000000000000000 : ℝ)*base68 + (909419138799/10000000000000000000000000 : ℝ)*base70 + (7046266423/10000000000000000000000 : ℝ)*base73 + (1536137369/5000000000000000000000 : ℝ)*base75 + (1324751337/10000000000000000000000 : ℝ)*base76 + (1368278761/10000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base83 + hcertificate_margin
  linarith only [hsep,f.failure]

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
namespace HlawkaSchatten.DiagonalCutoff4
theorem coarse_distinct_p028_b030 (p : ℝ) (hpa : (91/16 : ℝ) ≤ p) (hpb : p ≤ (93/16 : ℝ))
    (c : Fin 88) (hlo : 60 ≤ c.val) (hhi : c.val < 65)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (8679/4000 : ℝ) (80697/50000 : ℝ) (82433/100000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  have hc : c=60 ∨ c=61 ∨ c=62 ∨ c=63 ∨ c=64 := by omega
  rcases hc with rfl|rfl|rfl|rfl|rfl
  · exact collision_c328060 p hpa (by linarith only [hpb]) X hX
  · exact collision_c328061 p hpa (by linarith only [hpb]) X hX
  · exact collision_c328062 p hpa (by linarith only [hpb]) X hX
  · exact (hn63 rfl).elim
  · exact collision_c328064 p hpa (by linarith only [hpb]) X hX

end HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p : ℝ) (hpa : (91/16 : ℝ) ≤ p) (hpb : p ≤ (93/16 : ℝ))
    (c : Fin 88) (hlo : 60 ≤ c.val) (hhi : c.val < 65)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (8679/4000 : ℝ) (80697/50000 : ℝ) (82433/100000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  exact HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p028_b030 p hpa hpb c hlo hhi hn63 hn87 X hX

#print axioms solution
