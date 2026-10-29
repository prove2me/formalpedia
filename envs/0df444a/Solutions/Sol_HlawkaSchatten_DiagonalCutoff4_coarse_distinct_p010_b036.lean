-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p010_b036
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T22:16:41.441931+00:00
-- url     : https://prove2.me/submissions/c0900a40-3919-4747-ae98-3b3a1383bf88

import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c310082_s0
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c310082_s1
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c310082_s2
import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c310083_s0
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c310083_s1
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c310083_s2
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c310083_s3
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
theorem HlawkaSchatten.DiagonalCutoff4.collision_c310082 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (161793/100000 : ℝ) (18111/10000 : ℝ) (2431/3125 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![false, true, true]]) : False := by
  have h0 := collision_c310082_s0 p hpa hpb X hX
  have h1 := collision_c310082_s1 p hpa hpb X hX h0
  exact collision_c310082_s2 p hpa hpb X hX h1

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4
theorem HlawkaSchatten.DiagonalCutoff4.collision_c310083 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (161793/100000 : ℝ) (18111/10000 : ℝ) (2431/3125 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![true, true, true]]) : False := by
  have h0 := collision_c310083_s0 p hpa hpb X hX
  have h1 := collision_c310083_s1 p hpa hpb X hX h0
  have h2 := collision_c310083_s2 p hpa hpb X hX h1
  exact collision_c310083_s3 p hpa hpb X hX h2

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
theorem collision_support_c310081_s0_0 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-177772297/400000000 : ℝ)*x 0 + (107889389/400000000 : ℝ)*x 1 + (345208129/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (177772297/400000000 : ℝ)^71 ≤ (35103231762801/100000000000000 : ℝ)^55 := by
    have hnat : (177772297 : ℕ)^71*100000000000000^55 ≤ 35103231762801^55*400000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      177772297 400000000 35103231762801 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (107889389/400000000 : ℝ)^71 ≤ (18423317258927/100000000000000 : ℝ)^55 := by
    have hnat : (107889389 : ℕ)^71*100000000000000^55 ≤ 18423317258927^55*400000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      107889389 400000000 18423317258927 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (345208129/625000000 : ℝ)^71 ≤ (46473450962697/100000000000000 : ℝ)^55 := by
    have hnat : (345208129 : ℕ)^71*100000000000000^55 ≤ 46473450962697^55*625000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      345208129 625000000 46473450962697 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-177772297/400000000 : ℝ), (107889389/400000000 : ℝ), (345208129/625000000 : ℝ)] ![(35103231762801/100000000000000 : ℝ), (18423317258927/100000000000000 : ℝ), (46473450962697/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-177772297/400000000 : ℝ)|^71 ≤ (35103231762801/100000000000000 : ℝ)^55
        have hw : |(-177772297/400000000 : ℝ)|=(177772297/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(107889389/400000000 : ℝ)|^71 ≤ (18423317258927/100000000000000 : ℝ)^55
        have hw : |(107889389/400000000 : ℝ)|=(107889389/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(345208129/625000000 : ℝ)|^71 ≤ (46473450962697/100000000000000 : ℝ)^55
        have hw : |(345208129/625000000 : ℝ)|=(345208129/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310081_s0_2 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4037555251/10000000000 : ℝ)*x 0 + (7002778551/10000000000 : ℝ)*x 1 + (-1109768799/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4037555251/10000000000 : ℝ)^71 ≤ (31012356163023/100000000000000 : ℝ)^55 := by
    have hnat : (4037555251 : ℕ)^71*100000000000000^55 ≤ 31012356163023^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4037555251 10000000000 31012356163023 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (7002778551/10000000000 : ℝ)^71 ≤ (63133249537213/100000000000000 : ℝ)^55 := by
    have hnat : (7002778551 : ℕ)^71*100000000000000^55 ≤ 63133249537213^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7002778551 10000000000 63133249537213 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1109768799/10000000000 : ℝ)^71 ≤ (2927197142067/50000000000000 : ℝ)^55 := by
    have hnat : (1109768799 : ℕ)^71*50000000000000^55 ≤ 2927197142067^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1109768799 10000000000 2927197142067 50000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4037555251/10000000000 : ℝ), (7002778551/10000000000 : ℝ), (-1109768799/10000000000 : ℝ)] ![(31012356163023/100000000000000 : ℝ), (63133249537213/100000000000000 : ℝ), (2927197142067/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4037555251/10000000000 : ℝ)|^71 ≤ (31012356163023/100000000000000 : ℝ)^55
        have hw : |(4037555251/10000000000 : ℝ)|=(4037555251/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(7002778551/10000000000 : ℝ)|^71 ≤ (63133249537213/100000000000000 : ℝ)^55
        have hw : |(7002778551/10000000000 : ℝ)|=(7002778551/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1109768799/10000000000 : ℝ)|^71 ≤ (2927197142067/50000000000000 : ℝ)^55
        have hw : |(-1109768799/10000000000 : ℝ)|=(1109768799/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310081_s0_6 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2182473893/10000000000 : ℝ)*x 0 + (757061163/2000000000 : ℝ)*x 1 + (32546129/50000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2182473893/10000000000 : ℝ)^71 ≤ (14016620938119/100000000000000 : ℝ)^55 := by
    have hnat : (2182473893 : ℕ)^71*100000000000000^55 ≤ 14016620938119^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2182473893 10000000000 14016620938119 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (757061163/2000000000 : ℝ)^71 ≤ (7133566561343/25000000000000 : ℝ)^55 := by
    have hnat : (757061163 : ℕ)^71*25000000000000^55 ≤ 7133566561343^55*2000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      757061163 2000000000 7133566561343 25000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (32546129/50000000 : ℝ)^71 ≤ (11489822559039/20000000000000 : ℝ)^55 := by
    have hnat : (32546129 : ℕ)^71*20000000000000^55 ≤ 11489822559039^55*50000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      32546129 50000000 11489822559039 20000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2182473893/10000000000 : ℝ), (757061163/2000000000 : ℝ), (32546129/50000000 : ℝ)] ![(14016620938119/100000000000000 : ℝ), (7133566561343/25000000000000 : ℝ), (11489822559039/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2182473893/10000000000 : ℝ)|^71 ≤ (14016620938119/100000000000000 : ℝ)^55
        have hw : |(2182473893/10000000000 : ℝ)|=(2182473893/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(757061163/2000000000 : ℝ)|^71 ≤ (7133566561343/25000000000000 : ℝ)^55
        have hw : |(757061163/2000000000 : ℝ)|=(757061163/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(32546129/50000000 : ℝ)|^71 ≤ (11489822559039/20000000000000 : ℝ)^55
        have hw : |(32546129/50000000 : ℝ)|=(32546129/50000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310081_s0_7 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-4850010203/10000000000 : ℝ)*x 0 + (899818201/5000000000 : ℝ)*x 1 + (1456324313/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4850010203/10000000000 : ℝ)^71 ≤ (306981612661/781250000000 : ℝ)^55 := by
    have hnat : (4850010203 : ℕ)^71*781250000000^55 ≤ 306981612661^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4850010203 10000000000 306981612661 781250000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (899818201/5000000000 : ℝ)^71 ≤ (10927259267531/100000000000000 : ℝ)^55 := by
    have hnat : (899818201 : ℕ)^71*100000000000000^55 ≤ 10927259267531^55*5000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      899818201 5000000000 10927259267531 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1456324313/2500000000 : ℝ)^71 ≤ (9955818860583/20000000000000 : ℝ)^55 := by
    have hnat : (1456324313 : ℕ)^71*20000000000000^55 ≤ 9955818860583^55*2500000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1456324313 2500000000 9955818860583 20000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-4850010203/10000000000 : ℝ), (899818201/5000000000 : ℝ), (1456324313/2500000000 : ℝ)] ![(306981612661/781250000000 : ℝ), (10927259267531/100000000000000 : ℝ), (9955818860583/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-4850010203/10000000000 : ℝ)|^71 ≤ (306981612661/781250000000 : ℝ)^55
        have hw : |(-4850010203/10000000000 : ℝ)|=(4850010203/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(899818201/5000000000 : ℝ)|^71 ≤ (10927259267531/100000000000000 : ℝ)^55
        have hw : |(899818201/5000000000 : ℝ)|=(899818201/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1456324313/2500000000 : ℝ)|^71 ≤ (9955818860583/20000000000000 : ℝ)^55
        have hw : |(1456324313/2500000000 : ℝ)|=(1456324313/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310081_s0_8 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4817983761/10000000000 : ℝ)*x 0 + (-299832347/1250000000 : ℝ)*x 1 + (5406352217/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4817983761/10000000000 : ℝ)^71 ≤ (3895901551943/10000000000000 : ℝ)^55 := by
    have hnat : (4817983761 : ℕ)^71*10000000000000^55 ≤ 3895901551943^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4817983761 10000000000 3895901551943 10000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (299832347/1250000000 : ℝ)^71 ≤ (15834183111201/100000000000000 : ℝ)^55 := by
    have hnat : (299832347 : ℕ)^71*100000000000000^55 ≤ 15834183111201^55*1250000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      299832347 1250000000 15834183111201 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5406352217/10000000000 : ℝ)^71 ≤ (11301700338053/25000000000000 : ℝ)^55 := by
    have hnat : (5406352217 : ℕ)^71*25000000000000^55 ≤ 11301700338053^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5406352217 10000000000 11301700338053 25000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4817983761/10000000000 : ℝ), (-299832347/1250000000 : ℝ), (5406352217/10000000000 : ℝ)] ![(3895901551943/10000000000000 : ℝ), (15834183111201/100000000000000 : ℝ), (11301700338053/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4817983761/10000000000 : ℝ)|^71 ≤ (3895901551943/10000000000000 : ℝ)^55
        have hw : |(4817983761/10000000000 : ℝ)|=(4817983761/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-299832347/1250000000 : ℝ)|^71 ≤ (15834183111201/100000000000000 : ℝ)^55
        have hw : |(-299832347/1250000000 : ℝ)|=(299832347/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5406352217/10000000000 : ℝ)|^71 ≤ (11301700338053/25000000000000 : ℝ)^55
        have hw : |(5406352217/10000000000 : ℝ)|=(5406352217/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310081_s0_9 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1547163467/5000000000 : ℝ)*x 0 + (8037540227/10000000000 : ℝ)*x 1 + (-117528393/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1547163467/5000000000 : ℝ)^71 ≤ (1099859670199/5000000000000 : ℝ)^55 := by
    have hnat : (1547163467 : ℕ)^71*5000000000000^55 ≤ 1099859670199^55*5000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1547163467 5000000000 1099859670199 5000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (8037540227/10000000000 : ℝ)^71 ≤ (37713134368223/50000000000000 : ℝ)^55 := by
    have hnat : (8037540227 : ℕ)^71*50000000000000^55 ≤ 37713134368223^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8037540227 10000000000 37713134368223 50000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (117528393/2000000000 : ℝ)^71 ≤ (2576537849149/100000000000000 : ℝ)^55 := by
    have hnat : (117528393 : ℕ)^71*100000000000000^55 ≤ 2576537849149^55*2000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      117528393 2000000000 2576537849149 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1547163467/5000000000 : ℝ), (8037540227/10000000000 : ℝ), (-117528393/2000000000 : ℝ)] ![(1099859670199/5000000000000 : ℝ), (37713134368223/50000000000000 : ℝ), (2576537849149/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1547163467/5000000000 : ℝ)|^71 ≤ (1099859670199/5000000000000 : ℝ)^55
        have hw : |(1547163467/5000000000 : ℝ)|=(1547163467/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(8037540227/10000000000 : ℝ)|^71 ≤ (37713134368223/50000000000000 : ℝ)^55
        have hw : |(8037540227/10000000000 : ℝ)|=(8037540227/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-117528393/2000000000 : ℝ)|^71 ≤ (2576537849149/100000000000000 : ℝ)^55
        have hw : |(-117528393/2000000000 : ℝ)|=(117528393/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310081_s0_13 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (358738183/2500000000 : ℝ)*x 0 + (2500492661/5000000000 : ℝ)*x 1 + (5932319053/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (358738183/2500000000 : ℝ)^71 ≤ (1631488370861/20000000000000 : ℝ)^55 := by
    have hnat : (358738183 : ℕ)^71*20000000000000^55 ≤ 1631488370861^55*2500000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      358738183 2500000000 1631488370861 20000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2500492661/5000000000 : ℝ)^71 ≤ (40879738799413/100000000000000 : ℝ)^55 := by
    have hnat : (2500492661 : ℕ)^71*100000000000000^55 ≤ 40879738799413^55*5000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2500492661 5000000000 40879738799413 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5932319053/10000000000 : ℝ)^71 ≤ (50962819340553/100000000000000 : ℝ)^55 := by
    have hnat : (5932319053 : ℕ)^71*100000000000000^55 ≤ 50962819340553^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5932319053 10000000000 50962819340553 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(358738183/2500000000 : ℝ), (2500492661/5000000000 : ℝ), (5932319053/10000000000 : ℝ)] ![(1631488370861/20000000000000 : ℝ), (40879738799413/100000000000000 : ℝ), (50962819340553/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(358738183/2500000000 : ℝ)|^71 ≤ (1631488370861/20000000000000 : ℝ)^55
        have hw : |(358738183/2500000000 : ℝ)|=(358738183/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2500492661/5000000000 : ℝ)|^71 ≤ (40879738799413/100000000000000 : ℝ)^55
        have hw : |(2500492661/5000000000 : ℝ)|=(2500492661/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5932319053/10000000000 : ℝ)|^71 ≤ (50962819340553/100000000000000 : ℝ)^55
        have hw : |(5932319053/10000000000 : ℝ)|=(5932319053/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310081_s0_14 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-4069924833/10000000000 : ℝ)*x 0 + (1716070211/10000000000 : ℝ)*x 1 + (6591621561/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4069924833/10000000000 : ℝ)^71 ≤ (6266737669627/20000000000000 : ℝ)^55 := by
    have hnat : (4069924833 : ℕ)^71*20000000000000^55 ≤ 6266737669627^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4069924833 10000000000 6266737669627 20000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1716070211/10000000000 : ℝ)^71 ≤ (2569178915359/25000000000000 : ℝ)^55 := by
    have hnat : (1716070211 : ℕ)^71*25000000000000^55 ≤ 2569178915359^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1716070211 10000000000 2569178915359 25000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6591621561/10000000000 : ℝ)^71 ≤ (58389595976329/100000000000000 : ℝ)^55 := by
    have hnat : (6591621561 : ℕ)^71*100000000000000^55 ≤ 58389595976329^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6591621561 10000000000 58389595976329 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-4069924833/10000000000 : ℝ), (1716070211/10000000000 : ℝ), (6591621561/10000000000 : ℝ)] ![(6266737669627/20000000000000 : ℝ), (2569178915359/25000000000000 : ℝ), (58389595976329/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-4069924833/10000000000 : ℝ)|^71 ≤ (6266737669627/20000000000000 : ℝ)^55
        have hw : |(-4069924833/10000000000 : ℝ)|=(4069924833/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1716070211/10000000000 : ℝ)|^71 ≤ (2569178915359/25000000000000 : ℝ)^55
        have hw : |(1716070211/10000000000 : ℝ)|=(1716070211/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6591621561/10000000000 : ℝ)|^71 ≤ (58389595976329/100000000000000 : ℝ)^55
        have hw : |(6591621561/10000000000 : ℝ)|=(6591621561/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310081_s0_15 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5411736227/10000000000 : ℝ)*x 0 + (-1609822451/5000000000 : ℝ)*x 1 + (1023700181/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5411736227/10000000000 : ℝ)^71 ≤ (5658115808817/12500000000000 : ℝ)^55 := by
    have hnat : (5411736227 : ℕ)^71*12500000000000^55 ≤ 5658115808817^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5411736227 10000000000 5658115808817 12500000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1609822451/5000000000 : ℝ)^71 ≤ (1447121042113/6250000000000 : ℝ)^55 := by
    have hnat : (1609822451 : ℕ)^71*6250000000000^55 ≤ 1447121042113^55*5000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1609822451 5000000000 1447121042113 6250000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1023700181/2500000000 : ℝ)^71 ≤ (31581136840313/100000000000000 : ℝ)^55 := by
    have hnat : (1023700181 : ℕ)^71*100000000000000^55 ≤ 31581136840313^55*2500000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1023700181 2500000000 31581136840313 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5411736227/10000000000 : ℝ), (-1609822451/5000000000 : ℝ), (1023700181/2500000000 : ℝ)] ![(5658115808817/12500000000000 : ℝ), (1447121042113/6250000000000 : ℝ), (31581136840313/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5411736227/10000000000 : ℝ)|^71 ≤ (5658115808817/12500000000000 : ℝ)^55
        have hw : |(5411736227/10000000000 : ℝ)|=(5411736227/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1609822451/5000000000 : ℝ)|^71 ≤ (1447121042113/6250000000000 : ℝ)^55
        have hw : |(-1609822451/5000000000 : ℝ)|=(1609822451/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1023700181/2500000000 : ℝ)|^71 ≤ (31581136840313/100000000000000 : ℝ)^55
        have hw : |(1023700181/2500000000 : ℝ)|=(1023700181/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310081_s0_16 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (551079463/1250000000 : ℝ)*x 0 + (7086503987/10000000000 : ℝ)*x 1 + (-314725431/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (551079463/1250000000 : ℝ)^71 ≤ (17369970464431/50000000000000 : ℝ)^55 := by
    have hnat : (551079463 : ℕ)^71*50000000000000^55 ≤ 17369970464431^55*1250000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      551079463 1250000000 17369970464431 50000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (7086503987/10000000000 : ℝ)^71 ≤ (32054673648027/50000000000000 : ℝ)^55 := by
    have hnat : (7086503987 : ℕ)^71*50000000000000^55 ≤ 32054673648027^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7086503987 10000000000 32054673648027 50000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (314725431/10000000000 : ℝ)^71 ≤ (287677941103/25000000000000 : ℝ)^55 := by
    have hnat : (314725431 : ℕ)^71*25000000000000^55 ≤ 287677941103^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      314725431 10000000000 287677941103 25000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(551079463/1250000000 : ℝ), (7086503987/10000000000 : ℝ), (-314725431/10000000000 : ℝ)] ![(17369970464431/50000000000000 : ℝ), (32054673648027/50000000000000 : ℝ), (287677941103/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(551079463/1250000000 : ℝ)|^71 ≤ (17369970464431/50000000000000 : ℝ)^55
        have hw : |(551079463/1250000000 : ℝ)|=(551079463/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(7086503987/10000000000 : ℝ)|^71 ≤ (32054673648027/50000000000000 : ℝ)^55
        have hw : |(7086503987/10000000000 : ℝ)|=(7086503987/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-314725431/10000000000 : ℝ)|^71 ≤ (287677941103/25000000000000 : ℝ)^55
        have hw : |(-314725431/10000000000 : ℝ)|=(314725431/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310081_s0_20 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1301845133/10000000000 : ℝ)*x 0 + (5905271/20000000 : ℝ)*x 1 + (310463793/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1301845133/10000000000 : ℝ)^71 ≤ (1798525460891/25000000000000 : ℝ)^55 := by
    have hnat : (1301845133 : ℕ)^71*25000000000000^55 ≤ 1798525460891^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1301845133 10000000000 1798525460891 25000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5905271/20000000 : ℝ)^71 ≤ (5176414809487/25000000000000 : ℝ)^55 := by
    have hnat : (5905271 : ℕ)^71*25000000000000^55 ≤ 5176414809487^55*20000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5905271 20000000 5176414809487 25000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (310463793/400000000 : ℝ)^71 ≤ (9012529863551/12500000000000 : ℝ)^55 := by
    have hnat : (310463793 : ℕ)^71*12500000000000^55 ≤ 9012529863551^55*400000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      310463793 400000000 9012529863551 12500000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1301845133/10000000000 : ℝ), (5905271/20000000 : ℝ), (310463793/400000000 : ℝ)] ![(1798525460891/25000000000000 : ℝ), (5176414809487/25000000000000 : ℝ), (9012529863551/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1301845133/10000000000 : ℝ)|^71 ≤ (1798525460891/25000000000000 : ℝ)^55
        have hw : |(1301845133/10000000000 : ℝ)|=(1301845133/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5905271/20000000 : ℝ)|^71 ≤ (5176414809487/25000000000000 : ℝ)^55
        have hw : |(5905271/20000000 : ℝ)|=(5905271/20000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(310463793/400000000 : ℝ)|^71 ≤ (9012529863551/12500000000000 : ℝ)^55
        have hw : |(310463793/400000000 : ℝ)|=(310463793/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310081_s0_21 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-1320177771/2500000000 : ℝ)*x 0 + (1899763583/10000000000 : ℝ)*x 1 + (1066783419/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1320177771/2500000000 : ℝ)^71 ≤ (43855201166341/100000000000000 : ℝ)^55 := by
    have hnat : (1320177771 : ℕ)^71*100000000000000^55 ≤ 43855201166341^55*2500000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1320177771 2500000000 43855201166341 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1899763583/10000000000 : ℝ)^71 ≤ (11718356403827/100000000000000 : ℝ)^55 := by
    have hnat : (1899763583 : ℕ)^71*100000000000000^55 ≤ 11718356403827^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1899763583 10000000000 11718356403827 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1066783419/2000000000 : ℝ)^71 ≤ (2221322120717/5000000000000 : ℝ)^55 := by
    have hnat : (1066783419 : ℕ)^71*5000000000000^55 ≤ 2221322120717^55*2000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1066783419 2000000000 2221322120717 5000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1320177771/2500000000 : ℝ), (1899763583/10000000000 : ℝ), (1066783419/2000000000 : ℝ)] ![(43855201166341/100000000000000 : ℝ), (11718356403827/100000000000000 : ℝ), (2221322120717/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1320177771/2500000000 : ℝ)|^71 ≤ (43855201166341/100000000000000 : ℝ)^55
        have hw : |(-1320177771/2500000000 : ℝ)|=(1320177771/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1899763583/10000000000 : ℝ)|^71 ≤ (11718356403827/100000000000000 : ℝ)^55
        have hw : |(1899763583/10000000000 : ℝ)|=(1899763583/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1066783419/2000000000 : ℝ)|^71 ≤ (2221322120717/5000000000000 : ℝ)^55
        have hw : |(1066783419/2000000000 : ℝ)|=(1066783419/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310081_s0_22 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1888330019/5000000000 : ℝ)*x 0 + (-4094230277/10000000000 : ℝ)*x 1 + (4914972279/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1888330019/5000000000 : ℝ)^71 ≤ (28450161395231/100000000000000 : ℝ)^55 := by
    have hnat : (1888330019 : ℕ)^71*100000000000000^55 ≤ 28450161395231^55*5000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1888330019 5000000000 28450161395231 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4094230277/10000000000 : ℝ)^71 ≤ (31575457509753/100000000000000 : ℝ)^55 := by
    have hnat : (4094230277 : ℕ)^71*100000000000000^55 ≤ 31575457509753^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4094230277 10000000000 31575457509753 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4914972279/10000000000 : ℝ)^71 ≤ (39974381086983/100000000000000 : ℝ)^55 := by
    have hnat : (4914972279 : ℕ)^71*100000000000000^55 ≤ 39974381086983^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4914972279 10000000000 39974381086983 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1888330019/5000000000 : ℝ), (-4094230277/10000000000 : ℝ), (4914972279/10000000000 : ℝ)] ![(28450161395231/100000000000000 : ℝ), (31575457509753/100000000000000 : ℝ), (39974381086983/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1888330019/5000000000 : ℝ)|^71 ≤ (28450161395231/100000000000000 : ℝ)^55
        have hw : |(1888330019/5000000000 : ℝ)|=(1888330019/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-4094230277/10000000000 : ℝ)|^71 ≤ (31575457509753/100000000000000 : ℝ)^55
        have hw : |(-4094230277/10000000000 : ℝ)|=(4094230277/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4914972279/10000000000 : ℝ)|^71 ≤ (39974381086983/100000000000000 : ℝ)^55
        have hw : |(4914972279/10000000000 : ℝ)|=(4914972279/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310081_s0_23 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2445666353/5000000000 : ℝ)*x 0 + (6409905451/10000000000 : ℝ)*x 1 + (-818771983/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2445666353/5000000000 : ℝ)^71 ≤ (39726358244631/100000000000000 : ℝ)^55 := by
    have hnat : (2445666353 : ℕ)^71*100000000000000^55 ≤ 39726358244631^55*5000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2445666353 5000000000 39726358244631 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6409905451/10000000000 : ℝ)^71 ≤ (5632004652741/10000000000000 : ℝ)^55 := by
    have hnat : (6409905451 : ℕ)^71*10000000000000^55 ≤ 5632004652741^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6409905451 10000000000 5632004652741 10000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (818771983/10000000000 : ℝ)^71 ≤ (1976797605739/50000000000000 : ℝ)^55 := by
    have hnat : (818771983 : ℕ)^71*50000000000000^55 ≤ 1976797605739^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      818771983 10000000000 1976797605739 50000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2445666353/5000000000 : ℝ), (6409905451/10000000000 : ℝ), (-818771983/10000000000 : ℝ)] ![(39726358244631/100000000000000 : ℝ), (5632004652741/10000000000000 : ℝ), (1976797605739/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2445666353/5000000000 : ℝ)|^71 ≤ (39726358244631/100000000000000 : ℝ)^55
        have hw : |(2445666353/5000000000 : ℝ)|=(2445666353/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6409905451/10000000000 : ℝ)|^71 ≤ (5632004652741/10000000000000 : ℝ)^55
        have hw : |(6409905451/10000000000 : ℝ)|=(6409905451/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-818771983/10000000000 : ℝ)|^71 ≤ (1976797605739/50000000000000 : ℝ)^55
        have hw : |(-818771983/10000000000 : ℝ)|=(818771983/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310081_s0_27 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (585626161/5000000000 : ℝ)*x 0 + (2312608459/5000000000 : ℝ)*x 1 + (3224546893/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (585626161/5000000000 : ℝ)^71 ≤ (3138213039807/50000000000000 : ℝ)^55 := by
    have hnat : (585626161 : ℕ)^71*50000000000000^55 ≤ 3138213039807^55*5000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      585626161 5000000000 3138213039807 50000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2312608459/5000000000 : ℝ)^71 ≤ (36958640769951/100000000000000 : ℝ)^55 := by
    have hnat : (2312608459 : ℕ)^71*100000000000000^55 ≤ 36958640769951^55*5000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2312608459 5000000000 36958640769951 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3224546893/5000000000 : ℝ)^71 ≤ (14191233282837/25000000000000 : ℝ)^55 := by
    have hnat : (3224546893 : ℕ)^71*25000000000000^55 ≤ 14191233282837^55*5000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3224546893 5000000000 14191233282837 25000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(585626161/5000000000 : ℝ), (2312608459/5000000000 : ℝ), (3224546893/5000000000 : ℝ)] ![(3138213039807/50000000000000 : ℝ), (36958640769951/100000000000000 : ℝ), (14191233282837/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(585626161/5000000000 : ℝ)|^71 ≤ (3138213039807/50000000000000 : ℝ)^55
        have hw : |(585626161/5000000000 : ℝ)|=(585626161/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2312608459/5000000000 : ℝ)|^71 ≤ (36958640769951/100000000000000 : ℝ)^55
        have hw : |(2312608459/5000000000 : ℝ)|=(2312608459/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3224546893/5000000000 : ℝ)|^71 ≤ (14191233282837/25000000000000 : ℝ)^55
        have hw : |(3224546893/5000000000 : ℝ)|=(3224546893/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310081_s1_0 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-4387404071/10000000000 : ℝ)*x 0 + (3496486717/10000000000 : ℝ)*x 1 + (4890761277/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4387404071/10000000000 : ℝ)^71 ≤ (17262058587027/50000000000000 : ℝ)^55 := by
    have hnat : (4387404071 : ℕ)^71*50000000000000^55 ≤ 17262058587027^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4387404071 10000000000 17262058587027 50000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3496486717/10000000000 : ℝ)^71 ≤ (402429931383/1562500000000 : ℝ)^55 := by
    have hnat : (3496486717 : ℕ)^71*1562500000000^55 ≤ 402429931383^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3496486717 10000000000 402429931383 1562500000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4890761277/10000000000 : ℝ)^71 ≤ (19860183603093/50000000000000 : ℝ)^55 := by
    have hnat : (4890761277 : ℕ)^71*50000000000000^55 ≤ 19860183603093^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4890761277 10000000000 19860183603093 50000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-4387404071/10000000000 : ℝ), (3496486717/10000000000 : ℝ), (4890761277/10000000000 : ℝ)] ![(17262058587027/50000000000000 : ℝ), (402429931383/1562500000000 : ℝ), (19860183603093/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-4387404071/10000000000 : ℝ)|^71 ≤ (17262058587027/50000000000000 : ℝ)^55
        have hw : |(-4387404071/10000000000 : ℝ)|=(4387404071/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3496486717/10000000000 : ℝ)|^71 ≤ (402429931383/1562500000000 : ℝ)^55
        have hw : |(3496486717/10000000000 : ℝ)|=(3496486717/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4890761277/10000000000 : ℝ)|^71 ≤ (19860183603093/50000000000000 : ℝ)^55
        have hw : |(4890761277/10000000000 : ℝ)|=(4890761277/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310081_s1_1 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (70601327/156250000 : ℝ)*x 0 + (-900237491/2500000000 : ℝ)*x 1 + (1166635421/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (70601327/156250000 : ℝ)^71 ≤ (35861389929993/100000000000000 : ℝ)^55 := by
    have hnat : (70601327 : ℕ)^71*100000000000000^55 ≤ 35861389929993^55*156250000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      70601327 156250000 35861389929993 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (900237491/2500000000 : ℝ)^71 ≤ (5350628277697/20000000000000 : ℝ)^55 := by
    have hnat : (900237491 : ℕ)^71*20000000000000^55 ≤ 5350628277697^55*2500000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      900237491 2500000000 5350628277697 20000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1166635421/2500000000 : ℝ)^71 ≤ (149541874677/400000000000 : ℝ)^55 := by
    have hnat : (1166635421 : ℕ)^71*400000000000^55 ≤ 149541874677^55*2500000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1166635421 2500000000 149541874677 400000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(70601327/156250000 : ℝ), (-900237491/2500000000 : ℝ), (1166635421/2500000000 : ℝ)] ![(35861389929993/100000000000000 : ℝ), (5350628277697/20000000000000 : ℝ), (149541874677/400000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(70601327/156250000 : ℝ)|^71 ≤ (35861389929993/100000000000000 : ℝ)^55
        have hw : |(70601327/156250000 : ℝ)|=(70601327/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-900237491/2500000000 : ℝ)|^71 ≤ (5350628277697/20000000000000 : ℝ)^55
        have hw : |(-900237491/2500000000 : ℝ)|=(900237491/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1166635421/2500000000 : ℝ)|^71 ≤ (149541874677/400000000000 : ℝ)^55
        have hw : |(1166635421/2500000000 : ℝ)|=(1166635421/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310081_s1_2 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1083459797/2500000000 : ℝ)*x 0 + (2848881309/5000000000 : ℝ)*x 1 + (-521645561/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1083459797/2500000000 : ℝ)^71 ≤ (1699048557129/5000000000000 : ℝ)^55 := by
    have hnat : (1083459797 : ℕ)^71*5000000000000^55 ≤ 1699048557129^55*2500000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1083459797 2500000000 1699048557129 5000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2848881309/5000000000 : ℝ)^71 ≤ (1209418298619/2500000000000 : ℝ)^55 := by
    have hnat : (2848881309 : ℕ)^71*2500000000000^55 ≤ 1209418298619^55*5000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2848881309 5000000000 1209418298619 2500000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (521645561/2000000000 : ℝ)^71 ≤ (17642296893313/100000000000000 : ℝ)^55 := by
    have hnat : (521645561 : ℕ)^71*100000000000000^55 ≤ 17642296893313^55*2000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      521645561 2000000000 17642296893313 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1083459797/2500000000 : ℝ), (2848881309/5000000000 : ℝ), (-521645561/2000000000 : ℝ)] ![(1699048557129/5000000000000 : ℝ), (1209418298619/2500000000000 : ℝ), (17642296893313/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1083459797/2500000000 : ℝ)|^71 ≤ (1699048557129/5000000000000 : ℝ)^55
        have hw : |(1083459797/2500000000 : ℝ)|=(1083459797/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2848881309/5000000000 : ℝ)|^71 ≤ (1209418298619/2500000000000 : ℝ)^55
        have hw : |(2848881309/5000000000 : ℝ)|=(2848881309/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-521645561/2000000000 : ℝ)|^71 ≤ (17642296893313/100000000000000 : ℝ)^55
        have hw : |(-521645561/2000000000 : ℝ)|=(521645561/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310081_s1_6 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (389918353/1250000000 : ℝ)*x 0 + (820210301/2000000000 : ℝ)*x 1 + (219665667/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (389918353/1250000000 : ℝ)^71 ≤ (11113534173723/50000000000000 : ℝ)^55 := by
    have hnat : (389918353 : ℕ)^71*50000000000000^55 ≤ 11113534173723^55*1250000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      389918353 1250000000 11113534173723 50000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (820210301/2000000000 : ℝ)^71 ≤ (6328676850907/20000000000000 : ℝ)^55 := by
    have hnat : (820210301 : ℕ)^71*20000000000000^55 ≤ 6328676850907^55*2000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      820210301 2000000000 6328676850907 20000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (219665667/400000000 : ℝ)^71 ≤ (46129547393611/100000000000000 : ℝ)^55 := by
    have hnat : (219665667 : ℕ)^71*100000000000000^55 ≤ 46129547393611^55*400000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      219665667 400000000 46129547393611 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(389918353/1250000000 : ℝ), (820210301/2000000000 : ℝ), (219665667/400000000 : ℝ)] ![(11113534173723/50000000000000 : ℝ), (6328676850907/20000000000000 : ℝ), (46129547393611/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(389918353/1250000000 : ℝ)|^71 ≤ (11113534173723/50000000000000 : ℝ)^55
        have hw : |(389918353/1250000000 : ℝ)|=(389918353/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(820210301/2000000000 : ℝ)|^71 ≤ (6328676850907/20000000000000 : ℝ)^55
        have hw : |(820210301/2000000000 : ℝ)|=(820210301/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(219665667/400000000 : ℝ)|^71 ≤ (46129547393611/100000000000000 : ℝ)^55
        have hw : |(219665667/400000000 : ℝ)|=(219665667/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c310081 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (161793/100000 : ℝ) (18111/10000 : ℝ) (2431/3125 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![false, false, true]]) : False := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (2431/3125 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (2431/3125 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (2431/3125 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (2431/3125 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 0+X 2 0)) ∧ ((-1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 0) ∧ ((-1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (2431/3125 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (2431/3125 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((-1 : ℝ)*(X 0 1+X 1 1)) ∧ ((-1 : ℝ)*(X 0 1+X 1 1)) ≤ ((-1 : ℝ)*(X 0 0+X 1 0)) ∧ ((-1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((-1 : ℝ)*pair X 2 1) ∧ ((-1 : ℝ)*pair X 2 1) ≤ ((-1 : ℝ)*pair X 2 0) ∧ ((-1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base19 : ((1 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 2).2]
  have base23 : ((1 : ℝ)*X 2 1+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 1).2]
  have base31 : ((1 : ℝ)*X 0 2+(1 : ℝ)*X 1 2+(1 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [(f.column 2).2]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base49 : ((1 : ℝ)*X 0 0+(1 : ℝ)*X 2 0) ≤ (0 : ℝ) := by
    linarith only [order1.1]
  have base59 : ((1 : ℝ)*X 0 1+(1 : ℝ)*X 1 1) ≤ (0 : ℝ) := by
    linarith only [order2.1]
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
  have s0_pow0 : (1 : ℝ) ^ (35/8 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^35 ≤ (1 : ℝ)^8 := by
      have hnat : (1 : ℕ)^35*1^8 ≤ 1^8*1^35 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 35 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have s0_corner0a : (2 : ℝ) ≤ (11716741708364597/10000000000000000 : ℝ) ^ (35/8 : ℝ) := by
    have hpowers : (2 : ℝ)^8 ≤ (11716741708364597/10000000000000000 : ℝ)^35 := by
      have hnat : (2 : ℕ)^8*10000000000000000^35 ≤ 11716741708364597^35*1^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 11716741708364597 10000000000000000 8 35 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11716741708364597/10000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have s0_corner0b : (3 : ℝ) ≤ (3213633126210889/2500000000000000 : ℝ) ^ (35/8 : ℝ) := by
    have hpowers : (3 : ℝ)^8 ≤ (3213633126210889/2500000000000000 : ℝ)^35 := by
      have hnat : (3 : ℕ)^8*2500000000000000^35 ≤ 3213633126210889^35*1^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 3213633126210889 2500000000000000 8 35 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (3213633126210889/2500000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have major_s0_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(1716741708364597/10000000000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(1137790796478959/10000000000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (35/8 : ℝ)) (rho := (1 : ℝ)) (alpha := (1716741708364597/10000000000000000 : ℝ)) (beta := (1137790796478959/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow0,s0_corner0a]) (by linarith only [s0_pow0,s0_corner0b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![false, false, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (1 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order0.2.2])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(1716741708364597/10000000000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(1137790796478959/10000000000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow1 : (1 : ℝ) ^ (35/8 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^35 ≤ (1 : ℝ)^8 := by
      have hnat : (1 : ℕ)^35*1^8 ≤ 1^8*1^35 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 35 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have s0_corner1a : (2 : ℝ) ≤ (11716741708364597/10000000000000000 : ℝ) ^ (35/8 : ℝ) := by
    have hpowers : (2 : ℝ)^8 ≤ (11716741708364597/10000000000000000 : ℝ)^35 := by
      have hnat : (2 : ℕ)^8*10000000000000000^35 ≤ 11716741708364597^35*1^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 11716741708364597 10000000000000000 8 35 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11716741708364597/10000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have s0_corner1b : (3 : ℝ) ≤ (3213633126210889/2500000000000000 : ℝ) ^ (35/8 : ℝ) := by
    have hpowers : (3 : ℝ)^8 ≤ (3213633126210889/2500000000000000 : ℝ)^35 := by
      have hnat : (3 : ℕ)^8*2500000000000000^35 ≤ 3213633126210889^35*1^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 3213633126210889 2500000000000000 8 35 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (3213633126210889/2500000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have major_s0_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(1716741708364597/10000000000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2))+(1137790796478959/10000000000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 2 0)) := by
    have hh := chart_majorant (a := (35/8 : ℝ)) (rho := (1 : ℝ)) (alpha := (1716741708364597/10000000000000000 : ℝ)) (beta := (1137790796478959/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow1,s0_corner1a]) (by linarith only [s0_pow1,s0_corner1b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![false, false, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 2) ≤ (1 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order1.2.2])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(1716741708364597/10000000000000000 : ℝ)*((1 : ℝ)*pair X 1 2)+(1137790796478959/10000000000000000 : ℝ)*((-1 : ℝ)*pair X 1 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow2 : (1 : ℝ) ^ (35/8 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^35 ≤ (1 : ℝ)^8 := by
      have hnat : (1 : ℕ)^35*1^8 ≤ 1^8*1^35 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 35 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have s0_corner2a : (2 : ℝ) ≤ (11716741708364597/10000000000000000 : ℝ) ^ (35/8 : ℝ) := by
    have hpowers : (2 : ℝ)^8 ≤ (11716741708364597/10000000000000000 : ℝ)^35 := by
      have hnat : (2 : ℕ)^8*10000000000000000^35 ≤ 11716741708364597^35*1^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 11716741708364597 10000000000000000 8 35 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11716741708364597/10000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have s0_corner2b : (3 : ℝ) ≤ (3213633126210889/2500000000000000 : ℝ) ^ (35/8 : ℝ) := by
    have hpowers : (3 : ℝ)^8 ≤ (3213633126210889/2500000000000000 : ℝ)^35 := by
      have hnat : (3 : ℕ)^8*2500000000000000^35 ≤ 3213633126210889^35*1^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 3213633126210889 2500000000000000 8 35 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (3213633126210889/2500000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have major_s0_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(1716741708364597/10000000000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 1 0))+(1137790796478959/10000000000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (35/8 : ℝ)) (rho := (1 : ℝ)) (alpha := (1716741708364597/10000000000000000 : ℝ)) (beta := (1137790796478959/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow2,s0_corner2a]) (by linarith only [s0_pow2,s0_corner2b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![false, false, true]] hX 2 (by
        change ((-1 : ℝ)*pair X 2 0) ≤ (1 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order2.2.2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(1716741708364597/10000000000000000 : ℝ)*((-1 : ℝ)*pair X 2 0)+(1137790796478959/10000000000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s0_0 : ((-177772297/400000000 : ℝ)*X 0 0+(107889389/400000000 : ℝ)*X 0 1+(345208129/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c310081_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_2 : ((4037555251/10000000000 : ℝ)*X 2 0+(7002778551/10000000000 : ℝ)*X 2 1+(-1109768799/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c310081_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_6 : ((2182473893/10000000000 : ℝ)*X 0 0+(757061163/2000000000 : ℝ)*X 0 1+(32546129/50000000 : ℝ)*X 0 2+(2182473893/10000000000 : ℝ)*X 1 0+(757061163/2000000000 : ℝ)*X 1 1+(32546129/50000000 : ℝ)*X 1 2+(2182473893/10000000000 : ℝ)*X 2 0+(757061163/2000000000 : ℝ)*X 2 1+(32546129/50000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c310081_s0_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_7 : ((-4850010203/10000000000 : ℝ)*X 0 0+(899818201/5000000000 : ℝ)*X 0 1+(1456324313/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c310081_s0_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_8 : ((4817983761/10000000000 : ℝ)*X 1 0+(-299832347/1250000000 : ℝ)*X 1 1+(5406352217/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c310081_s0_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_9 : ((1547163467/5000000000 : ℝ)*X 2 0+(8037540227/10000000000 : ℝ)*X 2 1+(-117528393/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c310081_s0_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_13 : ((358738183/2500000000 : ℝ)*X 0 0+(2500492661/5000000000 : ℝ)*X 0 1+(5932319053/10000000000 : ℝ)*X 0 2+(358738183/2500000000 : ℝ)*X 1 0+(2500492661/5000000000 : ℝ)*X 1 1+(5932319053/10000000000 : ℝ)*X 1 2+(358738183/2500000000 : ℝ)*X 2 0+(2500492661/5000000000 : ℝ)*X 2 1+(5932319053/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c310081_s0_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_14 : ((-4069924833/10000000000 : ℝ)*X 0 0+(1716070211/10000000000 : ℝ)*X 0 1+(6591621561/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c310081_s0_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_15 : ((5411736227/10000000000 : ℝ)*X 1 0+(-1609822451/5000000000 : ℝ)*X 1 1+(1023700181/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c310081_s0_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_16 : ((551079463/1250000000 : ℝ)*X 2 0+(7086503987/10000000000 : ℝ)*X 2 1+(-314725431/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c310081_s0_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_20 : ((1301845133/10000000000 : ℝ)*X 0 0+(5905271/20000000 : ℝ)*X 0 1+(310463793/400000000 : ℝ)*X 0 2+(1301845133/10000000000 : ℝ)*X 1 0+(5905271/20000000 : ℝ)*X 1 1+(310463793/400000000 : ℝ)*X 1 2+(1301845133/10000000000 : ℝ)*X 2 0+(5905271/20000000 : ℝ)*X 2 1+(310463793/400000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c310081_s0_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_21 : ((-1320177771/2500000000 : ℝ)*X 0 0+(1899763583/10000000000 : ℝ)*X 0 1+(1066783419/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c310081_s0_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_22 : ((1888330019/5000000000 : ℝ)*X 1 0+(-4094230277/10000000000 : ℝ)*X 1 1+(4914972279/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c310081_s0_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_23 : ((2445666353/5000000000 : ℝ)*X 2 0+(6409905451/10000000000 : ℝ)*X 2 1+(-818771983/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c310081_s0_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_27 : ((585626161/5000000000 : ℝ)*X 0 0+(2312608459/5000000000 : ℝ)*X 0 1+(3224546893/5000000000 : ℝ)*X 0 2+(585626161/5000000000 : ℝ)*X 1 0+(2312608459/5000000000 : ℝ)*X 1 1+(3224546893/5000000000 : ℝ)*X 1 2+(585626161/5000000000 : ℝ)*X 2 0+(2312608459/5000000000 : ℝ)*X 2 1+(3224546893/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c310081_s0_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s0_0 : (0 : ℝ) ≤ ((29751/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(29751/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (342551089205366168979/25000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1193191830829/1000000000000 : ℝ)*(base49) + (33087424931/25000000000 : ℝ)*(base59) + (80596732047/20000000000 : ℝ)*(major_s0_0) + (80596732047/20000000000 : ℝ)*(major_s0_1) + (80596732047/20000000000 : ℝ)*(major_s0_2) + (5595681/40000000000 : ℝ)*(sp_s0_0) + (17963713/250000000000 : ℝ)*(sp_s0_2) + (5568748750369/1000000000000 : ℝ)*(sp_s0_7) + (5568913232549/1000000000000 : ℝ)*(sp_s0_8) + (5568860717059/1000000000000 : ℝ)*(sp_s0_9) + (2490669207493/1000000000000 : ℝ)*(sp_s0_13) + (43929517/1000000000000 : ℝ)*(sp_s0_14) + (19339361/1000000000000 : ℝ)*(sp_s0_22) + (33428971/500000000000 : ℝ)*(sp_s0_27) + (622684016359/250000000000 : ℝ)*(f.failure) + (5568932571911/1000000000000 : ℝ)*(f.sum) + (20691523305217/50000000000000000000000000 : ℝ)*base63 + (26523577539073/200000000000000000000000000 : ℝ)*base64 + (53932093179941/200000000000000000000000000 : ℝ)*base66 + (7263915719941/200000000000000000000000000 : ℝ)*base69 + (1210777989507/100000000000000000000000000 : ℝ)*base70 + (66119648639073/200000000000000000000000000 : ℝ)*base73 + (65094739659073/200000000000000000000000000 : ℝ)*base74 + (78656856799941/200000000000000000000000000 : ℝ)*base76 + (18127802369783/50000000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base82 + (21687/25000000000000000 : ℝ)*base87 + (21687/25000000000000000 : ℝ)*base89 + (21687/25000000000000000 : ℝ)*base91 + (1/1000000000000 : ℝ)*base92 + hcertificate_margin
  have ratio_s0_1 : (0 : ℝ) ≤ ((35651/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(35651/100000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (25617659206369468199331/2500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (311399209371/1000000000000 : ℝ)*(base40) + (448745336723/500000000000 : ℝ)*(base49) + (443588714487/250000000000 : ℝ)*(base59) + (1747053/1000000000000 : ℝ)*(base60) + (2283501731191/500000000000 : ℝ)*(major_s0_0) + (2283501731191/500000000000 : ℝ)*(major_s0_1) + (2283501731191/500000000000 : ℝ)*(major_s0_2) + (70611/8000000000 : ℝ)*(sp_s0_6) + (12650563/500000000000 : ℝ)*(sp_s0_7) + (6311233427651/1000000000000 : ℝ)*(sp_s0_14) + (6311258728777/1000000000000 : ℝ)*(sp_s0_15) + (98613142917/15625000000 : ℝ)*(sp_s0_16) + (2822735953919/1000000000000 : ℝ)*(sp_s0_20) + (17582089/1000000000000 : ℝ)*(sp_s0_23) + (564548956059/200000000000 : ℝ)*(f.failure) + (6311258728777/1000000000000 : ℝ)*(f.sum) + (411505685263799/1250000000000000000000000000 : ℝ)*base62 + (669182225489831/5000000000000000000000000000 : ℝ)*base65 + (829678346045027/5000000000000000000000000000 : ℝ)*base67 + (2866124155545027/5000000000000000000000000000 : ℝ)*base68 + (1144323037017429/2500000000000000000000000000 : ℝ)*base71 + (690334344010169/5000000000000000000000000000 : ℝ)*base73 + (966326349510169/5000000000000000000000000000 : ℝ)*base74 + (298558744954973/5000000000000000000000000000 : ℝ)*base76 + (456866010138799/1250000000000000000000000000 : ℝ)*base79 + (13787/20000000000000000 : ℝ)*base87 + (13787/20000000000000000 : ℝ)*base89 + (13787/20000000000000000 : ℝ)*base91 + (1/1000000000000 : ℝ)*base92 + hcertificate_margin
  have ratio_s0_2 : (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(1921/12500 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(1921/12500 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (21616218270770499147171/5000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1270299/1000000000000 : ℝ)*(base40) + (294587899679/500000000000 : ℝ)*(base49) + (721743998461/500000000000 : ℝ)*(base59) + (4273018681181/1000000000000 : ℝ)*(major_s0_0) + (4273018681181/1000000000000 : ℝ)*(major_s0_1) + (4273018681181/1000000000000 : ℝ)*(major_s0_2) + (12969803/1000000000000 : ℝ)*(sp_s0_0) + (19517249/500000000000 : ℝ)*(sp_s0_13) + (13527107/1000000000000 : ℝ)*(sp_s0_15) + (2484627/250000000000 : ℝ)*(sp_s0_16) + (1476245609003/250000000000 : ℝ)*(sp_s0_21) + (1476245469677/250000000000 : ℝ)*(sp_s0_22) + (5904985467307/1000000000000 : ℝ)*(sp_s0_23) + (660250370241/250000000000 : ℝ)*(sp_s0_27) + (1320520257731/500000000000 : ℝ)*(f.failure) + (1180999081163/200000000000 : ℝ)*(f.sum) + (1670885873170091/2500000000000000000000000000 : ℝ)*base63 + (2951712074770579/10000000000000000000000000000 : ℝ)*base64 + (5416673379450943/10000000000000000000000000000 : ℝ)*base66 + (4243412387549057/10000000000000000000000000000 : ℝ)*base68 + (732281011610761/5000000000000000000000000000 : ℝ)*base70 + (2235976502229421/10000000000000000000000000000 : ℝ)*base72 + (891756086229421/10000000000000000000000000000 : ℝ)*base75 + (8278619910450943/10000000000000000000000000000 : ℝ)*base76 + (329157619329909/2500000000000000000000000000 : ℝ)*base79 + (21683/50000000000000000 : ℝ)*base87 + (21683/50000000000000000 : ℝ)*base89 + (21683/50000000000000000 : ℝ)*base91 + hcertificate_margin
  have s1_pow0 : (29751/100000 : ℝ) ^ (35/8 : ℝ) ≤ (1988975122447039/400000000000000000 : ℝ) := by
    have hpowers : (29751/100000 : ℝ)^35 ≤ (1988975122447039/400000000000000000 : ℝ)^8 := by
      have hnat : (29751 : ℕ)^35*400000000000000000^8 ≤ 1988975122447039^8*100000^35 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        29751 100000 1988975122447039 400000000000000000 35 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (29751/100000 : ℝ)) (X := (1988975122447039/400000000000000000 : ℝ)) (by norm_num) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have s1_corner0a : (401988975122447039/400000000000000000 : ℝ) ≤ (10011343837422489/10000000000000000 : ℝ) ^ (35/8 : ℝ) := by
    have hpowers : (401988975122447039/400000000000000000 : ℝ)^8 ≤ (10011343837422489/10000000000000000 : ℝ)^35 := by
      have hnat : (401988975122447039 : ℕ)^8*10000000000000000^35 ≤ 10011343837422489^35*400000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        401988975122447039 400000000000000000 10011343837422489 10000000000000000 8 35 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10011343837422489/10000000000000000 : ℝ)) (X := (401988975122447039/400000000000000000 : ℝ)) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have s1_corner0b : (201988975122447039/200000000000000000 : ℝ) ≤ (1002264445882107/1000000000000000 : ℝ) ^ (35/8 : ℝ) := by
    have hpowers : (201988975122447039/200000000000000000 : ℝ)^8 ≤ (1002264445882107/1000000000000000 : ℝ)^35 := by
      have hnat : (201988975122447039 : ℕ)^8*1000000000000000^35 ≤ 1002264445882107^35*200000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        201988975122447039 200000000000000000 1002264445882107 1000000000000000 8 35 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1002264445882107/1000000000000000 : ℝ)) (X := (201988975122447039/200000000000000000 : ℝ)) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(11343837422489/2975100000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(3766873799527/991700000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (35/8 : ℝ)) (rho := (29751/100000 : ℝ)) (alpha := (11343837422489/2975100000000000 : ℝ)) (beta := (3766873799527/991700000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![false, false, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (29751/100000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(11343837422489/2975100000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(3766873799527/991700000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (35651/100000 : ℝ) ^ (35/8 : ℝ) ≤ (1097270638801971089/100000000000000000000 : ℝ) := by
    have hpowers : (35651/100000 : ℝ)^35 ≤ (1097270638801971089/100000000000000000000 : ℝ)^8 := by
      have hnat : (35651 : ℕ)^35*100000000000000000000^8 ≤ 1097270638801971089^8*100000^35 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        35651 100000 1097270638801971089 100000000000000000000 35 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (35651/100000 : ℝ)) (X := (1097270638801971089/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have s1_corner1a : (101097270638801971089/100000000000000000000 : ℝ) ≤ (626560937842897/625000000000000 : ℝ) ^ (35/8 : ℝ) := by
    have hpowers : (101097270638801971089/100000000000000000000 : ℝ)^8 ≤ (626560937842897/625000000000000 : ℝ)^35 := by
      have hnat : (101097270638801971089 : ℕ)^8*625000000000000^35 ≤ 626560937842897^35*100000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        101097270638801971089 100000000000000000000 626560937842897 625000000000000 8 35 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (626560937842897/625000000000000 : ℝ)) (X := (101097270638801971089/100000000000000000000 : ℝ)) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have s1_corner1b : (51097270638801971089/50000000000000000000 : ℝ) ≤ (1256217720988467/1250000000000000 : ℝ) ^ (35/8 : ℝ) := by
    have hpowers : (51097270638801971089/50000000000000000000 : ℝ)^8 ≤ (1256217720988467/1250000000000000 : ℝ)^35 := by
      have hnat : (51097270638801971089 : ℕ)^8*1250000000000000^35 ≤ 1256217720988467^35*50000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        51097270638801971089 50000000000000000000 1256217720988467 1250000000000000 8 35 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1256217720988467/1250000000000000 : ℝ)) (X := (51097270638801971089/50000000000000000000 : ℝ)) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(1560937842897/222818750000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2))+(3095845302673/445637500000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 2 0)) := by
    have hh := chart_majorant (a := (35/8 : ℝ)) (rho := (35651/100000 : ℝ)) (alpha := (1560937842897/222818750000000 : ℝ)) (beta := (3095845302673/445637500000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![false, false, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 2) ≤ (35651/100000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(1560937842897/222818750000000 : ℝ)*((1 : ℝ)*pair X 1 2)+(3095845302673/445637500000000 : ℝ)*((-1 : ℝ)*pair X 1 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (1921/12500 : ℝ) ^ (35/8 : ℝ) ≤ (27634455662239541/100000000000000000000 : ℝ) := by
    have hpowers : (1921/12500 : ℝ)^35 ≤ (27634455662239541/100000000000000000000 : ℝ)^8 := by
      have hnat : (1921 : ℕ)^35*100000000000000000000^8 ≤ 27634455662239541^8*12500^35 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1921 12500 27634455662239541 100000000000000000000 35 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1921/12500 : ℝ)) (X := (27634455662239541/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have s1_corner2a : (100027634455662239541/100000000000000000000 : ℝ) ≤ (12500789471731/12500000000000 : ℝ) ^ (35/8 : ℝ) := by
    have hpowers : (100027634455662239541/100000000000000000000 : ℝ)^8 ≤ (12500789471731/12500000000000 : ℝ)^35 := by
      have hnat : (100027634455662239541 : ℕ)^8*12500000000000^35 ≤ 12500789471731^35*100000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100027634455662239541 100000000000000000000 12500789471731 12500000000000 8 35 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12500789471731/12500000000000 : ℝ)) (X := (100027634455662239541/100000000000000000000 : ℝ)) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have s1_corner2b : (50027634455662239541/50000000000000000000 : ℝ) ≤ (5000631510090707/5000000000000000 : ℝ) ^ (35/8 : ℝ) := by
    have hpowers : (50027634455662239541/50000000000000000000 : ℝ)^8 ≤ (5000631510090707/5000000000000000 : ℝ)^35 := by
      have hnat : (50027634455662239541 : ℕ)^8*5000000000000000^35 ≤ 5000631510090707^35*50000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50027634455662239541 50000000000000000000 5000631510090707 5000000000000000 8 35 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000631510090707/5000000000000000 : ℝ)) (X := (50027634455662239541/50000000000000000000 : ℝ)) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(789471731/1921000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 1 0))+(315721398307/768400000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (35/8 : ℝ)) (rho := (1921/12500 : ℝ)) (alpha := (789471731/1921000000000 : ℝ)) (beta := (315721398307/768400000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![false, false, true]] hX 2 (by
        change ((-1 : ℝ)*pair X 2 0) ≤ (1921/12500 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(789471731/1921000000000 : ℝ)*((-1 : ℝ)*pair X 2 0)+(315721398307/768400000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-4387404071/10000000000 : ℝ)*X 0 0+(3496486717/10000000000 : ℝ)*X 0 1+(4890761277/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c310081_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_1 : ((70601327/156250000 : ℝ)*X 1 0+(-900237491/2500000000 : ℝ)*X 1 1+(1166635421/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c310081_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((1083459797/2500000000 : ℝ)*X 2 0+(2848881309/5000000000 : ℝ)*X 2 1+(-521645561/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c310081_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_6 : ((389918353/1250000000 : ℝ)*X 0 0+(820210301/2000000000 : ℝ)*X 0 1+(219665667/400000000 : ℝ)*X 0 2+(389918353/1250000000 : ℝ)*X 1 0+(820210301/2000000000 : ℝ)*X 1 1+(219665667/400000000 : ℝ)*X 1 2+(389918353/1250000000 : ℝ)*X 2 0+(820210301/2000000000 : ℝ)*X 2 1+(219665667/400000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c310081_s1_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have hsep : (-335379/50000 : ℝ) < ((-161793/100000 : ℝ)*P 0+(-161793/100000 : ℝ)*P 1+(-161793/100000 : ℝ)*P 2+(1 : ℝ)*T) := by
    have hcertificate_margin : (-335379/50000 : ℝ) < (-22498732863285327020739927012945741/3395857038035000000000000000000000 : ℝ) := by norm_num
    linear_combination (452907/1000000000000 : ℝ)*(base19) + (141529/100000000000 : ℝ)*(base23) + (151143/200000000000 : ℝ)*(base31) + (11082197617/250000000000 : ℝ)*(base40) + (168825096817/500000000000 : ℝ)*(base49) + (371212812431/500000000000 : ℝ)*(base59) + (153723279079/500000000000 : ℝ)*(base60) + (482641/1000000000000 : ℝ)*(ratio_s0_0) + (161793/100000 : ℝ)*(major_s1_0) + (161793/100000 : ℝ)*(major_s1_1) + (161793/100000 : ℝ)*(major_s1_2) + (1104224579699/500000000000 : ℝ)*(sp_s1_0) + (2208448706491/1000000000000 : ℝ)*(sp_s1_1) + (552111936027/250000000000 : ℝ)*(sp_s1_2) + (199999848857/200000000000 : ℝ)*(sp_s1_6) + (1104224579699/500000000000 : ℝ)*(f.sum) + (237419108065868339/342427855000000000000000000000 : ℝ)*base63 + (4956358724011/19210000000000000000000000 : ℝ)*base64 + (30418988052729/356510000000000000000000000 : ℝ)*base67 + (1187964179319/2401250000000000000000000 : ℝ)*base69 + (17224958779408757/190505570000000000000000000000 : ℝ)*base70 + (41760581987823/99170000000000000000000000 : ℝ)*base72 + (18763785913907/44563750000000000000000000 : ℝ)*base75 + (32588608764527/99170000000000000000000000 : ℝ)*base77 + (301491545948177729/707101934000000000000000000000 : ℝ)*base78 + hcertificate_margin
  linarith only [hsep,f.failure]

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem collision_support_c310084_s0_0 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-4204429383/10000000000 : ℝ)*x 0 + (-5184011673/10000000000 : ℝ)*x 1 + (840977859/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4204429383/10000000000 : ℝ)^71 ≤ (127643898769/390625000000 : ℝ)^55 := by
    have hnat : (4204429383 : ℕ)^71*390625000000^55 ≤ 127643898769^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4204429383 10000000000 127643898769 390625000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5184011673/10000000000 : ℝ)^71 ≤ (42821286190823/100000000000000 : ℝ)^55 := by
    have hnat : (5184011673 : ℕ)^71*100000000000000^55 ≤ 42821286190823^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5184011673 10000000000 42821286190823 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (840977859/2500000000 : ℝ)^71 ≤ (24501875707307/100000000000000 : ℝ)^55 := by
    have hnat : (840977859 : ℕ)^71*100000000000000^55 ≤ 24501875707307^55*2500000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      840977859 2500000000 24501875707307 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-4204429383/10000000000 : ℝ), (-5184011673/10000000000 : ℝ), (840977859/2500000000 : ℝ)] ![(127643898769/390625000000 : ℝ), (42821286190823/100000000000000 : ℝ), (24501875707307/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-4204429383/10000000000 : ℝ)|^71 ≤ (127643898769/390625000000 : ℝ)^55
        have hw : |(-4204429383/10000000000 : ℝ)|=(4204429383/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-5184011673/10000000000 : ℝ)|^71 ≤ (42821286190823/100000000000000 : ℝ)^55
        have hw : |(-5184011673/10000000000 : ℝ)|=(5184011673/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(840977859/2500000000 : ℝ)|^71 ≤ (24501875707307/100000000000000 : ℝ)^55
        have hw : |(840977859/2500000000 : ℝ)|=(840977859/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310084_s0_1 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (840977859/2500000000 : ℝ)*x 0 + (4204429383/10000000000 : ℝ)*x 1 + (5184011673/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (840977859/2500000000 : ℝ)^71 ≤ (24501875707307/100000000000000 : ℝ)^55 := by
    have hnat : (840977859 : ℕ)^71*100000000000000^55 ≤ 24501875707307^55*2500000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      840977859 2500000000 24501875707307 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4204429383/10000000000 : ℝ)^71 ≤ (127643898769/390625000000 : ℝ)^55 := by
    have hnat : (4204429383 : ℕ)^71*390625000000^55 ≤ 127643898769^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4204429383 10000000000 127643898769 390625000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5184011673/10000000000 : ℝ)^71 ≤ (42821286190823/100000000000000 : ℝ)^55 := by
    have hnat : (5184011673 : ℕ)^71*100000000000000^55 ≤ 42821286190823^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5184011673 10000000000 42821286190823 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(840977859/2500000000 : ℝ), (4204429383/10000000000 : ℝ), (5184011673/10000000000 : ℝ)] ![(24501875707307/100000000000000 : ℝ), (127643898769/390625000000 : ℝ), (42821286190823/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(840977859/2500000000 : ℝ)|^71 ≤ (24501875707307/100000000000000 : ℝ)^55
        have hw : |(840977859/2500000000 : ℝ)|=(840977859/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4204429383/10000000000 : ℝ)|^71 ≤ (127643898769/390625000000 : ℝ)^55
        have hw : |(4204429383/10000000000 : ℝ)|=(4204429383/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5184011673/10000000000 : ℝ)|^71 ≤ (42821286190823/100000000000000 : ℝ)^55
        have hw : |(5184011673/10000000000 : ℝ)|=(5184011673/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310084_s0_2 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5184011673/10000000000 : ℝ)*x 0 + (-840977859/2500000000 : ℝ)*x 1 + (-4204429383/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5184011673/10000000000 : ℝ)^71 ≤ (42821286190823/100000000000000 : ℝ)^55 := by
    have hnat : (5184011673 : ℕ)^71*100000000000000^55 ≤ 42821286190823^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5184011673 10000000000 42821286190823 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (840977859/2500000000 : ℝ)^71 ≤ (24501875707307/100000000000000 : ℝ)^55 := by
    have hnat : (840977859 : ℕ)^71*100000000000000^55 ≤ 24501875707307^55*2500000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      840977859 2500000000 24501875707307 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4204429383/10000000000 : ℝ)^71 ≤ (127643898769/390625000000 : ℝ)^55 := by
    have hnat : (4204429383 : ℕ)^71*390625000000^55 ≤ 127643898769^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4204429383 10000000000 127643898769 390625000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5184011673/10000000000 : ℝ), (-840977859/2500000000 : ℝ), (-4204429383/10000000000 : ℝ)] ![(42821286190823/100000000000000 : ℝ), (24501875707307/100000000000000 : ℝ), (127643898769/390625000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5184011673/10000000000 : ℝ)|^71 ≤ (42821286190823/100000000000000 : ℝ)^55
        have hw : |(5184011673/10000000000 : ℝ)|=(5184011673/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-840977859/2500000000 : ℝ)|^71 ≤ (24501875707307/100000000000000 : ℝ)^55
        have hw : |(-840977859/2500000000 : ℝ)|=(840977859/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-4204429383/10000000000 : ℝ)|^71 ≤ (127643898769/390625000000 : ℝ)^55
        have hw : |(-4204429383/10000000000 : ℝ)|=(4204429383/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310084_s0_6 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (133428637/312500000 : ℝ)*x 0 + (-133428637/312500000 : ℝ)*x 1 + (133428637/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (133428637/312500000 : ℝ)^71 ≤ (33333333326299/100000000000000 : ℝ)^55 := by
    have hnat : (133428637 : ℕ)^71*100000000000000^55 ≤ 33333333326299^55*312500000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      133428637 312500000 33333333326299 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (133428637/312500000 : ℝ)^71 ≤ (33333333326299/100000000000000 : ℝ)^55 := by
    have hnat : (133428637 : ℕ)^71*100000000000000^55 ≤ 33333333326299^55*312500000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      133428637 312500000 33333333326299 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (133428637/312500000 : ℝ)^71 ≤ (33333333326299/100000000000000 : ℝ)^55 := by
    have hnat : (133428637 : ℕ)^71*100000000000000^55 ≤ 33333333326299^55*312500000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      133428637 312500000 33333333326299 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(133428637/312500000 : ℝ), (-133428637/312500000 : ℝ), (133428637/312500000 : ℝ)] ![(33333333326299/100000000000000 : ℝ), (33333333326299/100000000000000 : ℝ), (33333333326299/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(133428637/312500000 : ℝ)|^71 ≤ (33333333326299/100000000000000 : ℝ)^55
        have hw : |(133428637/312500000 : ℝ)|=(133428637/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-133428637/312500000 : ℝ)|^71 ≤ (33333333326299/100000000000000 : ℝ)^55
        have hw : |(-133428637/312500000 : ℝ)|=(133428637/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(133428637/312500000 : ℝ)|^71 ≤ (33333333326299/100000000000000 : ℝ)^55
        have hw : |(133428637/312500000 : ℝ)|=(133428637/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c310084 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (161793/100000 : ℝ) (18111/10000 : ℝ) (2431/3125 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![true, false, false], ![false, false, true]]) : False := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (2431/3125 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (2431/3125 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (2431/3125 : ℝ)*P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (2431/3125 : ℝ)*P 1 ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((-1 : ℝ)*(X 0 2+X 2 2)) ∧ ((-1 : ℝ)*(X 0 2+X 2 2)) ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((-1 : ℝ)*pair X 1 2) ∧ ((-1 : ℝ)*pair X 1 2) ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (2431/3125 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (2431/3125 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((-1 : ℝ)*(X 0 1+X 1 1)) ∧ ((-1 : ℝ)*(X 0 1+X 1 1)) ≤ ((-1 : ℝ)*(X 0 0+X 1 0)) ∧ ((-1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((-1 : ℝ)*pair X 2 1) ∧ ((-1 : ℝ)*pair X 2 1) ≤ ((-1 : ℝ)*pair X 2 0) ∧ ((-1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base6 : ((-1 : ℝ)*T) ≤ (-1 : ℝ) := by
    linarith only [f.Tone]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base50 : ((1 : ℝ)*X 0 0+(1 : ℝ)*X 0 2+(1 : ℝ)*X 2 0+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.2.1]
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
  have s0_pow0 : (1 : ℝ) ^ (35/8 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^35 ≤ (1 : ℝ)^8 := by
      have hnat : (1 : ℕ)^35*1^8 ≤ 1^8*1^35 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 35 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have s0_corner0a : (2 : ℝ) ≤ (11716741708364597/10000000000000000 : ℝ) ^ (35/8 : ℝ) := by
    have hpowers : (2 : ℝ)^8 ≤ (11716741708364597/10000000000000000 : ℝ)^35 := by
      have hnat : (2 : ℕ)^8*10000000000000000^35 ≤ 11716741708364597^35*1^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 11716741708364597 10000000000000000 8 35 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11716741708364597/10000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have s0_corner0b : (3 : ℝ) ≤ (3213633126210889/2500000000000000 : ℝ) ^ (35/8 : ℝ) := by
    have hpowers : (3 : ℝ)^8 ≤ (3213633126210889/2500000000000000 : ℝ)^35 := by
      have hnat : (3 : ℕ)^8*2500000000000000^35 ≤ 3213633126210889^35*1^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 3213633126210889 2500000000000000 8 35 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (3213633126210889/2500000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have major_s0_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(1716741708364597/10000000000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(1137790796478959/10000000000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (35/8 : ℝ)) (rho := (1 : ℝ)) (alpha := (1716741708364597/10000000000000000 : ℝ)) (beta := (1137790796478959/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow0,s0_corner0a]) (by linarith only [s0_pow0,s0_corner0b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![true, false, false], ![false, false, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (1 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order0.2.2])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(1716741708364597/10000000000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(1137790796478959/10000000000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow1 : (1 : ℝ) ^ (35/8 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^35 ≤ (1 : ℝ)^8 := by
      have hnat : (1 : ℕ)^35*1^8 ≤ 1^8*1^35 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 35 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have s0_corner1a : (2 : ℝ) ≤ (11716741708364597/10000000000000000 : ℝ) ^ (35/8 : ℝ) := by
    have hpowers : (2 : ℝ)^8 ≤ (11716741708364597/10000000000000000 : ℝ)^35 := by
      have hnat : (2 : ℕ)^8*10000000000000000^35 ≤ 11716741708364597^35*1^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 11716741708364597 10000000000000000 8 35 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11716741708364597/10000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have s0_corner1b : (3 : ℝ) ≤ (3213633126210889/2500000000000000 : ℝ) ^ (35/8 : ℝ) := by
    have hpowers : (3 : ℝ)^8 ≤ (3213633126210889/2500000000000000 : ℝ)^35 := by
      have hnat : (3 : ℕ)^8*2500000000000000^35 ≤ 3213633126210889^35*1^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 3213633126210889 2500000000000000 8 35 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (3213633126210889/2500000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have major_s0_1 : P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1))+(1716741708364597/10000000000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2))+(1137790796478959/10000000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0)) := by
    have hh := chart_majorant (a := (35/8 : ℝ)) (rho := (1 : ℝ)) (alpha := (1716741708364597/10000000000000000 : ℝ)) (beta := (1137790796478959/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow1,s0_corner1a]) (by linarith only [s0_pow1,s0_corner1b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![true, false, false], ![false, false, true]] hX 1 (by
        change ((-1 : ℝ)*pair X 1 2) ≤ (1 : ℝ)*((-1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order1.2.2])
    change lpNorm p (pair X 1) ≤ ((-1 : ℝ)*pair X 1 1)+(1716741708364597/10000000000000000 : ℝ)*((-1 : ℝ)*pair X 1 2)+(1137790796478959/10000000000000000 : ℝ)*((1 : ℝ)*pair X 1 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow2 : (1 : ℝ) ^ (35/8 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^35 ≤ (1 : ℝ)^8 := by
      have hnat : (1 : ℕ)^35*1^8 ≤ 1^8*1^35 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 35 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have s0_corner2a : (2 : ℝ) ≤ (11716741708364597/10000000000000000 : ℝ) ^ (35/8 : ℝ) := by
    have hpowers : (2 : ℝ)^8 ≤ (11716741708364597/10000000000000000 : ℝ)^35 := by
      have hnat : (2 : ℕ)^8*10000000000000000^35 ≤ 11716741708364597^35*1^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 11716741708364597 10000000000000000 8 35 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11716741708364597/10000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have s0_corner2b : (3 : ℝ) ≤ (3213633126210889/2500000000000000 : ℝ) ^ (35/8 : ℝ) := by
    have hpowers : (3 : ℝ)^8 ≤ (3213633126210889/2500000000000000 : ℝ)^35 := by
      have hnat : (3 : ℕ)^8*2500000000000000^35 ≤ 3213633126210889^35*1^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 3213633126210889 2500000000000000 8 35 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (3213633126210889/2500000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have major_s0_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(1716741708364597/10000000000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 1 0))+(1137790796478959/10000000000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (35/8 : ℝ)) (rho := (1 : ℝ)) (alpha := (1716741708364597/10000000000000000 : ℝ)) (beta := (1137790796478959/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow2,s0_corner2a]) (by linarith only [s0_pow2,s0_corner2b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![true, false, false], ![false, false, true]] hX 2 (by
        change ((-1 : ℝ)*pair X 2 0) ≤ (1 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order2.2.2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(1716741708364597/10000000000000000 : ℝ)*((-1 : ℝ)*pair X 2 0)+(1137790796478959/10000000000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s0_0 : ((-4204429383/10000000000 : ℝ)*X 0 0+(-5184011673/10000000000 : ℝ)*X 0 1+(840977859/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c310084_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_1 : ((840977859/2500000000 : ℝ)*X 1 0+(4204429383/10000000000 : ℝ)*X 1 1+(5184011673/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c310084_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_2 : ((5184011673/10000000000 : ℝ)*X 2 0+(-840977859/2500000000 : ℝ)*X 2 1+(-4204429383/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c310084_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_6 : ((133428637/312500000 : ℝ)*X 0 0+(-133428637/312500000 : ℝ)*X 0 1+(133428637/312500000 : ℝ)*X 0 2+(133428637/312500000 : ℝ)*X 1 0+(-133428637/312500000 : ℝ)*X 1 1+(133428637/312500000 : ℝ)*X 1 2+(133428637/312500000 : ℝ)*X 2 0+(-133428637/312500000 : ℝ)*X 2 1+(133428637/312500000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c310084_s0_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have hsep : (-335379/50000 : ℝ) < ((-161793/100000 : ℝ)*P 0+(-161793/100000 : ℝ)*P 1+(-161793/100000 : ℝ)*P 2+(1 : ℝ)*T) := by
    have hcertificate_margin : (-335379/50000 : ℝ) < (-16530959201541217564869/2500000000000000000000 : ℝ) := by norm_num
    linear_combination (999999992013/1000000000000 : ℝ)*(base6) + (121648430579/250000000000 : ℝ)*(base40) + (121648430579/250000000000 : ℝ)*(base50) + (121648430579/250000000000 : ℝ)*(base60) + (161793/100000 : ℝ)*(major_s0_0) + (161793/100000 : ℝ)*(major_s0_1) + (161793/100000 : ℝ)*(major_s0_2) + (2537461224209/1000000000000 : ℝ)*(sp_s0_0) + (2537461224209/1000000000000 : ℝ)*(sp_s0_1) + (2537461224209/1000000000000 : ℝ)*(sp_s0_2) + (7987/1000000000000 : ℝ)*(sp_s0_6) + (2537461224209/1000000000000 : ℝ)*(f.sum) + (1884515301/10000000000000000000000 : ℝ)*base62 + (130236841/2000000000000000000000 : ℝ)*base64 + (113831329/5000000000000000000000 : ℝ)*base67 + (113831329/5000000000000000000000 : ℝ)*base69 + (1884515301/10000000000000000000000 : ℝ)*base71 + (130236841/2000000000000000000000 : ℝ)*base73 + (130236841/2000000000000000000000 : ℝ)*base75 + (113831329/5000000000000000000000 : ℝ)*base76 + (1884515301/10000000000000000000000 : ℝ)*base78 + hcertificate_margin
  linarith only [hsep,f.failure]

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
namespace HlawkaSchatten.DiagonalCutoff4
theorem coarse_distinct_p010_b036 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ))
    (c : Fin 88) (hlo : 81 ≤ c.val) (hhi : c.val < 85)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (161793/100000 : ℝ) (18111/10000 : ℝ) (2431/3125 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  have hc : c=81 ∨ c=82 ∨ c=83 ∨ c=84 := by omega
  rcases hc with rfl|rfl|rfl|rfl
  · exact collision_c310081 p hpa (by linarith only [hpb]) X hX
  · exact collision_c310082 p hpa (by linarith only [hpb]) X hX
  · exact collision_c310083 p hpa (by linarith only [hpb]) X hX
  · exact collision_c310084 p hpa (by linarith only [hpb]) X hX

end HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ))
    (c : Fin 88) (hlo : 81 ≤ c.val) (hhi : c.val < 85)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (161793/100000 : ℝ) (18111/10000 : ℝ) (2431/3125 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  exact HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p010_b036 p hpa hpb c hlo hhi hn63 hn87 X hX

#print axioms solution
