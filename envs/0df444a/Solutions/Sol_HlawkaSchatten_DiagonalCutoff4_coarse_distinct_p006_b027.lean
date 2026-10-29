-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p006_b027
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T20:55:39.868111+00:00
-- url     : https://prove2.me/submissions/3f8ab4c0-8bf5-41e4-8554-acf5dd2ac3f4

import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c306062_s0
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c306062_s1
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c306062_s2
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c306062_s3
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c306062_s4
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c306062_s5
import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
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
theorem HlawkaSchatten.DiagonalCutoff4.collision_c306062 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (77093/50000 : ℝ) (92997/50000 : ℝ) (38461/50000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, false]]) : False := by
  have h0 := collision_c306062_s0 p hpa hpb X hX
  have h1 := collision_c306062_s1 p hpa hpb X hX h0
  have h2 := collision_c306062_s2 p hpa hpb X hX h1
  have h3 := collision_c306062_s3 p hpa hpb X hX h2
  have h4 := collision_c306062_s4 p hpa hpb X hX h3
  exact collision_c306062_s5 p hpa hpb X hX h4

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
theorem collision_support_c306064_s0_0 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-811282499/2500000000 : ℝ)*x 0 + (-1884514451/5000000000 : ℝ)*x 1 + (-5828905639/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (811282499/2500000000 : ℝ)^135 ≤ (22876094243971/100000000000000 : ℝ)^103 := by
    have hnat : (811282499 : ℕ)^135*100000000000000^103 ≤ 22876094243971^103*2500000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      811282499 2500000000 22876094243971 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1884514451/5000000000 : ℝ)^135 ≤ (5566761295697/20000000000000 : ℝ)^103 := by
    have hnat : (1884514451 : ℕ)^135*20000000000000^103 ≤ 5566761295697^103*5000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1884514451 5000000000 5566761295697 20000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5828905639/10000000000 : ℝ)^135 ≤ (24645049629333/50000000000000 : ℝ)^103 := by
    have hnat : (5828905639 : ℕ)^135*50000000000000^103 ≤ 24645049629333^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5828905639 10000000000 24645049629333 50000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-811282499/2500000000 : ℝ), (-1884514451/5000000000 : ℝ), (-5828905639/10000000000 : ℝ)] ![(22876094243971/100000000000000 : ℝ), (5566761295697/20000000000000 : ℝ), (24645049629333/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-811282499/2500000000 : ℝ)|^135 ≤ (22876094243971/100000000000000 : ℝ)^103
        have hw : |(-811282499/2500000000 : ℝ)|=(811282499/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1884514451/5000000000 : ℝ)|^135 ≤ (5566761295697/20000000000000 : ℝ)^103
        have hw : |(-1884514451/5000000000 : ℝ)|=(1884514451/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-5828905639/10000000000 : ℝ)|^135 ≤ (24645049629333/50000000000000 : ℝ)^103
        have hw : |(-5828905639/10000000000 : ℝ)|=(5828905639/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306064_s0_2 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (6604084117/10000000000 : ℝ)*x 0 + (-3629504417/10000000000 : ℝ)*x 1 + (2405950561/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6604084117/10000000000 : ℝ)^135 ≤ (3628374123487/6250000000000 : ℝ)^103 := by
    have hnat : (6604084117 : ℕ)^135*6250000000000^103 ≤ 3628374123487^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6604084117 10000000000 3628374123487 6250000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3629504417/10000000000 : ℝ)^135 ≤ (26491153459051/100000000000000 : ℝ)^103 := by
    have hnat : (3629504417 : ℕ)^135*100000000000000^103 ≤ 26491153459051^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3629504417 10000000000 26491153459051 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2405950561/10000000000 : ℝ)^135 ≤ (7727430276491/50000000000000 : ℝ)^103 := by
    have hnat : (2405950561 : ℕ)^135*50000000000000^103 ≤ 7727430276491^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2405950561 10000000000 7727430276491 50000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6604084117/10000000000 : ℝ), (-3629504417/10000000000 : ℝ), (2405950561/10000000000 : ℝ)] ![(3628374123487/6250000000000 : ℝ), (26491153459051/100000000000000 : ℝ), (7727430276491/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6604084117/10000000000 : ℝ)|^135 ≤ (3628374123487/6250000000000 : ℝ)^103
        have hw : |(6604084117/10000000000 : ℝ)|=(6604084117/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3629504417/10000000000 : ℝ)|^135 ≤ (26491153459051/100000000000000 : ℝ)^103
        have hw : |(-3629504417/10000000000 : ℝ)|=(3629504417/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2405950561/10000000000 : ℝ)|^135 ≤ (7727430276491/50000000000000 : ℝ)^103
        have hw : |(2405950561/10000000000 : ℝ)|=(2405950561/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306064_s0_3 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (1 : ℝ)*x 0 + (0 : ℝ)*x 1 + (0 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1 : ℝ)^135 ≤ (1 : ℝ)^103 := by
    have hnat : (1 : ℕ)^135*1^103 ≤ 1^103*1^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1 1 1 1 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (0 : ℝ)^135 ≤ (0 : ℝ)^103 := by
    have hnat : (0 : ℕ)^135*1^103 ≤ 0^103*1^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      0 1 0 1 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (0 : ℝ)^135 ≤ (0 : ℝ)^103 := by
    have hnat : (0 : ℕ)^135*1^103 ≤ 0^103*1^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      0 1 0 1 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1 : ℝ), (0 : ℝ), (0 : ℝ)] ![(1 : ℝ), (0 : ℝ), (0 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1 : ℝ)|^135 ≤ (1 : ℝ)^103
        have hw : |(1 : ℝ)|=(1 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(0 : ℝ)|^135 ≤ (0 : ℝ)^103
        have hw : |(0 : ℝ)|=(0 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(0 : ℝ)|^135 ≤ (0 : ℝ)^103
        have hw : |(0 : ℝ)|=(0 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306064_s0_7 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-159020563/500000000 : ℝ)*x 0 + (-76641177/200000000 : ℝ)*x 1 + (-582750223/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (159020563/500000000 : ℝ)^135 ≤ (22279989496063/100000000000000 : ℝ)^103 := by
    have hnat : (159020563 : ℕ)^135*100000000000000^103 ≤ 22279989496063^103*500000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      159020563 500000000 22279989496063 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (76641177/200000000 : ℝ)^135 ≤ (2844546505223/10000000000000 : ℝ)^103 := by
    have hnat : (76641177 : ℕ)^135*10000000000000^103 ≤ 2844546505223^103*200000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      76641177 200000000 2844546505223 10000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (582750223/1000000000 : ℝ)^135 ≤ (3079659089567/6250000000000 : ℝ)^103 := by
    have hnat : (582750223 : ℕ)^135*6250000000000^103 ≤ 3079659089567^103*1000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      582750223 1000000000 3079659089567 6250000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-159020563/500000000 : ℝ), (-76641177/200000000 : ℝ), (-582750223/1000000000 : ℝ)] ![(22279989496063/100000000000000 : ℝ), (2844546505223/10000000000000 : ℝ), (3079659089567/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-159020563/500000000 : ℝ)|^135 ≤ (22279989496063/100000000000000 : ℝ)^103
        have hw : |(-159020563/500000000 : ℝ)|=(159020563/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-76641177/200000000 : ℝ)|^135 ≤ (2844546505223/10000000000000 : ℝ)^103
        have hw : |(-76641177/200000000 : ℝ)|=(76641177/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-582750223/1000000000 : ℝ)|^135 ≤ (3079659089567/6250000000000 : ℝ)^103
        have hw : |(-582750223/1000000000 : ℝ)|=(582750223/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306064_s0_8 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (213564629/625000000 : ℝ)*x 0 + (6051756333/10000000000 : ℝ)*x 1 + (-1669545879/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (213564629/625000000 : ℝ)^135 ≤ (12238654106991/50000000000000 : ℝ)^103 := by
    have hnat : (213564629 : ℕ)^135*50000000000000^103 ≤ 12238654106991^103*625000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      213564629 625000000 12238654106991 50000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6051756333/10000000000 : ℝ)^135 ≤ (51774562976849/100000000000000 : ℝ)^103 := by
    have hnat : (6051756333 : ℕ)^135*100000000000000^103 ≤ 51774562976849^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6051756333 10000000000 51774562976849 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1669545879/5000000000 : ℝ)^135 ≤ (11874064394551/50000000000000 : ℝ)^103 := by
    have hnat : (1669545879 : ℕ)^135*50000000000000^103 ≤ 11874064394551^103*5000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1669545879 5000000000 11874064394551 50000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(213564629/625000000 : ℝ), (6051756333/10000000000 : ℝ), (-1669545879/5000000000 : ℝ)] ![(12238654106991/50000000000000 : ℝ), (51774562976849/100000000000000 : ℝ), (11874064394551/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(213564629/625000000 : ℝ)|^135 ≤ (12238654106991/50000000000000 : ℝ)^103
        have hw : |(213564629/625000000 : ℝ)|=(213564629/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6051756333/10000000000 : ℝ)|^135 ≤ (51774562976849/100000000000000 : ℝ)^103
        have hw : |(6051756333/10000000000 : ℝ)|=(6051756333/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1669545879/5000000000 : ℝ)|^135 ≤ (11874064394551/50000000000000 : ℝ)^103
        have hw : |(-1669545879/5000000000 : ℝ)|=(1669545879/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306064_s0_9 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (6499578891/10000000000 : ℝ)*x 0 + (-12837527/39062500 : ℝ)*x 1 + (2916526689/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6499578891/10000000000 : ℝ)^135 ≤ (56852880331699/100000000000000 : ℝ)^103 := by
    have hnat : (6499578891 : ℕ)^135*100000000000000^103 ≤ 56852880331699^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6499578891 10000000000 56852880331699 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (12837527/39062500 : ℝ)^135 ≤ (11629110890823/50000000000000 : ℝ)^103 := by
    have hnat : (12837527 : ℕ)^135*50000000000000^103 ≤ 11629110890823^103*39062500^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      12837527 39062500 11629110890823 50000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2916526689/10000000000 : ℝ)^135 ≤ (9944448936297/50000000000000 : ℝ)^103 := by
    have hnat : (2916526689 : ℕ)^135*50000000000000^103 ≤ 9944448936297^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2916526689 10000000000 9944448936297 50000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6499578891/10000000000 : ℝ), (-12837527/39062500 : ℝ), (2916526689/10000000000 : ℝ)] ![(56852880331699/100000000000000 : ℝ), (11629110890823/50000000000000 : ℝ), (9944448936297/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6499578891/10000000000 : ℝ)|^135 ≤ (56852880331699/100000000000000 : ℝ)^103
        have hw : |(6499578891/10000000000 : ℝ)|=(6499578891/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-12837527/39062500 : ℝ)|^135 ≤ (11629110890823/50000000000000 : ℝ)^103
        have hw : |(-12837527/39062500 : ℝ)|=(12837527/39062500 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2916526689/10000000000 : ℝ)|^135 ≤ (9944448936297/50000000000000 : ℝ)^103
        have hw : |(2916526689/10000000000 : ℝ)|=(2916526689/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306064_s0_14 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-2830570523/10000000000 : ℝ)*x 0 + (-3005358413/10000000000 : ℝ)*x 1 + (-84857653/125000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2830570523/10000000000 : ℝ)^135 ≤ (3824832282409/20000000000000 : ℝ)^103 := by
    have hnat : (2830570523 : ℕ)^135*20000000000000^103 ≤ 3824832282409^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2830570523 10000000000 3824832282409 20000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3005358413/10000000000 : ℝ)^135 ≤ (20686608206463/100000000000000 : ℝ)^103 := by
    have hnat : (3005358413 : ℕ)^135*100000000000000^103 ≤ 20686608206463^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3005358413 10000000000 20686608206463 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (84857653/125000000 : ℝ)^135 ≤ (30094615186249/50000000000000 : ℝ)^103 := by
    have hnat : (84857653 : ℕ)^135*50000000000000^103 ≤ 30094615186249^103*125000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      84857653 125000000 30094615186249 50000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2830570523/10000000000 : ℝ), (-3005358413/10000000000 : ℝ), (-84857653/125000000 : ℝ)] ![(3824832282409/20000000000000 : ℝ), (20686608206463/100000000000000 : ℝ), (30094615186249/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2830570523/10000000000 : ℝ)|^135 ≤ (3824832282409/20000000000000 : ℝ)^103
        have hw : |(-2830570523/10000000000 : ℝ)|=(2830570523/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3005358413/10000000000 : ℝ)|^135 ≤ (20686608206463/100000000000000 : ℝ)^103
        have hw : |(-3005358413/10000000000 : ℝ)|=(3005358413/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-84857653/125000000 : ℝ)|^135 ≤ (30094615186249/50000000000000 : ℝ)^103
        have hw : |(-84857653/125000000 : ℝ)|=(84857653/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306064_s0_15 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (556825253/1250000000 : ℝ)*x 0 + (5345598133/10000000000 : ℝ)*x 1 + (-3078215491/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (556825253/1250000000 : ℝ)^135 ≤ (34649821256641/100000000000000 : ℝ)^103 := by
    have hnat : (556825253 : ℕ)^135*100000000000000^103 ≤ 34649821256641^103*1250000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      556825253 1250000000 34649821256641 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5345598133/10000000000 : ℝ)^135 ≤ (44003812428853/100000000000000 : ℝ)^103 := by
    have hnat : (5345598133 : ℕ)^135*100000000000000^103 ≤ 44003812428853^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5345598133 10000000000 44003812428853 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3078215491/10000000000 : ℝ)^135 ≤ (21346366295943/100000000000000 : ℝ)^103 := by
    have hnat : (3078215491 : ℕ)^135*100000000000000^103 ≤ 21346366295943^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3078215491 10000000000 21346366295943 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(556825253/1250000000 : ℝ), (5345598133/10000000000 : ℝ), (-3078215491/10000000000 : ℝ)] ![(34649821256641/100000000000000 : ℝ), (44003812428853/100000000000000 : ℝ), (21346366295943/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(556825253/1250000000 : ℝ)|^135 ≤ (34649821256641/100000000000000 : ℝ)^103
        have hw : |(556825253/1250000000 : ℝ)|=(556825253/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5345598133/10000000000 : ℝ)|^135 ≤ (44003812428853/100000000000000 : ℝ)^103
        have hw : |(5345598133/10000000000 : ℝ)|=(5345598133/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3078215491/10000000000 : ℝ)|^135 ≤ (21346366295943/100000000000000 : ℝ)^103
        have hw : |(-3078215491/10000000000 : ℝ)|=(3078215491/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306064_s0_16 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (299741943/400000000 : ℝ)*x 0 + (-306251313/1000000000 : ℝ)*x 1 + (1763521149/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (299741943/400000000 : ℝ)^135 ≤ (535236259187/781250000000 : ℝ)^103 := by
    have hnat : (299741943 : ℕ)^135*781250000000^103 ≤ 535236259187^103*400000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      299741943 400000000 535236259187 781250000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (306251313/1000000000 : ℝ)^135 ≤ (21203758995019/100000000000000 : ℝ)^103 := by
    have hnat : (306251313 : ℕ)^135*100000000000000^103 ≤ 21203758995019^103*1000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      306251313 1000000000 21203758995019 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1763521149/10000000000 : ℝ)^135 ≤ (5142999908327/50000000000000 : ℝ)^103 := by
    have hnat : (1763521149 : ℕ)^135*50000000000000^103 ≤ 5142999908327^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1763521149 10000000000 5142999908327 50000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(299741943/400000000 : ℝ), (-306251313/1000000000 : ℝ), (1763521149/10000000000 : ℝ)] ![(535236259187/781250000000 : ℝ), (21203758995019/100000000000000 : ℝ), (5142999908327/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(299741943/400000000 : ℝ)|^135 ≤ (535236259187/781250000000 : ℝ)^103
        have hw : |(299741943/400000000 : ℝ)|=(299741943/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-306251313/1000000000 : ℝ)|^135 ≤ (21203758995019/100000000000000 : ℝ)^103
        have hw : |(-306251313/1000000000 : ℝ)|=(306251313/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1763521149/10000000000 : ℝ)|^135 ≤ (5142999908327/50000000000000 : ℝ)^103
        have hw : |(1763521149/10000000000 : ℝ)|=(1763521149/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306064_s0_20 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-1841451669/5000000000 : ℝ)*x 0 + (-2251782941/5000000000 : ℝ)*x 1 + (-1191224233/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1841451669/5000000000 : ℝ)^135 ≤ (5400630855363/20000000000000 : ℝ)^103 := by
    have hnat : (1841451669 : ℕ)^135*20000000000000^103 ≤ 5400630855363^103*5000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1841451669 5000000000 5400630855363 20000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2251782941/5000000000 : ℝ)^135 ≤ (35149859599669/100000000000000 : ℝ)^103 := by
    have hnat : (2251782941 : ℕ)^135*100000000000000^103 ≤ 35149859599669^103*5000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2251782941 5000000000 35149859599669 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1191224233/2500000000 : ℝ)^135 ≤ (37846986110751/100000000000000 : ℝ)^103 := by
    have hnat : (1191224233 : ℕ)^135*100000000000000^103 ≤ 37846986110751^103*2500000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1191224233 2500000000 37846986110751 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1841451669/5000000000 : ℝ), (-2251782941/5000000000 : ℝ), (-1191224233/2500000000 : ℝ)] ![(5400630855363/20000000000000 : ℝ), (35149859599669/100000000000000 : ℝ), (37846986110751/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1841451669/5000000000 : ℝ)|^135 ≤ (5400630855363/20000000000000 : ℝ)^103
        have hw : |(-1841451669/5000000000 : ℝ)|=(1841451669/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2251782941/5000000000 : ℝ)|^135 ≤ (35149859599669/100000000000000 : ℝ)^103
        have hw : |(-2251782941/5000000000 : ℝ)|=(2251782941/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1191224233/2500000000 : ℝ)|^135 ≤ (37846986110751/100000000000000 : ℝ)^103
        have hw : |(-1191224233/2500000000 : ℝ)|=(1191224233/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306064_s0_21 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (293114669/1000000000 : ℝ)*x 0 + (1217267253/2000000000 : ℝ)*x 1 + (-941840323/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (293114669/1000000000 : ℝ)^135 ≤ (4003934673323/20000000000000 : ℝ)^103 := by
    have hnat : (293114669 : ℕ)^135*20000000000000^103 ≤ 4003934673323^103*1000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      293114669 1000000000 4003934673323 20000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1217267253/2000000000 : ℝ)^135 ≤ (10432532033451/20000000000000 : ℝ)^103 := by
    have hnat : (1217267253 : ℕ)^135*20000000000000^103 ≤ 10432532033451^103*2000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1217267253 2000000000 10432532033451 20000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (941840323/2500000000 : ℝ)^135 ≤ (13908833224627/50000000000000 : ℝ)^103 := by
    have hnat : (941840323 : ℕ)^135*50000000000000^103 ≤ 13908833224627^103*2500000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      941840323 2500000000 13908833224627 50000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(293114669/1000000000 : ℝ), (1217267253/2000000000 : ℝ), (-941840323/2500000000 : ℝ)] ![(4003934673323/20000000000000 : ℝ), (10432532033451/20000000000000 : ℝ), (13908833224627/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(293114669/1000000000 : ℝ)|^135 ≤ (4003934673323/20000000000000 : ℝ)^103
        have hw : |(293114669/1000000000 : ℝ)|=(293114669/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1217267253/2000000000 : ℝ)|^135 ≤ (10432532033451/20000000000000 : ℝ)^103
        have hw : |(1217267253/2000000000 : ℝ)|=(1217267253/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-941840323/2500000000 : ℝ)|^135 ≤ (13908833224627/50000000000000 : ℝ)^103
        have hw : |(-941840323/2500000000 : ℝ)|=(941840323/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306064_s0_22 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (757057723/1000000000 : ℝ)*x 0 + (-2921623503/10000000000 : ℝ)*x 1 + (361689227/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (757057723/1000000000 : ℝ)^135 ≤ (69434743747091/100000000000000 : ℝ)^103 := by
    have hnat : (757057723 : ℕ)^135*100000000000000^103 ≤ 69434743747091^103*1000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      757057723 1000000000 69434743747091 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2921623503/10000000000 : ℝ)^135 ≤ (2491808207277/12500000000000 : ℝ)^103 := by
    have hnat : (2921623503 : ℕ)^135*12500000000000^103 ≤ 2491808207277^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2921623503 10000000000 2491808207277 12500000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (361689227/2000000000 : ℝ)^135 ≤ (10630790583337/100000000000000 : ℝ)^103 := by
    have hnat : (361689227 : ℕ)^135*100000000000000^103 ≤ 10630790583337^103*2000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      361689227 2000000000 10630790583337 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(757057723/1000000000 : ℝ), (-2921623503/10000000000 : ℝ), (361689227/2000000000 : ℝ)] ![(69434743747091/100000000000000 : ℝ), (2491808207277/12500000000000 : ℝ), (10630790583337/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(757057723/1000000000 : ℝ)|^135 ≤ (69434743747091/100000000000000 : ℝ)^103
        have hw : |(757057723/1000000000 : ℝ)|=(757057723/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2921623503/10000000000 : ℝ)|^135 ≤ (2491808207277/12500000000000 : ℝ)^103
        have hw : |(-2921623503/10000000000 : ℝ)|=(2921623503/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(361689227/2000000000 : ℝ)|^135 ≤ (10630790583337/100000000000000 : ℝ)^103
        have hw : |(361689227/2000000000 : ℝ)|=(361689227/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306064_s1_0 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-3705115207/10000000000 : ℝ)*x 0 + (-3705115307/10000000000 : ℝ)*x 1 + (-1372456023/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3705115207/10000000000 : ℝ)^135 ≤ (3402101091169/12500000000000 : ℝ)^103 := by
    have hnat : (3705115207 : ℕ)^135*12500000000000^103 ≤ 3402101091169^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3705115207 10000000000 3402101091169 12500000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3705115307/10000000000 : ℝ)^135 ≤ (27216809692143/100000000000000 : ℝ)^103 := by
    have hnat : (3705115307 : ℕ)^135*100000000000000^103 ≤ 27216809692143^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3705115307 10000000000 27216809692143 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1372456023/2500000000 : ℝ)^135 ≤ (45566381566547/100000000000000 : ℝ)^103 := by
    have hnat : (1372456023 : ℕ)^135*100000000000000^103 ≤ 45566381566547^103*2500000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1372456023 2500000000 45566381566547 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-3705115207/10000000000 : ℝ), (-3705115307/10000000000 : ℝ), (-1372456023/2500000000 : ℝ)] ![(3402101091169/12500000000000 : ℝ), (27216809692143/100000000000000 : ℝ), (45566381566547/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-3705115207/10000000000 : ℝ)|^135 ≤ (3402101091169/12500000000000 : ℝ)^103
        have hw : |(-3705115207/10000000000 : ℝ)|=(3705115207/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3705115307/10000000000 : ℝ)|^135 ≤ (27216809692143/100000000000000 : ℝ)^103
        have hw : |(-3705115307/10000000000 : ℝ)|=(3705115307/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1372456023/2500000000 : ℝ)|^135 ≤ (45566381566547/100000000000000 : ℝ)^103
        have hw : |(-1372456023/2500000000 : ℝ)|=(1372456023/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306064_s1_1 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (4752688461/10000000000 : ℝ)*x 0 + (4752688589/10000000000 : ℝ)*x 1 + (-137034029/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4752688461/10000000000 : ℝ)^135 ≤ (4714992454421/12500000000000 : ℝ)^103 := by
    have hnat : (4752688461 : ℕ)^135*12500000000000^103 ≤ 4714992454421^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4752688461 10000000000 4714992454421 12500000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4752688589/10000000000 : ℝ)^135 ≤ (18859970483429/50000000000000 : ℝ)^103 := by
    have hnat : (4752688589 : ℕ)^135*50000000000000^103 ≤ 18859970483429^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4752688589 10000000000 18859970483429 50000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (137034029/400000000 : ℝ)^135 ≤ (2456011939259/10000000000000 : ℝ)^103 := by
    have hnat : (137034029 : ℕ)^135*10000000000000^103 ≤ 2456011939259^103*400000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      137034029 400000000 2456011939259 10000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4752688461/10000000000 : ℝ), (4752688589/10000000000 : ℝ), (-137034029/400000000 : ℝ)] ![(4714992454421/12500000000000 : ℝ), (18859970483429/50000000000000 : ℝ), (2456011939259/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4752688461/10000000000 : ℝ)|^135 ≤ (4714992454421/12500000000000 : ℝ)^103
        have hw : |(4752688461/10000000000 : ℝ)|=(4752688461/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4752688589/10000000000 : ℝ)|^135 ≤ (18859970483429/50000000000000 : ℝ)^103
        have hw : |(4752688589/10000000000 : ℝ)|=(4752688589/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-137034029/400000000 : ℝ)|^135 ≤ (2456011939259/10000000000000 : ℝ)^103
        have hw : |(-137034029/400000000 : ℝ)|=(137034029/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306064_s1_2 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (4752688461/10000000000 : ℝ)*x 0 + (-4752688589/10000000000 : ℝ)*x 1 + (137034029/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4752688461/10000000000 : ℝ)^135 ≤ (4714992454421/12500000000000 : ℝ)^103 := by
    have hnat : (4752688461 : ℕ)^135*12500000000000^103 ≤ 4714992454421^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4752688461 10000000000 4714992454421 12500000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4752688589/10000000000 : ℝ)^135 ≤ (18859970483429/50000000000000 : ℝ)^103 := by
    have hnat : (4752688589 : ℕ)^135*50000000000000^103 ≤ 18859970483429^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4752688589 10000000000 18859970483429 50000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (137034029/400000000 : ℝ)^135 ≤ (2456011939259/10000000000000 : ℝ)^103 := by
    have hnat : (137034029 : ℕ)^135*10000000000000^103 ≤ 2456011939259^103*400000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      137034029 400000000 2456011939259 10000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4752688461/10000000000 : ℝ), (-4752688589/10000000000 : ℝ), (137034029/400000000 : ℝ)] ![(4714992454421/12500000000000 : ℝ), (18859970483429/50000000000000 : ℝ), (2456011939259/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4752688461/10000000000 : ℝ)|^135 ≤ (4714992454421/12500000000000 : ℝ)^103
        have hw : |(4752688461/10000000000 : ℝ)|=(4752688461/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-4752688589/10000000000 : ℝ)|^135 ≤ (18859970483429/50000000000000 : ℝ)^103
        have hw : |(-4752688589/10000000000 : ℝ)|=(4752688589/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(137034029/400000000 : ℝ)|^135 ≤ (2456011939259/10000000000000 : ℝ)^103
        have hw : |(137034029/400000000 : ℝ)|=(137034029/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306064_s1_6 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (3705115207/10000000000 : ℝ)*x 0 + (-3705115307/10000000000 : ℝ)*x 1 + (-1372456023/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3705115207/10000000000 : ℝ)^135 ≤ (3402101091169/12500000000000 : ℝ)^103 := by
    have hnat : (3705115207 : ℕ)^135*12500000000000^103 ≤ 3402101091169^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3705115207 10000000000 3402101091169 12500000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3705115307/10000000000 : ℝ)^135 ≤ (27216809692143/100000000000000 : ℝ)^103 := by
    have hnat : (3705115307 : ℕ)^135*100000000000000^103 ≤ 27216809692143^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3705115307 10000000000 27216809692143 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1372456023/2500000000 : ℝ)^135 ≤ (45566381566547/100000000000000 : ℝ)^103 := by
    have hnat : (1372456023 : ℕ)^135*100000000000000^103 ≤ 45566381566547^103*2500000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1372456023 2500000000 45566381566547 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3705115207/10000000000 : ℝ), (-3705115307/10000000000 : ℝ), (-1372456023/2500000000 : ℝ)] ![(3402101091169/12500000000000 : ℝ), (27216809692143/100000000000000 : ℝ), (45566381566547/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3705115207/10000000000 : ℝ)|^135 ≤ (3402101091169/12500000000000 : ℝ)^103
        have hw : |(3705115207/10000000000 : ℝ)|=(3705115207/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3705115307/10000000000 : ℝ)|^135 ≤ (27216809692143/100000000000000 : ℝ)^103
        have hw : |(-3705115307/10000000000 : ℝ)|=(3705115307/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1372456023/2500000000 : ℝ)|^135 ≤ (45566381566547/100000000000000 : ℝ)^103
        have hw : |(-1372456023/2500000000 : ℝ)|=(1372456023/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c306064 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (77093/50000 : ℝ) (92997/50000 : ℝ) (38461/50000 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, false], ![false, false, false]]) : False := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (38461/50000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (38461/50000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (38461/50000 : ℝ)*P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (38461/50000 : ℝ)*P 1 ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 0+X 2 0)) ∧ ((-1 : ℝ)*(X 0 0+X 2 0)) ≤ ((-1 : ℝ)*(X 0 2+X 2 2)) ∧ ((-1 : ℝ)*(X 0 2+X 2 2)) ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 0) ∧ ((-1 : ℝ)*pair X 1 0) ≤ ((-1 : ℝ)*pair X 1 2) ∧ ((-1 : ℝ)*pair X 1 2) ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (38461/50000 : ℝ)*P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (38461/50000 : ℝ)*P 2 ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((-1 : ℝ)*(X 0 1+X 1 1)) ∧ ((-1 : ℝ)*(X 0 1+X 1 1)) ≤ ((-1 : ℝ)*(X 0 0+X 1 0)) ∧ ((-1 : ℝ)*(X 0 0+X 1 0)) ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((-1 : ℝ)*pair X 2 1) ∧ ((-1 : ℝ)*pair X 2 1) ≤ ((-1 : ℝ)*pair X 2 0) ∧ ((-1 : ℝ)*pair X 2 0) ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base1 : ((1 : ℝ)*N 0+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 0]
  have base7 : ((1 : ℝ)*T) ≤ (92997/50000 : ℝ) := by
    linarith only [f.Tcap]
  have base12 : ((-1 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 2).1]
  have base17 : ((1 : ℝ)*X 1 1+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 1).2]
  have base21 : ((1 : ℝ)*X 2 0+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 0).2]
  have base22 : ((-1 : ℝ)*X 2 1+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 1).1]
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base49 : ((1 : ℝ)*X 0 0+(1 : ℝ)*X 2 0) ≤ (0 : ℝ) := by
    linarith only [order1.1]
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
  have s0_pow0 : (1 : ℝ) ^ (67/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^67 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^67*1^16 ≤ 1^16*1^67 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 67 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have s0_corner0a : (2 : ℝ) ≤ (2360031261787197/2000000000000000 : ℝ) ^ (67/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (2360031261787197/2000000000000000 : ℝ)^67 := by
      have hnat : (2 : ℕ)^16*2000000000000000^67 ≤ 2360031261787197^67*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 2360031261787197 2000000000000000 16 67 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2360031261787197/2000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have s0_corner0b : (3 : ℝ) ≤ (12999881816832461/10000000000000000 : ℝ) ^ (67/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (12999881816832461/10000000000000000 : ℝ)^67 := by
      have hnat : (3 : ℕ)^16*10000000000000000^67 ≤ 12999881816832461^67*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 12999881816832461 10000000000000000 16 67 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12999881816832461/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have major_s0_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(360031261787197/2000000000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(299931376974119/2500000000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (67/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (360031261787197/2000000000000000 : ℝ)) (beta := (299931376974119/2500000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow0,s0_corner0a]) (by linarith only [s0_pow0,s0_corner0b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, false], ![false, false, false]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (1 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order0.2.2])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(360031261787197/2000000000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(299931376974119/2500000000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow1 : (1 : ℝ) ^ (67/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^67 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^67*1^16 ≤ 1^16*1^67 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 67 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have s0_corner1a : (2 : ℝ) ≤ (2360031261787197/2000000000000000 : ℝ) ^ (67/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (2360031261787197/2000000000000000 : ℝ)^67 := by
      have hnat : (2 : ℕ)^16*2000000000000000^67 ≤ 2360031261787197^67*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 2360031261787197 2000000000000000 16 67 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2360031261787197/2000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have s0_corner1b : (3 : ℝ) ≤ (12999881816832461/10000000000000000 : ℝ) ^ (67/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (12999881816832461/10000000000000000 : ℝ)^67 := by
      have hnat : (3 : ℕ)^16*10000000000000000^67 ≤ 12999881816832461^67*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 12999881816832461 10000000000000000 16 67 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12999881816832461/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have major_s0_1 : P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1))+(360031261787197/2000000000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2))+(299931376974119/2500000000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 2 0)) := by
    have hh := chart_majorant (a := (67/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (360031261787197/2000000000000000 : ℝ)) (beta := (299931376974119/2500000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow1,s0_corner1a]) (by linarith only [s0_pow1,s0_corner1b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, false], ![false, false, false]] hX 1 (by
        change ((-1 : ℝ)*pair X 1 2) ≤ (1 : ℝ)*((-1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order1.2.2])
    change lpNorm p (pair X 1) ≤ ((-1 : ℝ)*pair X 1 1)+(360031261787197/2000000000000000 : ℝ)*((-1 : ℝ)*pair X 1 2)+(299931376974119/2500000000000000 : ℝ)*((-1 : ℝ)*pair X 1 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow2 : (1 : ℝ) ^ (67/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^67 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^67*1^16 ≤ 1^16*1^67 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 67 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have s0_corner2a : (2 : ℝ) ≤ (2360031261787197/2000000000000000 : ℝ) ^ (67/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (2360031261787197/2000000000000000 : ℝ)^67 := by
      have hnat : (2 : ℕ)^16*2000000000000000^67 ≤ 2360031261787197^67*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 2360031261787197 2000000000000000 16 67 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2360031261787197/2000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have s0_corner2b : (3 : ℝ) ≤ (12999881816832461/10000000000000000 : ℝ) ^ (67/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (12999881816832461/10000000000000000 : ℝ)^67 := by
      have hnat : (3 : ℕ)^16*10000000000000000^67 ≤ 12999881816832461^67*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 12999881816832461 10000000000000000 16 67 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12999881816832461/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have major_s0_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(360031261787197/2000000000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 1 0))+(299931376974119/2500000000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (67/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (360031261787197/2000000000000000 : ℝ)) (beta := (299931376974119/2500000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow2,s0_corner2a]) (by linarith only [s0_pow2,s0_corner2b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, false], ![false, false, false]] hX 2 (by
        change ((-1 : ℝ)*pair X 2 0) ≤ (1 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order2.2.2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(360031261787197/2000000000000000 : ℝ)*((-1 : ℝ)*pair X 2 0)+(299931376974119/2500000000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s0_0 : ((-811282499/2500000000 : ℝ)*X 0 0+(-1884514451/5000000000 : ℝ)*X 0 1+(-5828905639/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c306064_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_2 : ((6604084117/10000000000 : ℝ)*X 2 0+(-3629504417/10000000000 : ℝ)*X 2 1+(2405950561/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c306064_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_3 : ((1 : ℝ)*X 1 0+(1 : ℝ)*X 2 0+(-1 : ℝ)*P 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c306064_s0_3 p hpa hpb (pair X 0)
    change _ ≤ P 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_7 : ((-159020563/500000000 : ℝ)*X 0 0+(-76641177/200000000 : ℝ)*X 0 1+(-582750223/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c306064_s0_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_8 : ((213564629/625000000 : ℝ)*X 1 0+(6051756333/10000000000 : ℝ)*X 1 1+(-1669545879/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c306064_s0_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_9 : ((6499578891/10000000000 : ℝ)*X 2 0+(-12837527/39062500 : ℝ)*X 2 1+(2916526689/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c306064_s0_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_14 : ((-2830570523/10000000000 : ℝ)*X 0 0+(-3005358413/10000000000 : ℝ)*X 0 1+(-84857653/125000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c306064_s0_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_15 : ((556825253/1250000000 : ℝ)*X 1 0+(5345598133/10000000000 : ℝ)*X 1 1+(-3078215491/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c306064_s0_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_16 : ((299741943/400000000 : ℝ)*X 2 0+(-306251313/1000000000 : ℝ)*X 2 1+(1763521149/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c306064_s0_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_20 : ((-1841451669/5000000000 : ℝ)*X 0 0+(-2251782941/5000000000 : ℝ)*X 0 1+(-1191224233/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c306064_s0_20 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_21 : ((293114669/1000000000 : ℝ)*X 1 0+(1217267253/2000000000 : ℝ)*X 1 1+(-941840323/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c306064_s0_21 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_22 : ((757057723/1000000000 : ℝ)*X 2 0+(-2921623503/10000000000 : ℝ)*X 2 1+(361689227/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c306064_s0_22 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s0_0 : (0 : ℝ) ≤ ((1803/25000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(1803/25000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (10833293118983862243489/1250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (458704595401/250000000000 : ℝ)*(base1) + (42103550871/250000000000 : ℝ)*(base7) + (9730749/1000000000000 : ℝ)*(base22) + (1136527552781/1000000000000 : ℝ)*(base39) + (110487657871/125000000000 : ℝ)*(base60) + (2569361946077/1000000000000 : ℝ)*(major_s0_0) + (2569361946077/1000000000000 : ℝ)*(major_s0_1) + (2569361946077/1000000000000 : ℝ)*(major_s0_2) + (182827/500000000000 : ℝ)*(sp_s0_2) + (1040544350993/200000000000 : ℝ)*(sp_s0_7) + (210482794973/62500000000 : ℝ)*(sp_s0_8) + (673578653243/200000000000 : ℝ)*(sp_s0_9) + (3572861/20000000000 : ℝ)*(sp_s0_21) + (41660104453/25000000000 : ℝ)*(f.failure) + (1683951681309/500000000000 : ℝ)*(f.sum) + (39559988455074794503/10000000000000000000000000000 : ℝ)*base63 + (12096013221059918837/2500000000000000000000000000 : ℝ)*base65 + (10237499885427023831/2000000000000000000000000000 : ℝ)*base67 + (790802733376169/2000000000000000000000000000 : ℝ)*base68 + (3446606410556193/10000000000000000000000000000 : ℝ)*base71 + (282936788581163/2500000000000000000000000000 : ℝ)*base73 + (265502226668837/2500000000000000000000000000 : ℝ)*base75 + (118363322576169/2000000000000000000000000000 : ℝ)*base77 + (1679217166443807/10000000000000000000000000000 : ℝ)*base79 + (10743/1000000000000 : ℝ)*base81 + (1121/1250000000000000 : ℝ)*base86 + (1121/1250000000000000 : ℝ)*base88 + (1121/1250000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s0_1 : (0 : ℝ) ≤ ((-75361/100000 : ℝ)*X 0 1+(1 : ℝ)*X 0 2+(-75361/100000 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (80461089843005652150423/5000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (3716088136263/1000000000000 : ℝ)*(base1) + (45441490421/40000000000 : ℝ)*(base7) + (84034845957/62500000000 : ℝ)*(base39) + (23617400897/20000000000 : ℝ)*(base60) + (4982163838073/500000000000 : ℝ)*(major_s0_0) + (795615448653/200000000000 : ℝ)*(major_s0_1) + (795615448653/200000000000 : ℝ)*(major_s0_2) + (38064147/1000000000000 : ℝ)*(sp_s0_0) + (11490933/125000000000 : ℝ)*(sp_s0_2) + (2993125216441/500000000000 : ℝ)*(sp_s0_3) + (1677565587609/200000000000 : ℝ)*(sp_s0_14) + (4671777865929/1000000000000 : ℝ)*(sp_s0_15) + (583864856261/125000000000 : ℝ)*(sp_s0_16) + (95886047/125000000000 : ℝ)*(sp_s0_22) + (2580050875737/1000000000000 : ℝ)*(f.failure) + (4671777865929/1000000000000 : ℝ)*(f.sum) + (1114594340274967/2000000000000000000000000000 : ℝ)*base63 + (367936795461707/500000000000000000000000000 : ℝ)*base64 + (32807936975641/400000000000000000000000000 : ℝ)*base66 + (155397378135641/400000000000000000000000000 : ℝ)*base68 + (863767671972033/1000000000000000000000000000 : ℝ)*base70 + (657352504792313/1250000000000000000000000000 : ℝ)*base72 + (137401372811707/500000000000000000000000000 : ℝ)*base74 + (650276601848619/1000000000000000000000000000 : ℝ)*base76 + (2299865510729529/10000000000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base84 + (7459/50000000000000000 : ℝ)*base86 + (57459/50000000000000000 : ℝ)*base88 + (57459/50000000000000000 : ℝ)*base90 + (1/1000000000000 : ℝ)*base93 + hcertificate_margin
  have ratio_s0_2 : (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(-27523/50000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(-27523/50000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (26158140940379927105169/1250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (3054159286579/1000000000000 : ℝ)*(base1) + (976541854129/1000000000000 : ℝ)*(base7) + (4794108827/50000000000 : ℝ)*(base40) + (107049840439/200000000000 : ℝ)*(base60) + (2804721456717/250000000000 : ℝ)*(major_s0_0) + (1601697607199/500000000000 : ℝ)*(major_s0_1) + (1601697607199/500000000000 : ℝ)*(major_s0_2) + (8015490612469/1000000000000 : ℝ)*(sp_s0_3) + (20965491/1000000000000 : ℝ)*(sp_s0_7) + (10356131/100000000000 : ℝ)*(sp_s0_8) + (164503843/500000000000 : ℝ)*(sp_s0_16) + (6777867923199/1000000000000 : ℝ)*(sp_s0_20) + (3723626040801/1000000000000 : ℝ)*(sp_s0_21) + (465425074303/125000000000 : ℝ)*(sp_s0_22) + (2077617432451/1000000000000 : ℝ)*(f.failure) + (3723729602111/1000000000000 : ℝ)*(f.sum) + (2844698290513261/5000000000000000000000000000 : ℝ)*base63 + (29667017582681/1250000000000000000000000000 : ℝ)*base64 + (378027806568797/1000000000000000000000000000 : ℝ)*base67 + (1045944513768797/1000000000000000000000000000 : ℝ)*base69 + (1747117124654117/2500000000000000000000000000 : ℝ)*base70 + (334760654707323/625000000000000000000000000 : ℝ)*base73 + (1478763627667319/1250000000000000000000000000 : ℝ)*base75 + (25499922852249/500000000000000000000000000 : ℝ)*base77 + (1327758908502569/5000000000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base84 + (5057/50000000000000000 : ℝ)*base86 + (44943/50000000000000000 : ℝ)*base89 + (44943/50000000000000000 : ℝ)*base91 + (1/1000000000000 : ℝ)*base92 + hcertificate_margin
  have s1_pow0 : (1803/25000 : ℝ) ^ (67/16 : ℝ) ≤ (826186936410939/50000000000000000000 : ℝ) := by
    have hpowers : (1803/25000 : ℝ)^67 ≤ (826186936410939/50000000000000000000 : ℝ)^16 := by
      have hnat : (1803 : ℕ)^67*50000000000000000000^16 ≤ 826186936410939^16*25000^67 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1803 25000 826186936410939 50000000000000000000 67 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1803/25000 : ℝ)) (X := (826186936410939/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have s1_corner0a : (50000826186936410939/50000000000000000000 : ℝ) ≤ (500001972971321/500000000000000 : ℝ) ^ (67/16 : ℝ) := by
    have hpowers : (50000826186936410939/50000000000000000000 : ℝ)^16 ≤ (500001972971321/500000000000000 : ℝ)^67 := by
      have hnat : (50000826186936410939 : ℕ)^16*500000000000000^67 ≤ 500001972971321^67*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000826186936410939 50000000000000000000 500001972971321 500000000000000 16 67 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (500001972971321/500000000000000 : ℝ)) (X := (50000826186936410939/50000000000000000000 : ℝ)) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have s1_corner0b : (25000826186936410939/25000000000000000000 : ℝ) ≤ (500003945917827/500000000000000 : ℝ) ^ (67/16 : ℝ) := by
    have hpowers : (25000826186936410939/25000000000000000000 : ℝ)^16 ≤ (500003945917827/500000000000000 : ℝ)^67 := by
      have hnat : (25000826186936410939 : ℕ)^16*500000000000000^67 ≤ 500003945917827^67*25000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000826186936410939 25000000000000000000 500003945917827 500000000000000 16 67 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (500003945917827/500000000000000 : ℝ)) (X := (25000826186936410939/25000000000000000000 : ℝ)) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(657657107/12020000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(986473253/18030000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (67/16 : ℝ)) (rho := (1803/25000 : ℝ)) (alpha := (657657107/12020000000000 : ℝ)) (beta := (986473253/18030000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, false], ![false, false, false]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (1803/25000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(657657107/12020000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(986473253/18030000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (75361/100000 : ℝ) ^ (67/16 : ℝ) ≤ (6117607417432977611/20000000000000000000 : ℝ) := by
    have hpowers : (75361/100000 : ℝ)^67 ≤ (6117607417432977611/20000000000000000000 : ℝ)^16 := by
      have hnat : (75361 : ℕ)^67*20000000000000000000^16 ≤ 6117607417432977611^16*100000^67 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        75361 100000 6117607417432977611 20000000000000000000 67 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (75361/100000 : ℝ)) (X := (6117607417432977611/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have s1_corner1a : (26117607417432977611/20000000000000000000 : ℝ) ≤ (10658066420755037/10000000000000000 : ℝ) ^ (67/16 : ℝ) := by
    have hpowers : (26117607417432977611/20000000000000000000 : ℝ)^16 ≤ (10658066420755037/10000000000000000 : ℝ)^67 := by
      have hnat : (26117607417432977611 : ℕ)^16*10000000000000000^67 ≤ 10658066420755037^67*20000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        26117607417432977611 20000000000000000000 10658066420755037 10000000000000000 16 67 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10658066420755037/10000000000000000 : ℝ)) (X := (26117607417432977611/20000000000000000000 : ℝ)) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have s1_corner1b : (16117607417432977611/10000000000000000000 : ℝ) ≤ (11207393342868523/10000000000000000 : ℝ) ^ (67/16 : ℝ) := by
    have hpowers : (16117607417432977611/10000000000000000000 : ℝ)^16 ≤ (11207393342868523/10000000000000000 : ℝ)^67 := by
      have hnat : (16117607417432977611 : ℕ)^16*10000000000000000^67 ≤ 11207393342868523^67*10000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        16117607417432977611 10000000000000000000 11207393342868523 10000000000000000 16 67 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11207393342868523/10000000000000000 : ℝ)) (X := (16117607417432977611/10000000000000000000 : ℝ)) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1))+(658066420755037/7536100000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2))+(24969405550613/342550000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 2 0)) := by
    have hh := chart_majorant (a := (67/16 : ℝ)) (rho := (75361/100000 : ℝ)) (alpha := (658066420755037/7536100000000000 : ℝ)) (beta := (24969405550613/342550000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, false], ![false, false, false]] hX 1 (by
        change ((-1 : ℝ)*pair X 1 2) ≤ (75361/100000 : ℝ)*((-1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((-1 : ℝ)*pair X 1 1)+(658066420755037/7536100000000000 : ℝ)*((-1 : ℝ)*pair X 1 2)+(24969405550613/342550000000000 : ℝ)*((-1 : ℝ)*pair X 1 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (27523/50000 : ℝ) ^ (67/16 : ℝ) ≤ (2052244748123304949/25000000000000000000 : ℝ) := by
    have hpowers : (27523/50000 : ℝ)^67 ≤ (2052244748123304949/25000000000000000000 : ℝ)^16 := by
      have hnat : (27523 : ℕ)^67*25000000000000000000^16 ≤ 2052244748123304949^16*50000^67 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        27523 50000 2052244748123304949 25000000000000000000 67 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (27523/50000 : ℝ)) (X := (2052244748123304949/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have s1_corner2a : (27052244748123304949/25000000000000000000 : ℝ) ≤ (10190189970727289/10000000000000000 : ℝ) ^ (67/16 : ℝ) := by
    have hpowers : (27052244748123304949/25000000000000000000 : ℝ)^16 ≤ (10190189970727289/10000000000000000 : ℝ)^67 := by
      have hnat : (27052244748123304949 : ℕ)^16*10000000000000000^67 ≤ 10190189970727289^67*25000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        27052244748123304949 25000000000000000000 10190189970727289 10000000000000000 16 67 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10190189970727289/10000000000000000 : ℝ)) (X := (27052244748123304949/25000000000000000000 : ℝ)) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have s1_corner2b : (14552244748123304949/12500000000000000000 : ℝ) ≤ (10369694567837219/10000000000000000 : ℝ) ^ (67/16 : ℝ) := by
    have hpowers : (14552244748123304949/12500000000000000000 : ℝ)^16 ≤ (10369694567837219/10000000000000000 : ℝ)^67 := by
      have hnat : (14552244748123304949 : ℕ)^16*10000000000000000^67 ≤ 10369694567837219^67*12500000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14552244748123304949 12500000000000000000 10369694567837219 10000000000000000 16 67 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10369694567837219/10000000000000000 : ℝ)) (X := (14552244748123304949/12500000000000000000 : ℝ)) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(190189970727289/5504600000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 1 0))+(17950459710993/550460000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (67/16 : ℝ)) (rho := (27523/50000 : ℝ)) (alpha := (190189970727289/5504600000000000 : ℝ)) (beta := (17950459710993/550460000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, false], ![false, false, false]] hX 2 (by
        change ((-1 : ℝ)*pair X 2 0) ≤ (27523/50000 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(190189970727289/5504600000000000 : ℝ)*((-1 : ℝ)*pair X 2 0)+(17950459710993/550460000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-3705115207/10000000000 : ℝ)*X 0 0+(-3705115307/10000000000 : ℝ)*X 0 1+(-1372456023/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c306064_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_1 : ((4752688461/10000000000 : ℝ)*X 1 0+(4752688589/10000000000 : ℝ)*X 1 1+(-137034029/400000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c306064_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((4752688461/10000000000 : ℝ)*X 2 0+(-4752688589/10000000000 : ℝ)*X 2 1+(137034029/400000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c306064_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_6 : ((3705115207/10000000000 : ℝ)*X 0 0+(-3705115307/10000000000 : ℝ)*X 0 1+(-1372456023/2500000000 : ℝ)*X 0 2+(3705115207/10000000000 : ℝ)*X 1 0+(-3705115307/10000000000 : ℝ)*X 1 1+(-1372456023/2500000000 : ℝ)*X 1 2+(3705115207/10000000000 : ℝ)*X 2 0+(-3705115307/10000000000 : ℝ)*X 2 1+(-1372456023/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c306064_s1_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have hsep : (-156279/25000 : ℝ) < ((-77093/50000 : ℝ)*P 0+(-77093/50000 : ℝ)*P 1+(-77093/50000 : ℝ)*P 2+(1 : ℝ)*T) := by
    have hcertificate_margin : (-156279/25000 : ℝ) < (-2259037273110997098378238281345067/366638424295000000000000000000000 : ℝ) := by norm_num
    linear_combination (860179571597/1000000000000 : ℝ)*(base1) + (3941/100000000000 : ℝ)*(base12) + (829/31250000000 : ℝ)*(base17) + (27411/250000000000 : ℝ)*(base21) + (637627818621/500000000000 : ℝ)*(base39) + (513849909683/1000000000000 : ℝ)*(base40) + (401543799711/1000000000000 : ℝ)*(base49) + (460661303501/1000000000000 : ℝ)*(base60) + (77093/50000 : ℝ)*(major_s1_0) + (77093/50000 : ℝ)*(major_s1_1) + (77093/50000 : ℝ)*(major_s1_2) + (2914007975883/1000000000000 : ℝ)*(sp_s1_0) + (128364276073/62500000000 : ℝ)*(sp_s1_1) + (513457083513/250000000000 : ℝ)*(sp_s1_2) + (139820428403/1000000000000 : ℝ)*(sp_s1_6) + (128364277731/62500000000 : ℝ)*(f.sum) + (1827075367251721/2772942250000000000000000000 : ℝ)*base63 + (20238820655777/137615000000000000000000000 : ℝ)*base64 + (3314284906329/94201250000000000000000000 : ℝ)*base67 + (83296711876513/275230000000000000000000000 : ℝ)*base69 + (151985002227258613/165413230000000000000000000000 : ℝ)*base70 + (2461583643107/4507500000000000000000000 : ℝ)*base73 + (19992941209557/68510000000000000000000000 : ℝ)*base75 + (2505378193251/6010000000000000000000000 : ℝ)*base76 + (18820599543624469/42461213437500000000000000000 : ℝ)*base79 + hcertificate_margin
  linarith only [hsep,f.failure]

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem collision_support_c306065_s0_0 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-67463281/156250000 : ℝ)*x 0 + (-4934747323/10000000000 : ℝ)*x 1 + (3694510867/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (67463281/156250000 : ℝ)^135 ≤ (33260306486671/100000000000000 : ℝ)^103 := by
    have hnat : (67463281 : ℕ)^135*100000000000000^103 ≤ 33260306486671^103*156250000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      67463281 156250000 33260306486671 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4934747323/10000000000 : ℝ)^135 ≤ (3962493698939/10000000000000 : ℝ)^103 := by
    have hnat : (4934747323 : ℕ)^135*10000000000000^103 ≤ 3962493698939^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4934747323 10000000000 3962493698939 10000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3694510867/10000000000 : ℝ)^135 ≤ (3389344564833/12500000000000 : ℝ)^103 := by
    have hnat : (3694510867 : ℕ)^135*12500000000000^103 ≤ 3389344564833^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3694510867 10000000000 3389344564833 12500000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-67463281/156250000 : ℝ), (-4934747323/10000000000 : ℝ), (3694510867/10000000000 : ℝ)] ![(33260306486671/100000000000000 : ℝ), (3962493698939/10000000000000 : ℝ), (3389344564833/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-67463281/156250000 : ℝ)|^135 ≤ (33260306486671/100000000000000 : ℝ)^103
        have hw : |(-67463281/156250000 : ℝ)|=(67463281/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-4934747323/10000000000 : ℝ)|^135 ≤ (3962493698939/10000000000000 : ℝ)^103
        have hw : |(-4934747323/10000000000 : ℝ)|=(4934747323/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3694510867/10000000000 : ℝ)|^135 ≤ (3389344564833/12500000000000 : ℝ)^103
        have hw : |(3694510867/10000000000 : ℝ)|=(3694510867/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306065_s0_1 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (3683890663/10000000000 : ℝ)*x 0 + (423832511/1000000000 : ℝ)*x 1 + (251005163/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3683890663/10000000000 : ℝ)^135 ≤ (13506321403453/50000000000000 : ℝ)^103 := by
    have hnat : (3683890663 : ℕ)^135*50000000000000^103 ≤ 13506321403453^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3683890663 10000000000 13506321403453 50000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (423832511/1000000000 : ℝ)^135 ≤ (32461690061113/100000000000000 : ℝ)^103 := by
    have hnat : (423832511 : ℕ)^135*100000000000000^103 ≤ 32461690061113^103*1000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      423832511 1000000000 32461690061113 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (251005163/500000000 : ℝ)^135 ≤ (20262833561133/50000000000000 : ℝ)^103 := by
    have hnat : (251005163 : ℕ)^135*50000000000000^103 ≤ 20262833561133^103*500000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      251005163 500000000 20262833561133 50000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3683890663/10000000000 : ℝ), (423832511/1000000000 : ℝ), (251005163/500000000 : ℝ)] ![(13506321403453/50000000000000 : ℝ), (32461690061113/100000000000000 : ℝ), (20262833561133/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3683890663/10000000000 : ℝ)|^135 ≤ (13506321403453/50000000000000 : ℝ)^103
        have hw : |(3683890663/10000000000 : ℝ)|=(3683890663/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(423832511/1000000000 : ℝ)|^135 ≤ (32461690061113/100000000000000 : ℝ)^103
        have hw : |(423832511/1000000000 : ℝ)|=(423832511/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(251005163/500000000 : ℝ)|^135 ≤ (20262833561133/50000000000000 : ℝ)^103
        have hw : |(251005163/500000000 : ℝ)|=(251005163/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306065_s0_2 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (252102743/500000000 : ℝ)*x 0 + (-1789798949/5000000000 : ℝ)*x 1 + (-4314366969/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (252102743/500000000 : ℝ)^135 ≤ (326064702771/800000000000 : ℝ)^103 := by
    have hnat : (252102743 : ℕ)^135*800000000000^103 ≤ 326064702771^103*500000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      252102743 500000000 326064702771 800000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1789798949/5000000000 : ℝ)^135 ≤ (6503687260203/25000000000000 : ℝ)^103 := by
    have hnat : (1789798949 : ℕ)^135*25000000000000^103 ≤ 6503687260203^103*5000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1789798949 5000000000 6503687260203 25000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4314366969/10000000000 : ℝ)^135 ≤ (16613581548771/50000000000000 : ℝ)^103 := by
    have hnat : (4314366969 : ℕ)^135*50000000000000^103 ≤ 16613581548771^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4314366969 10000000000 16613581548771 50000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(252102743/500000000 : ℝ), (-1789798949/5000000000 : ℝ), (-4314366969/10000000000 : ℝ)] ![(326064702771/800000000000 : ℝ), (6503687260203/25000000000000 : ℝ), (16613581548771/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(252102743/500000000 : ℝ)|^135 ≤ (326064702771/800000000000 : ℝ)^103
        have hw : |(252102743/500000000 : ℝ)|=(252102743/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1789798949/5000000000 : ℝ)|^135 ≤ (6503687260203/25000000000000 : ℝ)^103
        have hw : |(-1789798949/5000000000 : ℝ)|=(1789798949/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-4314366969/10000000000 : ℝ)|^135 ≤ (16613581548771/50000000000000 : ℝ)^103
        have hw : |(-4314366969/10000000000 : ℝ)|=(4314366969/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c306065 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (77093/50000 : ℝ) (92997/50000 : ℝ) (38461/50000 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, false], ![false, false, true]]) : False := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (38461/50000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (38461/50000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (38461/50000 : ℝ)*P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (38461/50000 : ℝ)*P 1 ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 0+X 2 0)) ∧ ((-1 : ℝ)*(X 0 0+X 2 0)) ≤ ((-1 : ℝ)*(X 0 2+X 2 2)) ∧ ((-1 : ℝ)*(X 0 2+X 2 2)) ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 0) ∧ ((-1 : ℝ)*pair X 1 0) ≤ ((-1 : ℝ)*pair X 1 2) ∧ ((-1 : ℝ)*pair X 1 2) ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (38461/50000 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (38461/50000 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((-1 : ℝ)*(X 0 1+X 1 1)) ∧ ((-1 : ℝ)*(X 0 1+X 1 1)) ≤ ((-1 : ℝ)*(X 0 0+X 1 0)) ∧ ((-1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((-1 : ℝ)*pair X 2 1) ∧ ((-1 : ℝ)*pair X 2 1) ≤ ((-1 : ℝ)*pair X 2 0) ∧ ((-1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base1 : ((1 : ℝ)*N 0+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 0]
  have base3 : ((1 : ℝ)*N 1+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 1]
  have base33 : ((-1 : ℝ)*N 1+(-1 : ℝ)*N 2+(1 : ℝ)*P 0) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 0,f.sum]
  have base34 : ((-1 : ℝ)*N 0+(1 : ℝ)*P 0+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ptotal 0]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base49 : ((1 : ℝ)*X 0 0+(1 : ℝ)*X 2 0) ≤ (0 : ℝ) := by
    linarith only [order1.1]
  have base50 : ((-1 : ℝ)*X 0 0+(1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 0+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.2.1]
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
  have s0_pow0 : (1 : ℝ) ^ (67/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^67 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^67*1^16 ≤ 1^16*1^67 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 67 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have s0_corner0a : (2 : ℝ) ≤ (2360031261787197/2000000000000000 : ℝ) ^ (67/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (2360031261787197/2000000000000000 : ℝ)^67 := by
      have hnat : (2 : ℕ)^16*2000000000000000^67 ≤ 2360031261787197^67*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 2360031261787197 2000000000000000 16 67 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2360031261787197/2000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have s0_corner0b : (3 : ℝ) ≤ (12999881816832461/10000000000000000 : ℝ) ^ (67/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (12999881816832461/10000000000000000 : ℝ)^67 := by
      have hnat : (3 : ℕ)^16*10000000000000000^67 ≤ 12999881816832461^67*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 12999881816832461 10000000000000000 16 67 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12999881816832461/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have major_s0_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(360031261787197/2000000000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(299931376974119/2500000000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (67/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (360031261787197/2000000000000000 : ℝ)) (beta := (299931376974119/2500000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow0,s0_corner0a]) (by linarith only [s0_pow0,s0_corner0b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, false], ![false, false, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (1 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order0.2.2])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(360031261787197/2000000000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(299931376974119/2500000000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow1 : (1 : ℝ) ^ (67/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^67 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^67*1^16 ≤ 1^16*1^67 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 67 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have s0_corner1a : (2 : ℝ) ≤ (2360031261787197/2000000000000000 : ℝ) ^ (67/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (2360031261787197/2000000000000000 : ℝ)^67 := by
      have hnat : (2 : ℕ)^16*2000000000000000^67 ≤ 2360031261787197^67*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 2360031261787197 2000000000000000 16 67 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2360031261787197/2000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have s0_corner1b : (3 : ℝ) ≤ (12999881816832461/10000000000000000 : ℝ) ^ (67/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (12999881816832461/10000000000000000 : ℝ)^67 := by
      have hnat : (3 : ℕ)^16*10000000000000000^67 ≤ 12999881816832461^67*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 12999881816832461 10000000000000000 16 67 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12999881816832461/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have major_s0_1 : P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1))+(360031261787197/2000000000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2))+(299931376974119/2500000000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 2 0)) := by
    have hh := chart_majorant (a := (67/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (360031261787197/2000000000000000 : ℝ)) (beta := (299931376974119/2500000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow1,s0_corner1a]) (by linarith only [s0_pow1,s0_corner1b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, false], ![false, false, true]] hX 1 (by
        change ((-1 : ℝ)*pair X 1 2) ≤ (1 : ℝ)*((-1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order1.2.2])
    change lpNorm p (pair X 1) ≤ ((-1 : ℝ)*pair X 1 1)+(360031261787197/2000000000000000 : ℝ)*((-1 : ℝ)*pair X 1 2)+(299931376974119/2500000000000000 : ℝ)*((-1 : ℝ)*pair X 1 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow2 : (1 : ℝ) ^ (67/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^67 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^67*1^16 ≤ 1^16*1^67 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 67 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have s0_corner2a : (2 : ℝ) ≤ (2360031261787197/2000000000000000 : ℝ) ^ (67/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (2360031261787197/2000000000000000 : ℝ)^67 := by
      have hnat : (2 : ℕ)^16*2000000000000000^67 ≤ 2360031261787197^67*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 2360031261787197 2000000000000000 16 67 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2360031261787197/2000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have s0_corner2b : (3 : ℝ) ≤ (12999881816832461/10000000000000000 : ℝ) ^ (67/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (12999881816832461/10000000000000000 : ℝ)^67 := by
      have hnat : (3 : ℕ)^16*10000000000000000^67 ≤ 12999881816832461^67*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 12999881816832461 10000000000000000 16 67 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12999881816832461/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have major_s0_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(360031261787197/2000000000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 1 0))+(299931376974119/2500000000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (67/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (360031261787197/2000000000000000 : ℝ)) (beta := (299931376974119/2500000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow2,s0_corner2a]) (by linarith only [s0_pow2,s0_corner2b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, false], ![false, false, true]] hX 2 (by
        change ((-1 : ℝ)*pair X 2 0) ≤ (1 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order2.2.2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(360031261787197/2000000000000000 : ℝ)*((-1 : ℝ)*pair X 2 0)+(299931376974119/2500000000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s0_0 : ((-67463281/156250000 : ℝ)*X 0 0+(-4934747323/10000000000 : ℝ)*X 0 1+(3694510867/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c306065_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_1 : ((3683890663/10000000000 : ℝ)*X 1 0+(423832511/1000000000 : ℝ)*X 1 1+(251005163/500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c306065_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_2 : ((252102743/500000000 : ℝ)*X 2 0+(-1789798949/5000000000 : ℝ)*X 2 1+(-4314366969/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c306065_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have hsep : (-156279/25000 : ℝ) < ((-77093/50000 : ℝ)*P 0+(-77093/50000 : ℝ)*P 1+(-77093/50000 : ℝ)*P 2+(1 : ℝ)*T) := by
    have hcertificate_margin : (-156279/25000 : ℝ) < (-384251691633173569754896689/62500000000000000000000000 : ℝ) := by norm_num
    linear_combination (133335668341/200000000000 : ℝ)*(base1) + (83330385381/250000000000 : ℝ)*(base3) + (140493/1000000000000 : ℝ)*(base33) + (116771/1000000000000 : ℝ)*(base34) + (106143807439/200000000000 : ℝ)*(base40) + (584453622599/1000000000000 : ℝ)*(base49) + (260864344457/1000000000000 : ℝ)*(base50) + (108593/500000000000 : ℝ)*(base59) + (193276782779/500000000000 : ℝ)*(base60) + (96366233921/62500000000 : ℝ)*(major_s0_0) + (77093/50000 : ℝ)*(major_s0_1) + (77093/50000 : ℝ)*(major_s0_2) + (1358010290153/500000000000 : ℝ)*(sp_s0_0) + (595665939101/250000000000 : ℝ)*(sp_s0_1) + (12808388843/6250000000 : ℝ)*(sp_s0_2) + (2049342355373/1000000000000 : ℝ)*(f.sum) + (143324411/2500000000000000000000 : ℝ)*base63 + (3660232261/5000000000000000000000 : ℝ)*base64 + (1100508701/5000000000000000000000 : ℝ)*base66 + (77492997/625000000000000000000 : ℝ)*base68 + (107897747590563/125000000000000000000000000 : ℝ)*base70 + (23611638140599/156250000000000000000000000 : ℝ)*base73 + (51610027/125000000000000000000 : ℝ)*base74 + (28281347090563/125000000000000000000000000 : ℝ)*base76 + (21689242171901/156250000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base80 + hcertificate_margin
  linarith only [hsep,f.failure]

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
namespace HlawkaSchatten.DiagonalCutoff4
theorem coarse_distinct_p006_b027 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ))
    (c : Fin 88) (hlo : 62 ≤ c.val) (hhi : c.val < 66)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (77093/50000 : ℝ) (92997/50000 : ℝ) (38461/50000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  have hc : c=62 ∨ c=63 ∨ c=64 ∨ c=65 := by omega
  rcases hc with rfl|rfl|rfl|rfl
  · exact collision_c306062 p hpa (by linarith only [hpb]) X hX
  · exact (hn63 rfl).elim
  · exact collision_c306064 p hpa (by linarith only [hpb]) X hX
  · exact collision_c306065 p hpa (by linarith only [hpb]) X hX

end HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ))
    (c : Fin 88) (hlo : 62 ≤ c.val) (hhi : c.val < 66)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (77093/50000 : ℝ) (92997/50000 : ℝ) (38461/50000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  exact HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p006_b027 p hpa hpb c hlo hhi hn63 hn87 X hX

#print axioms solution
