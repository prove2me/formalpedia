-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.wide_coarse_distinct_p018_b010
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T01:26:00.363633+00:00
-- url     : https://prove2.me/submissions/13345792-bbd9-41da-a4e1-e58c90152030

import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c318023_s0
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c318023_s1
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c318023_s2
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
theorem HlawkaSchatten.DiagonalCutoff4.collision_c318023 (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (7299/4000 : ℝ) (34269/20000 : ℝ) (39911/50000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![true, true, true]]) : False := by
  have h0 := collision_c318023_s0 p hpa hpb X hX
  have h1 := collision_c318023_s1 p hpa hpb X hX h0
  exact collision_c318023_s2 p hpa hpb X hX h1

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
theorem collision_support_c318022_s0_1 (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ)) (x : Fin 3 → ℝ) :
    (3488326599/5000000000 : ℝ)*x 0 + (-1103345913/10000000000 : ℝ)*x 1 + (-475562791/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3488326599/5000000000 : ℝ)^5 ≤ (31880778896433/50000000000000 : ℝ)^4 := by
    have hnat : (3488326599 : ℕ)^5*50000000000000^4 ≤ 31880778896433^4*5000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3488326599 5000000000 31880778896433 50000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1103345913/10000000000 : ℝ)^5 ≤ (3179505771333/50000000000000 : ℝ)^4 := by
    have hnat : (1103345913 : ℕ)^5*50000000000000^4 ≤ 3179505771333^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1103345913 10000000000 3179505771333 50000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (475562791/1250000000 : ℝ)^5 ≤ (29879430646729/100000000000000 : ℝ)^4 := by
    have hnat : (475562791 : ℕ)^5*100000000000000^4 ≤ 29879430646729^4*1250000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      475562791 1250000000 29879430646729 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5 : ℝ)) 5 4 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3488326599/5000000000 : ℝ), (-1103345913/10000000000 : ℝ), (-475562791/1250000000 : ℝ)] ![(31880778896433/50000000000000 : ℝ), (3179505771333/50000000000000 : ℝ), (29879430646729/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3488326599/5000000000 : ℝ)|^5 ≤ (31880778896433/50000000000000 : ℝ)^4
        have hw : |(3488326599/5000000000 : ℝ)|=(3488326599/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1103345913/10000000000 : ℝ)|^5 ≤ (3179505771333/50000000000000 : ℝ)^4
        have hw : |(-1103345913/10000000000 : ℝ)|=(1103345913/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-475562791/1250000000 : ℝ)|^5 ≤ (29879430646729/100000000000000 : ℝ)^4
        have hw : |(-475562791/1250000000 : ℝ)|=(475562791/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c318022_s0_2 (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ)) (x : Fin 3 → ℝ) :
    (2542176653/10000000000 : ℝ)*x 0 + (5476644871/10000000000 : ℝ)*x 1 + (4301476111/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2542176653/10000000000 : ℝ)^5 ≤ (4512811215473/25000000000000 : ℝ)^4 := by
    have hnat : (2542176653 : ℕ)^5*25000000000000^4 ≤ 4512811215473^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2542176653 10000000000 4512811215473 25000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5476644871/10000000000 : ℝ)^5 ≤ (47113267502019/100000000000000 : ℝ)^4 := by
    have hnat : (5476644871 : ℕ)^5*100000000000000^4 ≤ 47113267502019^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5476644871 10000000000 47113267502019 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4301476111/10000000000 : ℝ)^5 ≤ (34835487625073/100000000000000 : ℝ)^4 := by
    have hnat : (4301476111 : ℕ)^5*100000000000000^4 ≤ 34835487625073^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4301476111 10000000000 34835487625073 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5 : ℝ)) 5 4 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2542176653/10000000000 : ℝ), (5476644871/10000000000 : ℝ), (4301476111/10000000000 : ℝ)] ![(4512811215473/25000000000000 : ℝ), (47113267502019/100000000000000 : ℝ), (34835487625073/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2542176653/10000000000 : ℝ)|^5 ≤ (4512811215473/25000000000000 : ℝ)^4
        have hw : |(2542176653/10000000000 : ℝ)|=(2542176653/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5476644871/10000000000 : ℝ)|^5 ≤ (47113267502019/100000000000000 : ℝ)^4
        have hw : |(5476644871/10000000000 : ℝ)|=(5476644871/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4301476111/10000000000 : ℝ)|^5 ≤ (34835487625073/100000000000000 : ℝ)^4
        have hw : |(4301476111/10000000000 : ℝ)|=(4301476111/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c318022_s0_4 (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ)) (x : Fin 3 → ℝ) :
    (-3/2000000000 : ℝ)*x 0 + (9999999999/10000000000 : ℝ)*x 1 + (-3/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3/2000000000 : ℝ)^5 ≤ (467/50000000000000 : ℝ)^4 := by
    have hnat : (3 : ℕ)^5*50000000000000^4 ≤ 467^4*2000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3 2000000000 467 50000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (9999999999/10000000000 : ℝ)^5 ≤ (99999999987501/100000000000000 : ℝ)^4 := by
    have hnat : (9999999999 : ℕ)^5*100000000000000^4 ≤ 99999999987501^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      9999999999 10000000000 99999999987501 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3/2000000000 : ℝ)^5 ≤ (467/50000000000000 : ℝ)^4 := by
    have hnat : (3 : ℕ)^5*50000000000000^4 ≤ 467^4*2000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3 2000000000 467 50000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5 : ℝ)) 5 4 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-3/2000000000 : ℝ), (9999999999/10000000000 : ℝ), (-3/2000000000 : ℝ)] ![(467/50000000000000 : ℝ), (99999999987501/100000000000000 : ℝ), (467/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-3/2000000000 : ℝ)|^5 ≤ (467/50000000000000 : ℝ)^4
        have hw : |(-3/2000000000 : ℝ)|=(3/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(9999999999/10000000000 : ℝ)|^5 ≤ (99999999987501/100000000000000 : ℝ)^4
        have hw : |(9999999999/10000000000 : ℝ)|=(9999999999/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3/2000000000 : ℝ)|^5 ≤ (467/50000000000000 : ℝ)^4
        have hw : |(-3/2000000000 : ℝ)|=(3/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c318022_s0_7 (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ)) (x : Fin 3 → ℝ) :
    (-2799537971/10000000000 : ℝ)*x 0 + (200711551/500000000 : ℝ)*x 1 + (-276482261/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2799537971/10000000000 : ℝ)^5 ≤ (20363759201519/100000000000000 : ℝ)^4 := by
    have hnat : (2799537971 : ℕ)^5*100000000000000^4 ≤ 20363759201519^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2799537971 10000000000 20363759201519 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (200711551/500000000 : ℝ)^5 ≤ (31952360929363/100000000000000 : ℝ)^4 := by
    have hnat : (200711551 : ℕ)^5*100000000000000^4 ≤ 31952360929363^4*500000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      200711551 500000000 31952360929363 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (276482261/500000000 : ℝ)^5 ≤ (47683879852723/100000000000000 : ℝ)^4 := by
    have hnat : (276482261 : ℕ)^5*100000000000000^4 ≤ 47683879852723^4*500000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      276482261 500000000 47683879852723 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5 : ℝ)) 5 4 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2799537971/10000000000 : ℝ), (200711551/500000000 : ℝ), (-276482261/500000000 : ℝ)] ![(20363759201519/100000000000000 : ℝ), (31952360929363/100000000000000 : ℝ), (47683879852723/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2799537971/10000000000 : ℝ)|^5 ≤ (20363759201519/100000000000000 : ℝ)^4
        have hw : |(-2799537971/10000000000 : ℝ)|=(2799537971/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(200711551/500000000 : ℝ)|^5 ≤ (31952360929363/100000000000000 : ℝ)^4
        have hw : |(200711551/500000000 : ℝ)|=(200711551/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-276482261/500000000 : ℝ)|^5 ≤ (47683879852723/100000000000000 : ℝ)^4
        have hw : |(-276482261/500000000 : ℝ)|=(276482261/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c318022_s0_8 (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ)) (x : Fin 3 → ℝ) :
    (7246904119/10000000000 : ℝ)*x 0 + (-500289397/10000000000 : ℝ)*x 1 + (-3894971083/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (7246904119/10000000000 : ℝ)^5 ≤ (66863736793009/100000000000000 : ℝ)^4 := by
    have hnat : (7246904119 : ℕ)^5*100000000000000^4 ≤ 66863736793009^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7246904119 10000000000 66863736793009 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (500289397/10000000000 : ℝ)^5 ≤ (2366064738653/100000000000000 : ℝ)^4 := by
    have hnat : (500289397 : ℕ)^5*100000000000000^4 ≤ 2366064738653^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      500289397 10000000000 2366064738653 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3894971083/10000000000 : ℝ)^5 ≤ (769254961189/2500000000000 : ℝ)^4 := by
    have hnat : (3894971083 : ℕ)^5*2500000000000^4 ≤ 769254961189^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3894971083 10000000000 769254961189 2500000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5 : ℝ)) 5 4 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(7246904119/10000000000 : ℝ), (-500289397/10000000000 : ℝ), (-3894971083/10000000000 : ℝ)] ![(66863736793009/100000000000000 : ℝ), (2366064738653/100000000000000 : ℝ), (769254961189/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(7246904119/10000000000 : ℝ)|^5 ≤ (66863736793009/100000000000000 : ℝ)^4
        have hw : |(7246904119/10000000000 : ℝ)|=(7246904119/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-500289397/10000000000 : ℝ)|^5 ≤ (2366064738653/100000000000000 : ℝ)^4
        have hw : |(-500289397/10000000000 : ℝ)|=(500289397/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3894971083/10000000000 : ℝ)|^5 ≤ (769254961189/2500000000000 : ℝ)^4
        have hw : |(-3894971083/10000000000 : ℝ)|=(3894971083/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c318022_s0_9 (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ)) (x : Fin 3 → ℝ) :
    (1900407103/10000000000 : ℝ)*x 0 + (3236965551/5000000000 : ℝ)*x 1 + (375368263/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1900407103/10000000000 : ℝ)^5 ≤ (12547531834879/100000000000000 : ℝ)^4 := by
    have hnat : (1900407103 : ℕ)^5*100000000000000^4 ≤ 12547531834879^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1900407103 10000000000 12547531834879 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3236965551/5000000000 : ℝ)^5 ≤ (14517776297427/25000000000000 : ℝ)^4 := by
    have hnat : (3236965551 : ℕ)^5*25000000000000^4 ≤ 14517776297427^4*5000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3236965551 5000000000 14517776297427 25000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (375368263/1000000000 : ℝ)^5 ≤ (3672670371081/12500000000000 : ℝ)^4 := by
    have hnat : (375368263 : ℕ)^5*12500000000000^4 ≤ 3672670371081^4*1000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      375368263 1000000000 3672670371081 12500000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5 : ℝ)) 5 4 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1900407103/10000000000 : ℝ), (3236965551/5000000000 : ℝ), (375368263/1000000000 : ℝ)] ![(12547531834879/100000000000000 : ℝ), (14517776297427/25000000000000 : ℝ), (3672670371081/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1900407103/10000000000 : ℝ)|^5 ≤ (12547531834879/100000000000000 : ℝ)^4
        have hw : |(1900407103/10000000000 : ℝ)|=(1900407103/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3236965551/5000000000 : ℝ)|^5 ≤ (14517776297427/25000000000000 : ℝ)^4
        have hw : |(3236965551/5000000000 : ℝ)|=(3236965551/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(375368263/1000000000 : ℝ)|^5 ≤ (3672670371081/12500000000000 : ℝ)^4
        have hw : |(375368263/1000000000 : ℝ)|=(375368263/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c318022_s0_13 (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ)) (x : Fin 3 → ℝ) :
    (587606633/2000000000 : ℝ)*x 0 + (1845274683/2500000000 : ℝ)*x 1 + (-789547787/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (587606633/2000000000 : ℝ)^5 ≤ (173045716861/800000000000 : ℝ)^4 := by
    have hnat : (587606633 : ℕ)^5*800000000000^4 ≤ 173045716861^4*2000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      587606633 2000000000 173045716861 800000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1845274683/2500000000 : ℝ)^5 ≤ (34207495037207/50000000000000 : ℝ)^4 := by
    have hnat : (1845274683 : ℕ)^5*50000000000000^4 ≤ 34207495037207^4*2500000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1845274683 2500000000 34207495037207 50000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (789547787/5000000000 : ℝ)^5 ≤ (9954295303123/100000000000000 : ℝ)^4 := by
    have hnat : (789547787 : ℕ)^5*100000000000000^4 ≤ 9954295303123^4*5000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      789547787 5000000000 9954295303123 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5 : ℝ)) 5 4 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(587606633/2000000000 : ℝ), (1845274683/2500000000 : ℝ), (-789547787/5000000000 : ℝ)] ![(173045716861/800000000000 : ℝ), (34207495037207/50000000000000 : ℝ), (9954295303123/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(587606633/2000000000 : ℝ)|^5 ≤ (173045716861/800000000000 : ℝ)^4
        have hw : |(587606633/2000000000 : ℝ)|=(587606633/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1845274683/2500000000 : ℝ)|^5 ≤ (34207495037207/50000000000000 : ℝ)^4
        have hw : |(1845274683/2500000000 : ℝ)|=(1845274683/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-789547787/5000000000 : ℝ)|^5 ≤ (9954295303123/100000000000000 : ℝ)^4
        have hw : |(-789547787/5000000000 : ℝ)|=(789547787/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c318022_s0_14 (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ)) (x : Fin 3 → ℝ) :
    (-2807032663/10000000000 : ℝ)*x 0 + (4315858731/10000000000 : ℝ)*x 1 + (-5240419279/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2807032663/10000000000 : ℝ)^5 ≤ (20431927209669/100000000000000 : ℝ)^4 := by
    have hnat : (2807032663 : ℕ)^5*100000000000000^4 ≤ 20431927209669^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2807032663 10000000000 20431927209669 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4315858731/10000000000 : ℝ)^5 ≤ (34981145417863/100000000000000 : ℝ)^4 := by
    have hnat : (4315858731 : ℕ)^5*100000000000000^4 ≤ 34981145417863^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4315858731 10000000000 34981145417863 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5240419279/10000000000 : ℝ)^5 ≤ (44586927358427/100000000000000 : ℝ)^4 := by
    have hnat : (5240419279 : ℕ)^5*100000000000000^4 ≤ 44586927358427^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5240419279 10000000000 44586927358427 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5 : ℝ)) 5 4 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2807032663/10000000000 : ℝ), (4315858731/10000000000 : ℝ), (-5240419279/10000000000 : ℝ)] ![(20431927209669/100000000000000 : ℝ), (34981145417863/100000000000000 : ℝ), (44586927358427/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2807032663/10000000000 : ℝ)|^5 ≤ (20431927209669/100000000000000 : ℝ)^4
        have hw : |(-2807032663/10000000000 : ℝ)|=(2807032663/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4315858731/10000000000 : ℝ)|^5 ≤ (34981145417863/100000000000000 : ℝ)^4
        have hw : |(4315858731/10000000000 : ℝ)|=(4315858731/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-5240419279/10000000000 : ℝ)|^5 ≤ (44586927358427/100000000000000 : ℝ)^4
        have hw : |(-5240419279/10000000000 : ℝ)|=(5240419279/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c318022_s0_15 (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ)) (x : Fin 3 → ℝ) :
    (7791278231/10000000000 : ℝ)*x 0 + (-1363284991/10000000000 : ℝ)*x 1 + (-1297211423/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (7791278231/10000000000 : ℝ)^5 ≤ (1829999202991/2500000000000 : ℝ)^4 := by
    have hnat : (7791278231 : ℕ)^5*2500000000000^4 ≤ 1829999202991^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7791278231 10000000000 1829999202991 2500000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1363284991/10000000000 : ℝ)^5 ≤ (4141935399819/50000000000000 : ℝ)^4 := by
    have hnat : (1363284991 : ℕ)^5*50000000000000^4 ≤ 4141935399819^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1363284991 10000000000 4141935399819 50000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1297211423/5000000000 : ℝ)^5 ≤ (18516161069603/100000000000000 : ℝ)^4 := by
    have hnat : (1297211423 : ℕ)^5*100000000000000^4 ≤ 18516161069603^4*5000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1297211423 5000000000 18516161069603 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5 : ℝ)) 5 4 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(7791278231/10000000000 : ℝ), (-1363284991/10000000000 : ℝ), (-1297211423/5000000000 : ℝ)] ![(1829999202991/2500000000000 : ℝ), (4141935399819/50000000000000 : ℝ), (18516161069603/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(7791278231/10000000000 : ℝ)|^5 ≤ (1829999202991/2500000000000 : ℝ)^4
        have hw : |(7791278231/10000000000 : ℝ)|=(7791278231/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1363284991/10000000000 : ℝ)|^5 ≤ (4141935399819/50000000000000 : ℝ)^4
        have hw : |(-1363284991/10000000000 : ℝ)|=(1363284991/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1297211423/5000000000 : ℝ)|^5 ≤ (18516161069603/100000000000000 : ℝ)^4
        have hw : |(-1297211423/5000000000 : ℝ)|=(1297211423/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c318022_s0_16 (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ)) (x : Fin 3 → ℝ) :
    (10616667/50000000 : ℝ)*x 0 + (2792031123/5000000000 : ℝ)*x 1 + (4544737731/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (10616667/50000000 : ℝ)^5 ≤ (7206804538971/50000000000000 : ℝ)^4 := by
    have hnat : (10616667 : ℕ)^5*50000000000000^4 ≤ 7206804538971^4*50000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      10616667 50000000 7206804538971 50000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2792031123/5000000000 : ℝ)^5 ≤ (12067792167709/25000000000000 : ℝ)^4 := by
    have hnat : (2792031123 : ℕ)^5*25000000000000^4 ≤ 12067792167709^4*5000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2792031123 5000000000 12067792167709 25000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4544737731/10000000000 : ℝ)^5 ≤ (37315222227519/100000000000000 : ℝ)^4 := by
    have hnat : (4544737731 : ℕ)^5*100000000000000^4 ≤ 37315222227519^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4544737731 10000000000 37315222227519 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5 : ℝ)) 5 4 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(10616667/50000000 : ℝ), (2792031123/5000000000 : ℝ), (4544737731/10000000000 : ℝ)] ![(7206804538971/50000000000000 : ℝ), (12067792167709/25000000000000 : ℝ), (37315222227519/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(10616667/50000000 : ℝ)|^5 ≤ (7206804538971/50000000000000 : ℝ)^4
        have hw : |(10616667/50000000 : ℝ)|=(10616667/50000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2792031123/5000000000 : ℝ)|^5 ≤ (12067792167709/25000000000000 : ℝ)^4
        have hw : |(2792031123/5000000000 : ℝ)|=(2792031123/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4544737731/10000000000 : ℝ)|^5 ≤ (37315222227519/100000000000000 : ℝ)^4
        have hw : |(4544737731/10000000000 : ℝ)|=(4544737731/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c318022_s0_20 (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ)) (x : Fin 3 → ℝ) :
    (557800647/2000000000 : ℝ)*x 0 + (1165589101/2000000000 : ℝ)*x 1 + (-1847651647/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (557800647/2000000000 : ℝ)^5 ≤ (2026801758919/10000000000000 : ℝ)^4 := by
    have hnat : (557800647 : ℕ)^5*10000000000000^4 ≤ 2026801758919^4*2000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      557800647 2000000000 2026801758919 10000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1165589101/2000000000 : ℝ)^5 ≤ (25460349268571/50000000000000 : ℝ)^4 := by
    have hnat : (1165589101 : ℕ)^5*50000000000000^4 ≤ 25460349268571^4*2000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1165589101 2000000000 25460349268571 50000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1847651647/5000000000 : ℝ)^5 ≤ (28811283867901/100000000000000 : ℝ)^4 := by
    have hnat : (1847651647 : ℕ)^5*100000000000000^4 ≤ 28811283867901^4*5000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1847651647 5000000000 28811283867901 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5 : ℝ)) 5 4 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(557800647/2000000000 : ℝ), (1165589101/2000000000 : ℝ), (-1847651647/5000000000 : ℝ)] ![(2026801758919/10000000000000 : ℝ), (25460349268571/50000000000000 : ℝ), (28811283867901/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(557800647/2000000000 : ℝ)|^5 ≤ (2026801758919/10000000000000 : ℝ)^4
        have hw : |(557800647/2000000000 : ℝ)|=(557800647/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1165589101/2000000000 : ℝ)|^5 ≤ (25460349268571/50000000000000 : ℝ)^4
        have hw : |(1165589101/2000000000 : ℝ)|=(1165589101/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1847651647/5000000000 : ℝ)|^5 ≤ (28811283867901/100000000000000 : ℝ)^4
        have hw : |(-1847651647/5000000000 : ℝ)|=(1847651647/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c318022_s0_21 (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ)) (x : Fin 3 → ℝ) :
    (-1113358547/5000000000 : ℝ)*x 0 + (5211088063/10000000000 : ℝ)*x 1 + (-2422822851/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1113358547/5000000000 : ℝ)^5 ≤ (15296120769647/100000000000000 : ℝ)^4 := by
    have hnat : (1113358547 : ℕ)^5*100000000000000^4 ≤ 15296120769647^4*5000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1113358547 5000000000 15296120769647 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5211088063/10000000000 : ℝ)^5 ≤ (354201586859/800000000000 : ℝ)^4 := by
    have hnat : (5211088063 : ℕ)^5*800000000000^4 ≤ 354201586859^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5211088063 10000000000 354201586859 800000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2422822851/5000000000 : ℝ)^5 ≤ (20214340424717/50000000000000 : ℝ)^4 := by
    have hnat : (2422822851 : ℕ)^5*50000000000000^4 ≤ 20214340424717^4*5000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2422822851 5000000000 20214340424717 50000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5 : ℝ)) 5 4 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1113358547/5000000000 : ℝ), (5211088063/10000000000 : ℝ), (-2422822851/5000000000 : ℝ)] ![(15296120769647/100000000000000 : ℝ), (354201586859/800000000000 : ℝ), (20214340424717/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1113358547/5000000000 : ℝ)|^5 ≤ (15296120769647/100000000000000 : ℝ)^4
        have hw : |(-1113358547/5000000000 : ℝ)|=(1113358547/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5211088063/10000000000 : ℝ)|^5 ≤ (354201586859/800000000000 : ℝ)^4
        have hw : |(5211088063/10000000000 : ℝ)|=(5211088063/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2422822851/5000000000 : ℝ)|^5 ≤ (20214340424717/50000000000000 : ℝ)^4
        have hw : |(-2422822851/5000000000 : ℝ)|=(2422822851/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c318022_s0_22 (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ)) (x : Fin 3 → ℝ) :
    (393046697/500000000 : ℝ)*x 0 + (-155945353/2500000000 : ℝ)*x 1 + (-3071264933/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (393046697/500000000 : ℝ)^5 ≤ (4626181852921/6250000000000 : ℝ)^4 := by
    have hnat : (393046697 : ℕ)^5*6250000000000^4 ≤ 4626181852921^4*500000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      393046697 500000000 4626181852921 6250000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (155945353/2500000000 : ℝ)^5 ≤ (1558692841051/50000000000000 : ℝ)^4 := by
    have hnat : (155945353 : ℕ)^5*50000000000000^4 ≤ 1558692841051^4*2500000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      155945353 2500000000 1558692841051 50000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3071264933/10000000000 : ℝ)^5 ≤ (22863704652687/100000000000000 : ℝ)^4 := by
    have hnat : (3071264933 : ℕ)^5*100000000000000^4 ≤ 22863704652687^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3071264933 10000000000 22863704652687 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5 : ℝ)) 5 4 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(393046697/500000000 : ℝ), (-155945353/2500000000 : ℝ), (-3071264933/10000000000 : ℝ)] ![(4626181852921/6250000000000 : ℝ), (1558692841051/50000000000000 : ℝ), (22863704652687/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(393046697/500000000 : ℝ)|^5 ≤ (4626181852921/6250000000000 : ℝ)^4
        have hw : |(393046697/500000000 : ℝ)|=(393046697/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-155945353/2500000000 : ℝ)|^5 ≤ (1558692841051/50000000000000 : ℝ)^4
        have hw : |(-155945353/2500000000 : ℝ)|=(155945353/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3071264933/10000000000 : ℝ)|^5 ≤ (22863704652687/100000000000000 : ℝ)^4
        have hw : |(-3071264933/10000000000 : ℝ)|=(3071264933/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c318022_s0_23 (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ)) (x : Fin 3 → ℝ) :
    (2101283411/10000000000 : ℝ)*x 0 + (111495763/200000000 : ℝ)*x 1 + (571585573/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2101283411/10000000000 : ℝ)^5 ≤ (14226752946927/100000000000000 : ℝ)^4 := by
    have hnat : (2101283411 : ℕ)^5*100000000000000^4 ≤ 14226752946927^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2101283411 10000000000 14226752946927 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (111495763/200000000 : ℝ)^5 ≤ (376335762613/781250000000 : ℝ)^4 := by
    have hnat : (111495763 : ℕ)^5*781250000000^4 ≤ 376335762613^4*200000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      111495763 200000000 376335762613 781250000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (571585573/1250000000 : ℝ)^5 ≤ (37602269427603/100000000000000 : ℝ)^4 := by
    have hnat : (571585573 : ℕ)^5*100000000000000^4 ≤ 37602269427603^4*1250000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      571585573 1250000000 37602269427603 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5 : ℝ)) 5 4 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2101283411/10000000000 : ℝ), (111495763/200000000 : ℝ), (571585573/1250000000 : ℝ)] ![(14226752946927/100000000000000 : ℝ), (376335762613/781250000000 : ℝ), (37602269427603/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2101283411/10000000000 : ℝ)|^5 ≤ (14226752946927/100000000000000 : ℝ)^4
        have hw : |(2101283411/10000000000 : ℝ)|=(2101283411/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(111495763/200000000 : ℝ)|^5 ≤ (376335762613/781250000000 : ℝ)^4
        have hw : |(111495763/200000000 : ℝ)|=(111495763/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(571585573/1250000000 : ℝ)|^5 ≤ (37602269427603/100000000000000 : ℝ)^4
        have hw : |(571585573/1250000000 : ℝ)|=(571585573/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c318022_s0_26 (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ)) (x : Fin 3 → ℝ) :
    (1050104561/2500000000 : ℝ)*x 0 + (6265112209/10000000000 : ℝ)*x 1 + (-820551181/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1050104561/2500000000 : ℝ)^5 ≤ (8453872212637/25000000000000 : ℝ)^4 := by
    have hnat : (1050104561 : ℕ)^5*25000000000000^4 ≤ 8453872212637^4*2500000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1050104561 2500000000 8453872212637 25000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6265112209/10000000000 : ℝ)^5 ≤ (13934810777849/25000000000000 : ℝ)^4 := by
    have hnat : (6265112209 : ℕ)^5*25000000000000^4 ≤ 13934810777849^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6265112209 10000000000 13934810777849 25000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (820551181/5000000000 : ℝ)^5 ≤ (10445268019143/100000000000000 : ℝ)^4 := by
    have hnat : (820551181 : ℕ)^5*100000000000000^4 ≤ 10445268019143^4*5000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      820551181 5000000000 10445268019143 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5 : ℝ)) 5 4 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1050104561/2500000000 : ℝ), (6265112209/10000000000 : ℝ), (-820551181/5000000000 : ℝ)] ![(8453872212637/25000000000000 : ℝ), (13934810777849/25000000000000 : ℝ), (10445268019143/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1050104561/2500000000 : ℝ)|^5 ≤ (8453872212637/25000000000000 : ℝ)^4
        have hw : |(1050104561/2500000000 : ℝ)|=(1050104561/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6265112209/10000000000 : ℝ)|^5 ≤ (13934810777849/25000000000000 : ℝ)^4
        have hw : |(6265112209/10000000000 : ℝ)|=(6265112209/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-820551181/5000000000 : ℝ)|^5 ≤ (10445268019143/100000000000000 : ℝ)^4
        have hw : |(-820551181/5000000000 : ℝ)|=(820551181/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c318022_s1_0 (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ)) (x : Fin 3 → ℝ) :
    (-3416455669/10000000000 : ℝ)*x 0 + (4603736111/10000000000 : ℝ)*x 1 + (-4412057099/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3416455669/10000000000 : ℝ)^5 ≤ (6529948346799/25000000000000 : ℝ)^4 := by
    have hnat : (3416455669 : ℕ)^5*25000000000000^4 ≤ 6529948346799^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3416455669 10000000000 6529948346799 25000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4603736111/10000000000 : ℝ)^5 ≤ (474021499807/1250000000000 : ℝ)^4 := by
    have hnat : (4603736111 : ℕ)^5*1250000000000^4 ≤ 474021499807^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4603736111 10000000000 474021499807 1250000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4412057099/10000000000 : ℝ)^5 ≤ (17979243308991/50000000000000 : ℝ)^4 := by
    have hnat : (4412057099 : ℕ)^5*50000000000000^4 ≤ 17979243308991^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4412057099 10000000000 17979243308991 50000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5 : ℝ)) 5 4 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-3416455669/10000000000 : ℝ), (4603736111/10000000000 : ℝ), (-4412057099/10000000000 : ℝ)] ![(6529948346799/25000000000000 : ℝ), (474021499807/1250000000000 : ℝ), (17979243308991/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-3416455669/10000000000 : ℝ)|^5 ≤ (6529948346799/25000000000000 : ℝ)^4
        have hw : |(-3416455669/10000000000 : ℝ)|=(3416455669/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4603736111/10000000000 : ℝ)|^5 ≤ (474021499807/1250000000000 : ℝ)^4
        have hw : |(4603736111/10000000000 : ℝ)|=(4603736111/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-4412057099/10000000000 : ℝ)|^5 ≤ (17979243308991/50000000000000 : ℝ)^4
        have hw : |(-4412057099/10000000000 : ℝ)|=(4412057099/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c318022_s1_1 (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ)) (x : Fin 3 → ℝ) :
    (5732885177/10000000000 : ℝ)*x 0 + (-2362061949/10000000000 : ℝ)*x 1 + (-4183806711/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5732885177/10000000000 : ℝ)^5 ≤ (9976921381523/20000000000000 : ℝ)^4 := by
    have hnat : (5732885177 : ℕ)^5*20000000000000^4 ≤ 9976921381523^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5732885177 10000000000 9976921381523 20000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2362061949/10000000000 : ℝ)^5 ≤ (16466985549981/100000000000000 : ℝ)^4 := by
    have hnat : (2362061949 : ℕ)^5*100000000000000^4 ≤ 16466985549981^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2362061949 10000000000 16466985549981 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4183806711/10000000000 : ℝ)^5 ≤ (16824203763931/50000000000000 : ℝ)^4 := by
    have hnat : (4183806711 : ℕ)^5*50000000000000^4 ≤ 16824203763931^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4183806711 10000000000 16824203763931 50000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5 : ℝ)) 5 4 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5732885177/10000000000 : ℝ), (-2362061949/10000000000 : ℝ), (-4183806711/10000000000 : ℝ)] ![(9976921381523/20000000000000 : ℝ), (16466985549981/100000000000000 : ℝ), (16824203763931/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5732885177/10000000000 : ℝ)|^5 ≤ (9976921381523/20000000000000 : ℝ)^4
        have hw : |(5732885177/10000000000 : ℝ)|=(5732885177/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2362061949/10000000000 : ℝ)|^5 ≤ (16466985549981/100000000000000 : ℝ)^4
        have hw : |(-2362061949/10000000000 : ℝ)|=(2362061949/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-4183806711/10000000000 : ℝ)|^5 ≤ (16824203763931/50000000000000 : ℝ)^4
        have hw : |(-4183806711/10000000000 : ℝ)|=(4183806711/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c318022_s1_2 (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ)) (x : Fin 3 → ℝ) :
    (3295221081/10000000000 : ℝ)*x 0 + (304256239/625000000 : ℝ)*x 1 + (425549311/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3295221081/10000000000 : ℝ)^5 ≤ (6241596728551/25000000000000 : ℝ)^4 := by
    have hnat : (3295221081 : ℕ)^5*25000000000000^4 ≤ 6241596728551^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3295221081 10000000000 6241596728551 25000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (304256239/625000000 : ℝ)^5 ≤ (40662993210377/100000000000000 : ℝ)^4 := by
    have hnat : (304256239 : ℕ)^5*100000000000000^4 ≤ 40662993210377^4*625000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      304256239 625000000 40662993210377 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (425549311/1000000000 : ℝ)^5 ≤ (8592654966699/25000000000000 : ℝ)^4 := by
    have hnat : (425549311 : ℕ)^5*25000000000000^4 ≤ 8592654966699^4*1000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      425549311 1000000000 8592654966699 25000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5 : ℝ)) 5 4 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3295221081/10000000000 : ℝ), (304256239/625000000 : ℝ), (425549311/1000000000 : ℝ)] ![(6241596728551/25000000000000 : ℝ), (40662993210377/100000000000000 : ℝ), (8592654966699/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3295221081/10000000000 : ℝ)|^5 ≤ (6241596728551/25000000000000 : ℝ)^4
        have hw : |(3295221081/10000000000 : ℝ)|=(3295221081/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(304256239/625000000 : ℝ)|^5 ≤ (40662993210377/100000000000000 : ℝ)^4
        have hw : |(304256239/625000000 : ℝ)|=(304256239/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(425549311/1000000000 : ℝ)|^5 ≤ (8592654966699/25000000000000 : ℝ)^4
        have hw : |(425549311/1000000000 : ℝ)|=(425549311/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c318022_s1_6 (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ)) (x : Fin 3 → ℝ) :
    (3938521617/10000000000 : ℝ)*x 0 + (5536092579/10000000000 : ℝ)*x 1 + (-143714837/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3938521617/10000000000 : ℝ)^5 ≤ (15600429176101/50000000000000 : ℝ)^4 := by
    have hnat : (3938521617 : ℕ)^5*50000000000000^4 ≤ 15600429176101^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3938521617 10000000000 15600429176101 50000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5536092579/10000000000 : ℝ)^5 ≤ (47753386998719/100000000000000 : ℝ)^4 := by
    have hnat : (5536092579 : ℕ)^5*100000000000000^4 ≤ 47753386998719^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5536092579 10000000000 47753386998719 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (143714837/500000000 : ℝ)^5 ≤ (10522877319563/50000000000000 : ℝ)^4 := by
    have hnat : (143714837 : ℕ)^5*50000000000000^4 ≤ 10522877319563^4*500000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      143714837 500000000 10522877319563 50000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5 : ℝ)) 5 4 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3938521617/10000000000 : ℝ), (5536092579/10000000000 : ℝ), (-143714837/500000000 : ℝ)] ![(15600429176101/50000000000000 : ℝ), (47753386998719/100000000000000 : ℝ), (10522877319563/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3938521617/10000000000 : ℝ)|^5 ≤ (15600429176101/50000000000000 : ℝ)^4
        have hw : |(3938521617/10000000000 : ℝ)|=(3938521617/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5536092579/10000000000 : ℝ)|^5 ≤ (47753386998719/100000000000000 : ℝ)^4
        have hw : |(5536092579/10000000000 : ℝ)|=(5536092579/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-143714837/500000000 : ℝ)|^5 ≤ (10522877319563/50000000000000 : ℝ)^4
        have hw : |(-143714837/500000000 : ℝ)|=(143714837/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c318022 (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (7299/4000 : ℝ) (34269/20000 : ℝ) (39911/50000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![true, true, false]]) : False := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (39911/50000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (39911/50000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (39911/50000 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (39911/50000 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 2+X 2 2)) ∧ ((-1 : ℝ)*(X 0 2+X 2 2)) ≤ ((-1 : ℝ)*(X 0 0+X 2 0)) ∧ ((-1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 2) ∧ ((-1 : ℝ)*pair X 1 2) ≤ ((-1 : ℝ)*pair X 1 0) ∧ ((-1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (39911/50000 : ℝ)*P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (39911/50000 : ℝ)*P 2 ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base3 : ((1 : ℝ)*N 1+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 1]
  have base25 : ((1 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 2).2]
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base49 : ((1 : ℝ)*X 0 2+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.1]
  have base50 : ((1 : ℝ)*X 0 0+(-1 : ℝ)*X 0 2+(1 : ℝ)*X 2 0+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.2.1]
  have base60 : ((-1 : ℝ)*X 0 0+(1 : ℝ)*X 0 1+(-1 : ℝ)*X 1 0+(1 : ℝ)*X 1 1) ≤ (0 : ℝ) := by
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
  have s0_pow0 : (1 : ℝ) ^ (39/8 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^39 ≤ (1 : ℝ)^8 := by
      have hnat : (1 : ℕ)^39*1^8 ≤ 1^8*1^39 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 39 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 39 8 (by norm_num) hpowers
    exact h
  have s0_corner0a : (2 : ℝ) ≤ (5763943924246341/5000000000000000 : ℝ) ^ (39/8 : ℝ) := by
    have hpowers : (2 : ℝ)^8 ≤ (5763943924246341/5000000000000000 : ℝ)^39 := by
      have hnat : (2 : ℕ)^8*5000000000000000^39 ≤ 5763943924246341^39*1^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 5763943924246341 5000000000000000 8 39 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5763943924246341/5000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 39 8 (by norm_num) hpowers
    exact h
  have s0_corner0b : (3 : ℝ) ≤ (782980676308869/625000000000000 : ℝ) ^ (39/8 : ℝ) := by
    have hpowers : (3 : ℝ)^8 ≤ (782980676308869/625000000000000 : ℝ)^39 := by
      have hnat : (3 : ℕ)^8*625000000000000^39 ≤ 782980676308869^39*1^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 782980676308869 625000000000000 8 39 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (782980676308869/625000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 39 8 (by norm_num) hpowers
    exact h
  have major_s0_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(763943924246341/5000000000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(499901486224611/5000000000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (39/8 : ℝ)) (rho := (1 : ℝ)) (alpha := (763943924246341/5000000000000000 : ℝ)) (beta := (499901486224611/5000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow0,s0_corner0a]) (by linarith only [s0_pow0,s0_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![true, true, false]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (1 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order0.2.2])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(763943924246341/5000000000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(499901486224611/5000000000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow1 : (1 : ℝ) ^ (39/8 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^39 ≤ (1 : ℝ)^8 := by
      have hnat : (1 : ℕ)^39*1^8 ≤ 1^8*1^39 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 39 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 39 8 (by norm_num) hpowers
    exact h
  have s0_corner1a : (2 : ℝ) ≤ (5763943924246341/5000000000000000 : ℝ) ^ (39/8 : ℝ) := by
    have hpowers : (2 : ℝ)^8 ≤ (5763943924246341/5000000000000000 : ℝ)^39 := by
      have hnat : (2 : ℕ)^8*5000000000000000^39 ≤ 5763943924246341^39*1^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 5763943924246341 5000000000000000 8 39 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5763943924246341/5000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 39 8 (by norm_num) hpowers
    exact h
  have s0_corner1b : (3 : ℝ) ≤ (782980676308869/625000000000000 : ℝ) ^ (39/8 : ℝ) := by
    have hpowers : (3 : ℝ)^8 ≤ (782980676308869/625000000000000 : ℝ)^39 := by
      have hnat : (3 : ℕ)^8*625000000000000^39 ≤ 782980676308869^39*1^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 782980676308869 625000000000000 8 39 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (782980676308869/625000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 39 8 (by norm_num) hpowers
    exact h
  have major_s0_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(763943924246341/5000000000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 2 0))+(499901486224611/5000000000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (39/8 : ℝ)) (rho := (1 : ℝ)) (alpha := (763943924246341/5000000000000000 : ℝ)) (beta := (499901486224611/5000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow1,s0_corner1a]) (by linarith only [s0_pow1,s0_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![true, true, false]] hX 1 (by
        change ((-1 : ℝ)*pair X 1 0) ≤ (1 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order1.2.2])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(763943924246341/5000000000000000 : ℝ)*((-1 : ℝ)*pair X 1 0)+(499901486224611/5000000000000000 : ℝ)*((-1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow2 : (1 : ℝ) ^ (39/8 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^39 ≤ (1 : ℝ)^8 := by
      have hnat : (1 : ℕ)^39*1^8 ≤ 1^8*1^39 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 39 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 39 8 (by norm_num) hpowers
    exact h
  have s0_corner2a : (2 : ℝ) ≤ (5763943924246341/5000000000000000 : ℝ) ^ (39/8 : ℝ) := by
    have hpowers : (2 : ℝ)^8 ≤ (5763943924246341/5000000000000000 : ℝ)^39 := by
      have hnat : (2 : ℕ)^8*5000000000000000^39 ≤ 5763943924246341^39*1^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 5763943924246341 5000000000000000 8 39 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5763943924246341/5000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 39 8 (by norm_num) hpowers
    exact h
  have s0_corner2b : (3 : ℝ) ≤ (782980676308869/625000000000000 : ℝ) ^ (39/8 : ℝ) := by
    have hpowers : (3 : ℝ)^8 ≤ (782980676308869/625000000000000 : ℝ)^39 := by
      have hnat : (3 : ℕ)^8*625000000000000^39 ≤ 782980676308869^39*1^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 782980676308869 625000000000000 8 39 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (782980676308869/625000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 39 8 (by norm_num) hpowers
    exact h
  have major_s0_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(763943924246341/5000000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(499901486224611/5000000000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (39/8 : ℝ)) (rho := (1 : ℝ)) (alpha := (763943924246341/5000000000000000 : ℝ)) (beta := (499901486224611/5000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow2,s0_corner2a]) (by linarith only [s0_pow2,s0_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![true, true, false]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (1 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order2.2.2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(763943924246341/5000000000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(499901486224611/5000000000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s0_1 : ((3488326599/5000000000 : ℝ)*X 1 0+(-1103345913/10000000000 : ℝ)*X 1 1+(-475562791/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c318022_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_2 : ((2542176653/10000000000 : ℝ)*X 2 0+(5476644871/10000000000 : ℝ)*X 2 1+(4301476111/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c318022_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_4 : ((-3/2000000000 : ℝ)*X 0 0+(9999999999/10000000000 : ℝ)*X 0 1+(-3/2000000000 : ℝ)*X 0 2+(-3/2000000000 : ℝ)*X 2 0+(9999999999/10000000000 : ℝ)*X 2 1+(-3/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*P 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c318022_s0_4 p hpa hpb (pair X 1)
    change _ ≤ P 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_7 : ((-2799537971/10000000000 : ℝ)*X 0 0+(200711551/500000000 : ℝ)*X 0 1+(-276482261/500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c318022_s0_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_8 : ((7246904119/10000000000 : ℝ)*X 1 0+(-500289397/10000000000 : ℝ)*X 1 1+(-3894971083/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c318022_s0_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_9 : ((1900407103/10000000000 : ℝ)*X 2 0+(3236965551/5000000000 : ℝ)*X 2 1+(375368263/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c318022_s0_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_13 : ((587606633/2000000000 : ℝ)*X 0 0+(1845274683/2500000000 : ℝ)*X 0 1+(-789547787/5000000000 : ℝ)*X 0 2+(587606633/2000000000 : ℝ)*X 1 0+(1845274683/2500000000 : ℝ)*X 1 1+(-789547787/5000000000 : ℝ)*X 1 2+(587606633/2000000000 : ℝ)*X 2 0+(1845274683/2500000000 : ℝ)*X 2 1+(-789547787/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c318022_s0_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_14 : ((-2807032663/10000000000 : ℝ)*X 0 0+(4315858731/10000000000 : ℝ)*X 0 1+(-5240419279/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c318022_s0_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_15 : ((7791278231/10000000000 : ℝ)*X 1 0+(-1363284991/10000000000 : ℝ)*X 1 1+(-1297211423/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c318022_s0_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_16 : ((10616667/50000000 : ℝ)*X 2 0+(2792031123/5000000000 : ℝ)*X 2 1+(4544737731/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c318022_s0_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_20 : ((557800647/2000000000 : ℝ)*X 0 0+(1165589101/2000000000 : ℝ)*X 0 1+(-1847651647/5000000000 : ℝ)*X 0 2+(557800647/2000000000 : ℝ)*X 1 0+(1165589101/2000000000 : ℝ)*X 1 1+(-1847651647/5000000000 : ℝ)*X 1 2+(557800647/2000000000 : ℝ)*X 2 0+(1165589101/2000000000 : ℝ)*X 2 1+(-1847651647/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c318022_s0_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_21 : ((-1113358547/5000000000 : ℝ)*X 0 0+(5211088063/10000000000 : ℝ)*X 0 1+(-2422822851/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c318022_s0_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_22 : ((393046697/500000000 : ℝ)*X 1 0+(-155945353/2500000000 : ℝ)*X 1 1+(-3071264933/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c318022_s0_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_23 : ((2101283411/10000000000 : ℝ)*X 2 0+(111495763/200000000 : ℝ)*X 2 1+(571585573/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c318022_s0_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_26 : ((1050104561/2500000000 : ℝ)*X 0 0+(6265112209/10000000000 : ℝ)*X 0 1+(-820551181/5000000000 : ℝ)*X 0 2+(1050104561/2500000000 : ℝ)*X 1 0+(6265112209/10000000000 : ℝ)*X 1 1+(-820551181/5000000000 : ℝ)*X 1 2+(1050104561/2500000000 : ℝ)*X 2 0+(6265112209/10000000000 : ℝ)*X 2 1+(-820551181/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c318022_s0_26 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s0_0 : (0 : ℝ) ≤ ((27211/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(27211/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (9432012561376597091583/1250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (161663441119/125000000000 : ℝ)*(base39) + (11221574837/8000000000 : ℝ)*(base50) + (58746194793/100000000000 : ℝ)*(base60) + (1043240077197/200000000000 : ℝ)*(major_s0_0) + (8261061431427/1000000000000 : ℝ)*(major_s0_1) + (1043240077197/200000000000 : ℝ)*(major_s0_2) + (5480123/50000000000 : ℝ)*(sp_s0_1) + (1522430522721/500000000000 : ℝ)*(sp_s0_4) + (7573791630167/1000000000000 : ℝ)*(sp_s0_7) + (757370507519/100000000000 : ℝ)*(sp_s0_8) + (946717244243/125000000000 : ℝ)*(sp_s0_9) + (357322947389/125000000000 : ℝ)*(sp_s0_13) + (23047483/1000000000000 : ℝ)*(sp_s0_21) + (38361853/500000000000 : ℝ)*(sp_s0_23) + (357322947389/125000000000 : ℝ)*(f.failure) + (151476293553/20000000000 : ℝ)*(f.sum) + (1694489825636139/2500000000000000000000000000 : ℝ)*base63 + (244439909804633/1000000000000000000000000000 : ℝ)*base64 + (1342693834249897/5000000000000000000000000000 : ℝ)*base66 + (517842467786177/1000000000000000000000000000 : ℝ)*base69 + (34540168914807/125000000000000000000000000 : ℝ)*base70 + (303542515095367/1000000000000000000000000000 : ℝ)*base73 + (1035429748841393/5000000000000000000000000000 : ℝ)*base75 + (163715811786177/1000000000000000000000000000 : ℝ)*base77 + (252542178613469/2500000000000000000000000000 : ℝ)*base79 + (189/500000000000000 : ℝ)*base86 + (189/500000000000000 : ℝ)*base88 + (189/500000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s0_1 : (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(1133/12500 : ℝ)*X 0 1+(1 : ℝ)*X 2 0+(1133/12500 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (2926589896378815348891/156250000000000000000000000 : ℝ) := by norm_num
    linear_combination (1285835349049/1000000000000 : ℝ)*(base39) + (273700752127/500000000000 : ℝ)*(base50) + (526395254143/1000000000000 : ℝ)*(base60) + (250509953673/62500000000 : ℝ)*(major_s0_0) + (250509953673/62500000000 : ℝ)*(major_s0_1) + (250509953673/62500000000 : ℝ)*(major_s0_2) + (98063237/250000000000 : ℝ)*(sp_s0_2) + (131901463/1000000000000 : ℝ)*(sp_s0_7) + (5819627826427/1000000000000 : ℝ)*(sp_s0_14) + (5819709186313/1000000000000 : ℝ)*(sp_s0_15) + (363464035101/62500000000 : ℝ)*(sp_s0_16) + (2196552546249/1000000000000 : ℝ)*(sp_s0_20) + (50541577/1000000000000 : ℝ)*(sp_s0_22) + (3942913327/1000000000000 : ℝ)*(sp_s0_23) + (2196552546249/1000000000000 : ℝ)*(f.failure) + (581975972789/100000000000 : ℝ)*(f.sum) + (7565578841/10000000000000000000000 : ℝ)*base62 + (252317184258703/312500000000000000000000000 : ℝ)*base65 + (24821557477453/312500000000000000000000000 : ℝ)*base66 + (3313125177007/312500000000000000000000000 : ℝ)*base68 + (36066268692299/78125000000000000000000000 : ℝ)*base71 + (195307894272547/312500000000000000000000000 : ℝ)*base72 + (66668829635493/312500000000000000000000000 : ℝ)*base74 + (54482620208257/312500000000000000000000000 : ℝ)*base76 + (2032432643/5000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base85 + (549/4000000000000000 : ℝ)*base86 + (549/4000000000000000 : ℝ)*base88 + (549/4000000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s0_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-5519/25000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-5519/25000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (188835950489628638289/31250000000000000000000000 : ℝ) := by norm_num
    linear_combination (1443560466669/1000000000000 : ℝ)*(base39) + (638562114003/500000000000 : ℝ)*(base50) + (71059/62500000000 : ℝ)*(base60) + (5713144507/1250000000 : ℝ)*(major_s0_0) + (692804310939/125000000000 : ℝ)*(major_s0_1) + (5713144507/1250000000 : ℝ)*(major_s0_2) + (121489860239/125000000000 : ℝ)*(sp_s0_4) + (6587/31250000000 : ℝ)*(sp_s0_13) + (15807757/1000000000000 : ℝ)*(sp_s0_15) + (1169092637/1000000000000 : ℝ)*(sp_s0_16) + (414768373117/62500000000 : ℝ)*(sp_s0_21) + (1659069540529/250000000000 : ℝ)*(sp_s0_22) + (1327024975447/200000000000 : ℝ)*(sp_s0_23) + (78272969259/31250000000 : ℝ)*(sp_s0_26) + (39136487923/15625000000 : ℝ)*(f.failure) + (414768373117/62500000000 : ℝ)*(f.sum) + (261695808635499/625000000000000000000000000 : ℝ)*base62 + (2635164046777/6250000000000000000000000 : ℝ)*base65 + (25391880180271/625000000000000000000000000 : ℝ)*base67 + (188304084497/1562500000000000000000000 : ℝ)*base68 + (570374922539/6250000000000000000000000 : ℝ)*base71 + (2079650938027/6250000000000000000000000 : ℝ)*base73 + (53454230586699/625000000000000000000000000 : ℝ)*base74 + (3013478923887/6250000000000000000000000 : ℝ)*base77 + (642672039420471/625000000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base83 + (23/62500000000000 : ℝ)*base86 + (23/62500000000000 : ℝ)*base88 + (23/62500000000000 : ℝ)*base90 + hcertificate_margin
  have s1_pow0 : (27211/100000 : ℝ) ^ (39/8 : ℝ) ≤ (87770678005798321/50000000000000000000 : ℝ) := by
    have hpowers : (27211/100000 : ℝ)^39 ≤ (87770678005798321/50000000000000000000 : ℝ)^8 := by
      have hnat : (27211 : ℕ)^39*50000000000000000000^8 ≤ 87770678005798321^8*100000^39 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        27211 100000 87770678005798321 50000000000000000000 39 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (27211/100000 : ℝ)) (X := (87770678005798321/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 39 8 (by norm_num) hpowers
    exact h
  have s1_corner0a : (50087770678005798321/50000000000000000000 : ℝ) ≤ (2500899584695017/2500000000000000 : ℝ) ^ (39/8 : ℝ) := by
    have hpowers : (50087770678005798321/50000000000000000000 : ℝ)^8 ≤ (2500899584695017/2500000000000000 : ℝ)^39 := by
      have hnat : (50087770678005798321 : ℕ)^8*2500000000000000^39 ≤ 2500899584695017^39*50000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50087770678005798321 50000000000000000000 2500899584695017 2500000000000000 8 39 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500899584695017/2500000000000000 : ℝ)) (X := (50087770678005798321/50000000000000000000 : ℝ)) (by norm_num) 39 8 (by norm_num) hpowers
    exact h
  have s1_corner0b : (25087770678005798321/25000000000000000000 : ℝ) ≤ (1000719166897833/1000000000000000 : ℝ) ^ (39/8 : ℝ) := by
    have hpowers : (25087770678005798321/25000000000000000000 : ℝ)^8 ≤ (1000719166897833/1000000000000000 : ℝ)^39 := by
      have hnat : (25087770678005798321 : ℕ)^8*1000000000000000^39 ≤ 1000719166897833^39*25000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25087770678005798321 25000000000000000000 1000719166897833 1000000000000000 8 39 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000719166897833/1000000000000000 : ℝ)) (X := (25087770678005798321/25000000000000000000 : ℝ)) (by norm_num) 39 8 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(899584695017/680275000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(1796665099131/1360550000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (39/8 : ℝ)) (rho := (27211/100000 : ℝ)) (alpha := (899584695017/680275000000000 : ℝ)) (beta := (1796665099131/1360550000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![true, true, false]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (27211/100000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(899584695017/680275000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(1796665099131/1360550000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (1133/12500 : ℝ) ^ (39/8 : ℝ) ≤ (103239171388037/12500000000000000000 : ℝ) := by
    have hpowers : (1133/12500 : ℝ)^39 ≤ (103239171388037/12500000000000000000 : ℝ)^8 := by
      have hnat : (1133 : ℕ)^39*12500000000000000000^8 ≤ 103239171388037^8*12500^39 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1133 12500 103239171388037 12500000000000000000 39 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1133/12500 : ℝ)) (X := (103239171388037/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 39 8 (by norm_num) hpowers
    exact h
  have s1_corner1a : (12500103239171388037/12500000000000000000 : ℝ) ≤ (1000001694175713/1000000000000000 : ℝ) ^ (39/8 : ℝ) := by
    have hpowers : (12500103239171388037/12500000000000000000 : ℝ)^8 ≤ (1000001694175713/1000000000000000 : ℝ)^39 := by
      have hnat : (12500103239171388037 : ℕ)^8*1000000000000000^39 ≤ 1000001694175713^39*12500000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12500103239171388037 12500000000000000000 1000001694175713 1000000000000000 8 39 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000001694175713/1000000000000000 : ℝ)) (X := (12500103239171388037/12500000000000000000 : ℝ)) (by norm_num) 39 8 (by norm_num) hpowers
    exact h
  have s1_corner1b : (6250103239171388037/6250000000000000000 : ℝ) ≤ (62500211771269/62500000000000 : ℝ) ^ (39/8 : ℝ) := by
    have hpowers : (6250103239171388037/6250000000000000000 : ℝ)^8 ≤ (62500211771269/62500000000000 : ℝ)^39 := by
      have hnat : (6250103239171388037 : ℕ)^8*62500000000000^39 ≤ 62500211771269^39*6250000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6250103239171388037 6250000000000000000 62500211771269 62500000000000 8 39 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (62500211771269/62500000000000 : ℝ)) (X := (6250103239171388037/6250000000000000000 : ℝ)) (by norm_num) 39 8 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(1694175713/90640000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 2 0))+(1694164591/90640000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (39/8 : ℝ)) (rho := (1133/12500 : ℝ)) (alpha := (1694175713/90640000000000 : ℝ)) (beta := (1694164591/90640000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![true, true, false]] hX 1 (by
        change ((-1 : ℝ)*pair X 1 0) ≤ (1133/12500 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(1694175713/90640000000000 : ℝ)*((-1 : ℝ)*pair X 1 0)+(1694164591/90640000000000 : ℝ)*((-1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (5519/25000 : ℝ) ^ (39/8 : ℝ) ≤ (3958146789296897/6250000000000000000 : ℝ) := by
    have hpowers : (5519/25000 : ℝ)^39 ≤ (3958146789296897/6250000000000000000 : ℝ)^8 := by
      have hnat : (5519 : ℕ)^39*6250000000000000000^8 ≤ 3958146789296897^8*25000^39 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5519 25000 3958146789296897 6250000000000000000 39 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5519/25000 : ℝ)) (X := (3958146789296897/6250000000000000000 : ℝ)) (by norm_num) (by norm_num) 39 8 (by norm_num) hpowers
    exact h
  have s1_corner2a : (6253958146789296897/6250000000000000000 : ℝ) ≤ (1250162344652751/1250000000000000 : ℝ) ^ (39/8 : ℝ) := by
    have hpowers : (6253958146789296897/6250000000000000000 : ℝ)^8 ≤ (1250162344652751/1250000000000000 : ℝ)^39 := by
      have hnat : (6253958146789296897 : ℕ)^8*1250000000000000^39 ≤ 1250162344652751^39*6250000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6253958146789296897 6250000000000000000 1250162344652751 1250000000000000 8 39 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250162344652751/1250000000000000 : ℝ)) (X := (6253958146789296897/6250000000000000000 : ℝ)) (by norm_num) 39 8 (by norm_num) hpowers
    exact h
  have s1_corner2b : (3128958146789296897/3125000000000000000 : ℝ) ≤ (2000519372246813/2000000000000000 : ℝ) ^ (39/8 : ℝ) := by
    have hpowers : (3128958146789296897/3125000000000000000 : ℝ)^8 ≤ (2000519372246813/2000000000000000 : ℝ)^39 := by
      have hnat : (3128958146789296897 : ℕ)^8*2000000000000000^39 ≤ 2000519372246813^39*3125000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3128958146789296897 3125000000000000000 2000519372246813 2000000000000000 8 39 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000519372246813/2000000000000000 : ℝ)) (X := (3128958146789296897/3125000000000000000 : ℝ)) (by norm_num) 39 8 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(162344652751/275950000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(1298104012057/2207600000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (39/8 : ℝ)) (rho := (5519/25000 : ℝ)) (alpha := (162344652751/275950000000000 : ℝ)) (beta := (1298104012057/2207600000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![true, true, false]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (5519/25000 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(162344652751/275950000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(1298104012057/2207600000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-3416455669/10000000000 : ℝ)*X 0 0+(4603736111/10000000000 : ℝ)*X 0 1+(-4412057099/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c318022_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_1 : ((5732885177/10000000000 : ℝ)*X 1 0+(-2362061949/10000000000 : ℝ)*X 1 1+(-4183806711/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c318022_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((3295221081/10000000000 : ℝ)*X 2 0+(304256239/625000000 : ℝ)*X 2 1+(425549311/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c318022_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_6 : ((3938521617/10000000000 : ℝ)*X 0 0+(5536092579/10000000000 : ℝ)*X 0 1+(-143714837/500000000 : ℝ)*X 0 2+(3938521617/10000000000 : ℝ)*X 1 0+(5536092579/10000000000 : ℝ)*X 1 1+(-143714837/500000000 : ℝ)*X 1 2+(3938521617/10000000000 : ℝ)*X 2 0+(5536092579/10000000000 : ℝ)*X 2 1+(-143714837/500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c318022_s1_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have hsep : (-15897/2000 : ℝ) < ((-7299/4000 : ℝ)*P 0+(-7299/4000 : ℝ)*P 1+(-7299/4000 : ℝ)*P 2+(1 : ℝ)*T) := by
    have hcertificate_margin : (-15897/2000 : ℝ) < (-333851919767396679950687355057081/42537779424250000000000000000000 : ℝ) := by norm_num
    linear_combination (519/500000000000 : ℝ)*(base3) + (111/500000000000 : ℝ)*(base25) + (13761757887/31250000000 : ℝ)*(base39) + (92843551097/500000000000 : ℝ)*(base49) + (142198515591/250000000000 : ℝ)*(base50) + (6782070499/100000000000 : ℝ)*(base60) + (7299/4000 : ℝ)*(major_s1_0) + (7299/4000 : ℝ)*(major_s1_1) + (7299/4000 : ℝ)*(major_s1_2) + (2616120886857/1000000000000 : ℝ)*(sp_s1_0) + (654030221897/250000000000 : ℝ)*(sp_s1_1) + (2616120886327/1000000000000 : ℝ)*(sp_s1_2) + (499999999511/500000000000 : ℝ)*(sp_s1_6) + (2616120886549/1000000000000 : ℝ)*(f.sum) + (3818136080867861507/62530270000000000000000000000 : ℝ)*base62 + (4333290725213/11038000000000000000000000 : ℝ)*base65 + (3489137907877359/11330000000000000000000000 : ℝ)*base67 + (67088181231327/1103800000000000000000000 : ℝ)*base68 + (227374159617483233/750887545000000000000000000000 : ℝ)*base71 + (16097662157393/68027500000000000000000000 : ℝ)*base72 + (685813713913113/11330000000000000000000000 : ℝ)*base74 + (21370599167377/136055000000000000000000000 : ℝ)*base77 + (2906181217832747/30830063000000000000000000000 : ℝ)*base78 + (77/250000000000 : ℝ)*base81 + (1/1000000000000 : ℝ)*base83 + (3/50000000000 : ℝ)*base93 + hcertificate_margin
  linarith only [hsep,f.failure]

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem collision_support_c318024_s0_0 (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ)) (x : Fin 3 → ℝ) :
    (-4719430299/10000000000 : ℝ)*x 0 + (590558823/2000000000 : ℝ)*x 1 + (-117985757/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4719430299/10000000000 : ℝ)^5 ≤ (7823335698343/20000000000000 : ℝ)^4 := by
    have hnat : (4719430299 : ℕ)^5*20000000000000^4 ≤ 7823335698343^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4719430299 10000000000 7823335698343 20000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (590558823/2000000000 : ℝ)^5 ≤ (2720830399641/12500000000000 : ℝ)^4 := by
    have hnat : (590558823 : ℕ)^5*12500000000000^4 ≤ 2720830399641^4*2000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      590558823 2000000000 2720830399641 12500000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (117985757/250000000 : ℝ)^5 ≤ (7823335658973/20000000000000 : ℝ)^4 := by
    have hnat : (117985757 : ℕ)^5*20000000000000^4 ≤ 7823335658973^4*250000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      117985757 250000000 7823335658973 20000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5 : ℝ)) 5 4 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-4719430299/10000000000 : ℝ), (590558823/2000000000 : ℝ), (-117985757/250000000 : ℝ)] ![(7823335698343/20000000000000 : ℝ), (2720830399641/12500000000000 : ℝ), (7823335658973/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-4719430299/10000000000 : ℝ)|^5 ≤ (7823335698343/20000000000000 : ℝ)^4
        have hw : |(-4719430299/10000000000 : ℝ)|=(4719430299/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(590558823/2000000000 : ℝ)|^5 ≤ (2720830399641/12500000000000 : ℝ)^4
        have hw : |(590558823/2000000000 : ℝ)|=(590558823/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-117985757/250000000 : ℝ)|^5 ≤ (7823335658973/20000000000000 : ℝ)^4
        have hw : |(-117985757/250000000 : ℝ)|=(117985757/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c318024_s0_1 (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ)) (x : Fin 3 → ℝ) :
    (4719430299/10000000000 : ℝ)*x 0 + (-590558823/2000000000 : ℝ)*x 1 + (-117985757/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4719430299/10000000000 : ℝ)^5 ≤ (7823335698343/20000000000000 : ℝ)^4 := by
    have hnat : (4719430299 : ℕ)^5*20000000000000^4 ≤ 7823335698343^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4719430299 10000000000 7823335698343 20000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (590558823/2000000000 : ℝ)^5 ≤ (2720830399641/12500000000000 : ℝ)^4 := by
    have hnat : (590558823 : ℕ)^5*12500000000000^4 ≤ 2720830399641^4*2000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      590558823 2000000000 2720830399641 12500000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (117985757/250000000 : ℝ)^5 ≤ (7823335658973/20000000000000 : ℝ)^4 := by
    have hnat : (117985757 : ℕ)^5*20000000000000^4 ≤ 7823335658973^4*250000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      117985757 250000000 7823335658973 20000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5 : ℝ)) 5 4 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4719430299/10000000000 : ℝ), (-590558823/2000000000 : ℝ), (-117985757/250000000 : ℝ)] ![(7823335698343/20000000000000 : ℝ), (2720830399641/12500000000000 : ℝ), (7823335658973/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4719430299/10000000000 : ℝ)|^5 ≤ (7823335698343/20000000000000 : ℝ)^4
        have hw : |(4719430299/10000000000 : ℝ)|=(4719430299/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-590558823/2000000000 : ℝ)|^5 ≤ (2720830399641/12500000000000 : ℝ)^4
        have hw : |(-590558823/2000000000 : ℝ)|=(590558823/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-117985757/250000000 : ℝ)|^5 ≤ (7823335658973/20000000000000 : ℝ)^4
        have hw : |(-117985757/250000000 : ℝ)|=(117985757/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c318024_s0_2 (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ)) (x : Fin 3 → ℝ) :
    (3257863801/10000000000 : ℝ)*x 0 + (5814493107/10000000000 : ℝ)*x 1 + (814465947/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3257863801/10000000000 : ℝ)^5 ≤ (12306545437367/50000000000000 : ℝ)^4 := by
    have hnat : (3257863801 : ℕ)^5*50000000000000^4 ≤ 12306545437367^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3257863801 10000000000 12306545437367 50000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5814493107/10000000000 : ℝ)^5 ≤ (50773818358209/100000000000000 : ℝ)^4 := by
    have hnat : (5814493107 : ℕ)^5*100000000000000^4 ≤ 50773818358209^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5814493107 10000000000 50773818358209 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (814465947/2500000000 : ℝ)^5 ≤ (12306545375983/50000000000000 : ℝ)^4 := by
    have hnat : (814465947 : ℕ)^5*50000000000000^4 ≤ 12306545375983^4*2500000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      814465947 2500000000 12306545375983 50000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5 : ℝ)) 5 4 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3257863801/10000000000 : ℝ), (5814493107/10000000000 : ℝ), (814465947/2500000000 : ℝ)] ![(12306545437367/50000000000000 : ℝ), (50773818358209/100000000000000 : ℝ), (12306545375983/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3257863801/10000000000 : ℝ)|^5 ≤ (12306545437367/50000000000000 : ℝ)^4
        have hw : |(3257863801/10000000000 : ℝ)|=(3257863801/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5814493107/10000000000 : ℝ)|^5 ≤ (50773818358209/100000000000000 : ℝ)^4
        have hw : |(5814493107/10000000000 : ℝ)|=(5814493107/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(814465947/2500000000 : ℝ)|^5 ≤ (12306545375983/50000000000000 : ℝ)^4
        have hw : |(814465947/2500000000 : ℝ)|=(814465947/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c318024_s0_6 (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ)) (x : Fin 3 → ℝ) :
    (3257863801/10000000000 : ℝ)*x 0 + (5814493107/10000000000 : ℝ)*x 1 + (-814465947/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3257863801/10000000000 : ℝ)^5 ≤ (12306545437367/50000000000000 : ℝ)^4 := by
    have hnat : (3257863801 : ℕ)^5*50000000000000^4 ≤ 12306545437367^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3257863801 10000000000 12306545437367 50000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5814493107/10000000000 : ℝ)^5 ≤ (50773818358209/100000000000000 : ℝ)^4 := by
    have hnat : (5814493107 : ℕ)^5*100000000000000^4 ≤ 50773818358209^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5814493107 10000000000 50773818358209 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (814465947/2500000000 : ℝ)^5 ≤ (12306545375983/50000000000000 : ℝ)^4 := by
    have hnat : (814465947 : ℕ)^5*50000000000000^4 ≤ 12306545375983^4*2500000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      814465947 2500000000 12306545375983 50000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5 : ℝ)) 5 4 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3257863801/10000000000 : ℝ), (5814493107/10000000000 : ℝ), (-814465947/2500000000 : ℝ)] ![(12306545437367/50000000000000 : ℝ), (50773818358209/100000000000000 : ℝ), (12306545375983/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3257863801/10000000000 : ℝ)|^5 ≤ (12306545437367/50000000000000 : ℝ)^4
        have hw : |(3257863801/10000000000 : ℝ)|=(3257863801/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5814493107/10000000000 : ℝ)|^5 ≤ (50773818358209/100000000000000 : ℝ)^4
        have hw : |(5814493107/10000000000 : ℝ)|=(5814493107/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-814465947/2500000000 : ℝ)|^5 ≤ (12306545375983/50000000000000 : ℝ)^4
        have hw : |(-814465947/2500000000 : ℝ)|=(814465947/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c318024 (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (7299/4000 : ℝ) (34269/20000 : ℝ) (39911/50000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![false, false, false]]) : False := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (39911/50000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (39911/50000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (39911/50000 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (39911/50000 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((-1 : ℝ)*(X 0 0+X 2 0)) ∧ ((-1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((-1 : ℝ)*pair X 1 0) ∧ ((-1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (39911/50000 : ℝ)*P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (39911/50000 : ℝ)*P 2 ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((-1 : ℝ)*(X 0 1+X 1 1)) ∧ ((-1 : ℝ)*(X 0 1+X 1 1)) ≤ ((-1 : ℝ)*(X 0 0+X 1 0)) ∧ ((-1 : ℝ)*(X 0 0+X 1 0)) ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((-1 : ℝ)*pair X 2 1) ∧ ((-1 : ℝ)*pair X 2 1) ≤ ((-1 : ℝ)*pair X 2 0) ∧ ((-1 : ℝ)*pair X 2 0) ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base5 : ((1 : ℝ)*N 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 2]
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base49 : ((-1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.1]
  have base50 : ((1 : ℝ)*X 0 0+(1 : ℝ)*X 0 2+(1 : ℝ)*X 2 0+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.2.1]
  have base54 : ((-1 : ℝ)*N 2+(1 : ℝ)*P 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ptotal 2]
  have base59 : ((1 : ℝ)*X 0 1+(1 : ℝ)*X 1 1) ≤ (0 : ℝ) := by
    linarith only [order2.1]
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
  have s0_pow0 : (1 : ℝ) ^ (39/8 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^39 ≤ (1 : ℝ)^8 := by
      have hnat : (1 : ℕ)^39*1^8 ≤ 1^8*1^39 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 39 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 39 8 (by norm_num) hpowers
    exact h
  have s0_corner0a : (2 : ℝ) ≤ (5763943924246341/5000000000000000 : ℝ) ^ (39/8 : ℝ) := by
    have hpowers : (2 : ℝ)^8 ≤ (5763943924246341/5000000000000000 : ℝ)^39 := by
      have hnat : (2 : ℕ)^8*5000000000000000^39 ≤ 5763943924246341^39*1^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 5763943924246341 5000000000000000 8 39 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5763943924246341/5000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 39 8 (by norm_num) hpowers
    exact h
  have s0_corner0b : (3 : ℝ) ≤ (782980676308869/625000000000000 : ℝ) ^ (39/8 : ℝ) := by
    have hpowers : (3 : ℝ)^8 ≤ (782980676308869/625000000000000 : ℝ)^39 := by
      have hnat : (3 : ℕ)^8*625000000000000^39 ≤ 782980676308869^39*1^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 782980676308869 625000000000000 8 39 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (782980676308869/625000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 39 8 (by norm_num) hpowers
    exact h
  have major_s0_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(763943924246341/5000000000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(499901486224611/5000000000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (39/8 : ℝ)) (rho := (1 : ℝ)) (alpha := (763943924246341/5000000000000000 : ℝ)) (beta := (499901486224611/5000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow0,s0_corner0a]) (by linarith only [s0_pow0,s0_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![false, false, false]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (1 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order0.2.2])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(763943924246341/5000000000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(499901486224611/5000000000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow1 : (1 : ℝ) ^ (39/8 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^39 ≤ (1 : ℝ)^8 := by
      have hnat : (1 : ℕ)^39*1^8 ≤ 1^8*1^39 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 39 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 39 8 (by norm_num) hpowers
    exact h
  have s0_corner1a : (2 : ℝ) ≤ (5763943924246341/5000000000000000 : ℝ) ^ (39/8 : ℝ) := by
    have hpowers : (2 : ℝ)^8 ≤ (5763943924246341/5000000000000000 : ℝ)^39 := by
      have hnat : (2 : ℕ)^8*5000000000000000^39 ≤ 5763943924246341^39*1^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 5763943924246341 5000000000000000 8 39 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5763943924246341/5000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 39 8 (by norm_num) hpowers
    exact h
  have s0_corner1b : (3 : ℝ) ≤ (782980676308869/625000000000000 : ℝ) ^ (39/8 : ℝ) := by
    have hpowers : (3 : ℝ)^8 ≤ (782980676308869/625000000000000 : ℝ)^39 := by
      have hnat : (3 : ℕ)^8*625000000000000^39 ≤ 782980676308869^39*1^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 782980676308869 625000000000000 8 39 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (782980676308869/625000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 39 8 (by norm_num) hpowers
    exact h
  have major_s0_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(763943924246341/5000000000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 2 0))+(499901486224611/5000000000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (39/8 : ℝ)) (rho := (1 : ℝ)) (alpha := (763943924246341/5000000000000000 : ℝ)) (beta := (499901486224611/5000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow1,s0_corner1a]) (by linarith only [s0_pow1,s0_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![false, false, false]] hX 1 (by
        change ((-1 : ℝ)*pair X 1 0) ≤ (1 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order1.2.2])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(763943924246341/5000000000000000 : ℝ)*((-1 : ℝ)*pair X 1 0)+(499901486224611/5000000000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow2 : (1 : ℝ) ^ (39/8 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^39 ≤ (1 : ℝ)^8 := by
      have hnat : (1 : ℕ)^39*1^8 ≤ 1^8*1^39 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 39 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 39 8 (by norm_num) hpowers
    exact h
  have s0_corner2a : (2 : ℝ) ≤ (5763943924246341/5000000000000000 : ℝ) ^ (39/8 : ℝ) := by
    have hpowers : (2 : ℝ)^8 ≤ (5763943924246341/5000000000000000 : ℝ)^39 := by
      have hnat : (2 : ℕ)^8*5000000000000000^39 ≤ 5763943924246341^39*1^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 5763943924246341 5000000000000000 8 39 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5763943924246341/5000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 39 8 (by norm_num) hpowers
    exact h
  have s0_corner2b : (3 : ℝ) ≤ (782980676308869/625000000000000 : ℝ) ^ (39/8 : ℝ) := by
    have hpowers : (3 : ℝ)^8 ≤ (782980676308869/625000000000000 : ℝ)^39 := by
      have hnat : (3 : ℕ)^8*625000000000000^39 ≤ 782980676308869^39*1^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 782980676308869 625000000000000 8 39 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (782980676308869/625000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 39 8 (by norm_num) hpowers
    exact h
  have major_s0_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(763943924246341/5000000000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 1 0))+(499901486224611/5000000000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (39/8 : ℝ)) (rho := (1 : ℝ)) (alpha := (763943924246341/5000000000000000 : ℝ)) (beta := (499901486224611/5000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow2,s0_corner2a]) (by linarith only [s0_pow2,s0_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![false, false, false]] hX 2 (by
        change ((-1 : ℝ)*pair X 2 0) ≤ (1 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order2.2.2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(763943924246341/5000000000000000 : ℝ)*((-1 : ℝ)*pair X 2 0)+(499901486224611/5000000000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s0_0 : ((-4719430299/10000000000 : ℝ)*X 0 0+(590558823/2000000000 : ℝ)*X 0 1+(-117985757/250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c318024_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_1 : ((4719430299/10000000000 : ℝ)*X 1 0+(-590558823/2000000000 : ℝ)*X 1 1+(-117985757/250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c318024_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_2 : ((3257863801/10000000000 : ℝ)*X 2 0+(5814493107/10000000000 : ℝ)*X 2 1+(814465947/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c318024_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_6 : ((3257863801/10000000000 : ℝ)*X 0 0+(5814493107/10000000000 : ℝ)*X 0 1+(-814465947/2500000000 : ℝ)*X 0 2+(3257863801/10000000000 : ℝ)*X 1 0+(5814493107/10000000000 : ℝ)*X 1 1+(-814465947/2500000000 : ℝ)*X 1 2+(3257863801/10000000000 : ℝ)*X 2 0+(5814493107/10000000000 : ℝ)*X 2 1+(-814465947/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c318024_s0_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have hsep : (-15897/2000 : ℝ) < ((-7299/4000 : ℝ)*P 0+(-7299/4000 : ℝ)*P 1+(-7299/4000 : ℝ)*P 2+(1 : ℝ)*T) := by
    have hcertificate_margin : (-15897/2000 : ℝ) < (-3926658826576908560958700347/500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2344666493/50000000000 : ℝ)*(base5) + (96362285807/1000000000000 : ℝ)*(base39) + (463689946889/1000000000000 : ℝ)*(base49) + (183663829013/500000000000 : ℝ)*(base50) + (2983/500000000000 : ℝ)*(base54) + (315153408667/1000000000000 : ℝ)*(base59) + (364950001069/200000000000 : ℝ)*(major_s0_0) + (7299/4000 : ℝ)*(major_s0_1) + (91237499901/50000000000 : ℝ)*(major_s0_2) + (2617772527041/1000000000000 : ℝ)*(sp_s0_0) + (2617772532387/1000000000000 : ℝ)*(sp_s0_1) + (532933170459/200000000000 : ℝ)*(sp_s0_2) + (476553332087/500000000000 : ℝ)*(sp_s0_6) + (163610782691/62500000000 : ℝ)*(f.sum) + (151774227487241/250000000000000000000000000 : ℝ)*base62 + (51550715411489/250000000000000000000000000 : ℝ)*base65 + (2479105727/2500000000000000000000 : ℝ)*base66 + (82707464287241/250000000000000000000000000 : ℝ)*base68 + (39354490596897/200000000000000000000000000 : ℝ)*base71 + (410474171309159/1000000000000000000000000000 : ℝ)*base73 + (4052918169/10000000000000000000000 : ℝ)*base74 + (53755051038529/1000000000000000000000000000 : ℝ)*base77 + (70308560690841/1000000000000000000000000000 : ℝ)*base78 + (797/200000000000 : ℝ)*base81 + (9331/1000000000000 : ℝ)*base83 + (1069/200000000000 : ℝ)*base85 + (1069/200000000000 : ℝ)*base86 + (1993/500000000000 : ℝ)*base90 + hcertificate_margin
  linarith only [hsep,f.failure]

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
namespace HlawkaSchatten.DiagonalCutoff4
theorem wide_coarse_distinct_p018_b010 (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ))
    (c : Fin 88) (hlo : 22 ≤ c.val) (hhi : c.val < 25)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (7299/4000 : ℝ) (34269/20000 : ℝ) (39911/50000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  have hc : c=22 ∨ c=23 ∨ c=24 := by omega
  rcases hc with rfl|rfl|rfl
  · exact collision_c318022 p hpa (by linarith only [hpb]) X hX
  · exact collision_c318023 p hpa (by linarith only [hpb]) X hX
  · exact collision_c318024 p hpa (by linarith only [hpb]) X hX

end HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ))
    (c : Fin 88) (hlo : 22 ≤ c.val) (hhi : c.val < 25)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (7299/4000 : ℝ) (34269/20000 : ℝ) (39911/50000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  exact HlawkaSchatten.DiagonalCutoff4.wide_coarse_distinct_p018_b010 p hpa hpb c hlo hhi hn63 hn87 X hX

#print axioms solution
