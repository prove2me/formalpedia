-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.wide_coarse_distinct_p016_b021
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T01:10:35.322414+00:00
-- url     : https://prove2.me/submissions/d9ffaa57-61a6-48bf-b886-f9ed09d27777

import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c316045_s0
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c316045_s1
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c316045_s2
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
theorem HlawkaSchatten.DiagonalCutoff4.collision_c316045 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (177257/100000 : ℝ) (173433/100000 : ℝ) (1587/2000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, false, true]]) : False := by
  have h0 := collision_c316045_s0 p hpa hpb X hX
  have h1 := collision_c316045_s1 p hpa hpb X hX h0
  exact collision_c316045_s2 p hpa hpb X hX h1

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
theorem collision_support_c316044_s0_0 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-768119813/10000000000 : ℝ)*x 0 + (-103202217/156250000 : ℝ)*x 1 + (-2253617547/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (768119813/10000000000 : ℝ)^39 ≤ (3960935161881/100000000000000 : ℝ)^31 := by
    have hnat : (768119813 : ℕ)^39*100000000000000^31 ≤ 3960935161881^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      768119813 10000000000 3960935161881 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (103202217/156250000 : ℝ)^39 ≤ (11868984904343/20000000000000 : ℝ)^31 := by
    have hnat : (103202217 : ℕ)^39*20000000000000^31 ≤ 11868984904343^31*156250000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      103202217 156250000 11868984904343 20000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2253617547/5000000000 : ℝ)^39 ≤ (36694140307031/100000000000000 : ℝ)^31 := by
    have hnat : (2253617547 : ℕ)^39*100000000000000^31 ≤ 36694140307031^31*5000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2253617547 5000000000 36694140307031 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-768119813/10000000000 : ℝ), (-103202217/156250000 : ℝ), (-2253617547/5000000000 : ℝ)] ![(3960935161881/100000000000000 : ℝ), (11868984904343/20000000000000 : ℝ), (36694140307031/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-768119813/10000000000 : ℝ)|^39 ≤ (3960935161881/100000000000000 : ℝ)^31
        have hw : |(-768119813/10000000000 : ℝ)|=(768119813/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-103202217/156250000 : ℝ)|^39 ≤ (11868984904343/20000000000000 : ℝ)^31
        have hw : |(-103202217/156250000 : ℝ)|=(103202217/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2253617547/5000000000 : ℝ)|^39 ≤ (36694140307031/100000000000000 : ℝ)^31
        have hw : |(-2253617547/5000000000 : ℝ)|=(2253617547/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316044_s0_2 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (2528498091/5000000000 : ℝ)*x 0 + (-3099151517/10000000000 : ℝ)*x 1 + (2154872889/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2528498091/5000000000 : ℝ)^39 ≤ (42410932302241/100000000000000 : ℝ)^31 := by
    have hnat : (2528498091 : ℕ)^39*100000000000000^31 ≤ 42410932302241^31*5000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2528498091 5000000000 42410932302241 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3099151517/10000000000 : ℝ)^39 ≤ (1431629531707/6250000000000 : ℝ)^31 := by
    have hnat : (3099151517 : ℕ)^39*6250000000000^31 ≤ 1431629531707^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3099151517 10000000000 1431629531707 6250000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2154872889/5000000000 : ℝ)^39 ≤ (346829951809/1000000000000 : ℝ)^31 := by
    have hnat : (2154872889 : ℕ)^39*1000000000000^31 ≤ 346829951809^31*5000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2154872889 5000000000 346829951809 1000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2528498091/5000000000 : ℝ), (-3099151517/10000000000 : ℝ), (2154872889/5000000000 : ℝ)] ![(42410932302241/100000000000000 : ℝ), (1431629531707/6250000000000 : ℝ), (346829951809/1000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2528498091/5000000000 : ℝ)|^39 ≤ (42410932302241/100000000000000 : ℝ)^31
        have hw : |(2528498091/5000000000 : ℝ)|=(2528498091/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3099151517/10000000000 : ℝ)|^39 ≤ (1431629531707/6250000000000 : ℝ)^31
        have hw : |(-3099151517/10000000000 : ℝ)|=(3099151517/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2154872889/5000000000 : ℝ)|^39 ≤ (346829951809/1000000000000 : ℝ)^31
        have hw : |(2154872889/5000000000 : ℝ)|=(2154872889/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316044_s0_6 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (7539924467/10000000000 : ℝ)*x 0 + (-653105311/2500000000 : ℝ)*x 1 + (-356545051/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (7539924467/10000000000 : ℝ)^39 ≤ (70100282509207/100000000000000 : ℝ)^31 := by
    have hnat : (7539924467 : ℕ)^39*100000000000000^31 ≤ 70100282509207^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7539924467 10000000000 70100282509207 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (653105311/2500000000 : ℝ)^39 ≤ (3695155674341/20000000000000 : ℝ)^31 := by
    have hnat : (653105311 : ℕ)^39*20000000000000^31 ≤ 3695155674341^31*2500000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      653105311 2500000000 3695155674341 20000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (356545051/2000000000 : ℝ)^39 ≤ (2855984776023/25000000000000 : ℝ)^31 := by
    have hnat : (356545051 : ℕ)^39*25000000000000^31 ≤ 2855984776023^31*2000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      356545051 2000000000 2855984776023 25000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(7539924467/10000000000 : ℝ), (-653105311/2500000000 : ℝ), (-356545051/2000000000 : ℝ)] ![(70100282509207/100000000000000 : ℝ), (3695155674341/20000000000000 : ℝ), (2855984776023/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(7539924467/10000000000 : ℝ)|^39 ≤ (70100282509207/100000000000000 : ℝ)^31
        have hw : |(7539924467/10000000000 : ℝ)|=(7539924467/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-653105311/2500000000 : ℝ)|^39 ≤ (3695155674341/20000000000000 : ℝ)^31
        have hw : |(-653105311/2500000000 : ℝ)|=(653105311/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-356545051/2000000000 : ℝ)|^39 ≤ (2855984776023/25000000000000 : ℝ)^31
        have hw : |(-356545051/2000000000 : ℝ)|=(356545051/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316044_s0_7 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-51708217/625000000 : ℝ)*x 0 + (-6854041689/10000000000 : ℝ)*x 1 + (-838038443/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (51708217/625000000 : ℝ)^39 ≤ (4348816080611/100000000000000 : ℝ)^31 := by
    have hnat : (51708217 : ℕ)^39*100000000000000^31 ≤ 4348816080611^31*625000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      51708217 625000000 4348816080611 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6854041689/10000000000 : ℝ)^39 ≤ (7771778776591/12500000000000 : ℝ)^31 := by
    have hnat : (6854041689 : ℕ)^39*12500000000000^31 ≤ 7771778776591^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6854041689 10000000000 7771778776591 12500000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (838038443/2000000000 : ℝ)^39 ≤ (8369238424147/25000000000000 : ℝ)^31 := by
    have hnat : (838038443 : ℕ)^39*25000000000000^31 ≤ 8369238424147^31*2000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      838038443 2000000000 8369238424147 25000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-51708217/625000000 : ℝ), (-6854041689/10000000000 : ℝ), (-838038443/2000000000 : ℝ)] ![(4348816080611/100000000000000 : ℝ), (7771778776591/12500000000000 : ℝ), (8369238424147/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-51708217/625000000 : ℝ)|^39 ≤ (4348816080611/100000000000000 : ℝ)^31
        have hw : |(-51708217/625000000 : ℝ)|=(51708217/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-6854041689/10000000000 : ℝ)|^39 ≤ (7771778776591/12500000000000 : ℝ)^31
        have hw : |(-6854041689/10000000000 : ℝ)|=(6854041689/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-838038443/2000000000 : ℝ)|^39 ≤ (8369238424147/25000000000000 : ℝ)^31
        have hw : |(-838038443/2000000000 : ℝ)|=(838038443/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316044_s0_8 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (1219671699/2500000000 : ℝ)*x 0 + (3672210817/10000000000 : ℝ)*x 1 + (-988118679/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1219671699/2500000000 : ℝ)^39 ≤ (40538249051781/100000000000000 : ℝ)^31 := by
    have hnat : (1219671699 : ℕ)^39*100000000000000^31 ≤ 40538249051781^31*2500000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1219671699 2500000000 40538249051781 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3672210817/10000000000 : ℝ)^39 ≤ (5671276926477/20000000000000 : ℝ)^31 := by
    have hnat : (3672210817 : ℕ)^39*20000000000000^31 ≤ 5671276926477^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3672210817 10000000000 5671276926477 20000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (988118679/2500000000 : ℝ)^39 ≤ (31105366292081/100000000000000 : ℝ)^31 := by
    have hnat : (988118679 : ℕ)^39*100000000000000^31 ≤ 31105366292081^31*2500000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      988118679 2500000000 31105366292081 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1219671699/2500000000 : ℝ), (3672210817/10000000000 : ℝ), (-988118679/2500000000 : ℝ)] ![(40538249051781/100000000000000 : ℝ), (5671276926477/20000000000000 : ℝ), (31105366292081/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1219671699/2500000000 : ℝ)|^39 ≤ (40538249051781/100000000000000 : ℝ)^31
        have hw : |(1219671699/2500000000 : ℝ)|=(1219671699/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3672210817/10000000000 : ℝ)|^39 ≤ (5671276926477/20000000000000 : ℝ)^31
        have hw : |(3672210817/10000000000 : ℝ)|=(3672210817/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-988118679/2500000000 : ℝ)|^39 ≤ (31105366292081/100000000000000 : ℝ)^31
        have hw : |(-988118679/2500000000 : ℝ)|=(988118679/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316044_s0_9 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (2439343419/5000000000 : ℝ)*x 0 + (-5027739/19531250 : ℝ)*x 1 + (4953835371/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2439343419/5000000000 : ℝ)^39 ≤ (40538249490831/100000000000000 : ℝ)^31 := by
    have hnat : (2439343419 : ℕ)^39*100000000000000^31 ≤ 40538249490831^31*5000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2439343419 5000000000 40538249490831 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5027739/19531250 : ℝ)^39 ≤ (3627274902287/20000000000000 : ℝ)^31 := by
    have hnat : (5027739 : ℕ)^39*20000000000000^31 ≤ 3627274902287^31*19531250^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5027739 19531250 3627274902287 20000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4953835371/10000000000 : ℝ)^39 ≤ (5165671998129/12500000000000 : ℝ)^31 := by
    have hnat : (4953835371 : ℕ)^39*12500000000000^31 ≤ 5165671998129^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4953835371 10000000000 5165671998129 12500000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2439343419/5000000000 : ℝ), (-5027739/19531250 : ℝ), (4953835371/10000000000 : ℝ)] ![(40538249490831/100000000000000 : ℝ), (3627274902287/20000000000000 : ℝ), (5165671998129/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2439343419/5000000000 : ℝ)|^39 ≤ (40538249490831/100000000000000 : ℝ)^31
        have hw : |(2439343419/5000000000 : ℝ)|=(2439343419/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-5027739/19531250 : ℝ)|^39 ≤ (3627274902287/20000000000000 : ℝ)^31
        have hw : |(-5027739/19531250 : ℝ)|=(5027739/19531250 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4953835371/10000000000 : ℝ)|^39 ≤ (5165671998129/12500000000000 : ℝ)^31
        have hw : |(4953835371/10000000000 : ℝ)|=(4953835371/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316044_s0_13 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (3837726099/5000000000 : ℝ)*x 0 + (-2108907581/10000000000 : ℝ)*x 1 + (-1059484721/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3837726099/5000000000 : ℝ)^39 ≤ (71689142099609/100000000000000 : ℝ)^31 := by
    have hnat : (3837726099 : ℕ)^39*100000000000000^31 ≤ 71689142099609^31*5000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3837726099 5000000000 71689142099609 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2108907581/10000000000 : ℝ)^39 ≤ (7056523473133/50000000000000 : ℝ)^31 := by
    have hnat : (2108907581 : ℕ)^39*50000000000000^31 ≤ 7056523473133^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2108907581 10000000000 7056523473133 50000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1059484721/5000000000 : ℝ)^39 ≤ (7098905472099/50000000000000 : ℝ)^31 := by
    have hnat : (1059484721 : ℕ)^39*50000000000000^31 ≤ 7098905472099^31*5000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1059484721 5000000000 7098905472099 50000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3837726099/5000000000 : ℝ), (-2108907581/10000000000 : ℝ), (-1059484721/5000000000 : ℝ)] ![(71689142099609/100000000000000 : ℝ), (7056523473133/50000000000000 : ℝ), (7098905472099/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3837726099/5000000000 : ℝ)|^39 ≤ (71689142099609/100000000000000 : ℝ)^31
        have hw : |(3837726099/5000000000 : ℝ)|=(3837726099/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2108907581/10000000000 : ℝ)|^39 ≤ (7056523473133/50000000000000 : ℝ)^31
        have hw : |(-2108907581/10000000000 : ℝ)|=(2108907581/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1059484721/5000000000 : ℝ)|^39 ≤ (7098905472099/50000000000000 : ℝ)^31
        have hw : |(-1059484721/5000000000 : ℝ)|=(1059484721/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316044_s0_14 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-11894167/2000000000 : ℝ)*x 0 + (-832177719/1250000000 : ℝ)*x 1 + (-481779997/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (11894167/2000000000 : ℝ)^39 ≤ (9904006157/6250000000000 : ℝ)^31 := by
    have hnat : (11894167 : ℕ)^39*6250000000000^31 ≤ 9904006157^31*2000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      11894167 2000000000 9904006157 6250000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (832177719/1250000000 : ℝ)^39 ≤ (1498468596897/2500000000000 : ℝ)^31 := by
    have hnat : (832177719 : ℕ)^39*2500000000000^31 ≤ 1498468596897^31*1250000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      832177719 1250000000 1498468596897 2500000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (481779997/1000000000 : ℝ)^39 ≤ (39902792011551/100000000000000 : ℝ)^31 := by
    have hnat : (481779997 : ℕ)^39*100000000000000^31 ≤ 39902792011551^31*1000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      481779997 1000000000 39902792011551 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-11894167/2000000000 : ℝ), (-832177719/1250000000 : ℝ), (-481779997/1000000000 : ℝ)] ![(9904006157/6250000000000 : ℝ), (1498468596897/2500000000000 : ℝ), (39902792011551/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-11894167/2000000000 : ℝ)|^39 ≤ (9904006157/6250000000000 : ℝ)^31
        have hw : |(-11894167/2000000000 : ℝ)|=(11894167/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-832177719/1250000000 : ℝ)|^39 ≤ (1498468596897/2500000000000 : ℝ)^31
        have hw : |(-832177719/1250000000 : ℝ)|=(832177719/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-481779997/1000000000 : ℝ)|^39 ≤ (39902792011551/100000000000000 : ℝ)^31
        have hw : |(-481779997/1000000000 : ℝ)|=(481779997/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316044_s0_15 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (4553457887/10000000000 : ℝ)*x 0 + (629444497/2000000000 : ℝ)*x 1 + (-4776974473/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4553457887/10000000000 : ℝ)^39 ≤ (4646023011577/12500000000000 : ℝ)^31 := by
    have hnat : (4553457887 : ℕ)^39*12500000000000^31 ≤ 4646023011577^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4553457887 10000000000 4646023011577 12500000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (629444497/2000000000 : ℝ)^39 ≤ (2335394937721/10000000000000 : ℝ)^31 := by
    have hnat : (629444497 : ℕ)^39*10000000000000^31 ≤ 2335394937721^31*2000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      629444497 2000000000 2335394937721 10000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4776974473/10000000000 : ℝ)^39 ≤ (19738933255793/50000000000000 : ℝ)^31 := by
    have hnat : (4776974473 : ℕ)^39*50000000000000^31 ≤ 19738933255793^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4776974473 10000000000 19738933255793 50000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4553457887/10000000000 : ℝ), (629444497/2000000000 : ℝ), (-4776974473/10000000000 : ℝ)] ![(4646023011577/12500000000000 : ℝ), (2335394937721/10000000000000 : ℝ), (19738933255793/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4553457887/10000000000 : ℝ)|^39 ≤ (4646023011577/12500000000000 : ℝ)^31
        have hw : |(4553457887/10000000000 : ℝ)|=(4553457887/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(629444497/2000000000 : ℝ)|^39 ≤ (2335394937721/10000000000000 : ℝ)^31
        have hw : |(629444497/2000000000 : ℝ)|=(629444497/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-4776974473/10000000000 : ℝ)|^39 ≤ (19738933255793/50000000000000 : ℝ)^31
        have hw : |(-4776974473/10000000000 : ℝ)|=(4776974473/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316044_s0_16 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (5810859061/10000000000 : ℝ)*x 0 + (-20337693/78125000 : ℝ)*x 1 + (3951273867/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5810859061/10000000000 : ℝ)^39 ≤ (12628133039697/25000000000000 : ℝ)^31 := by
    have hnat : (5810859061 : ℕ)^39*25000000000000^31 ≤ 12628133039697^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5810859061 10000000000 12628133039697 25000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (20337693/78125000 : ℝ)^39 ≤ (4598497600551/25000000000000 : ℝ)^31 := by
    have hnat : (20337693 : ℕ)^39*25000000000000^31 ≤ 4598497600551^31*78125000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      20337693 78125000 4598497600551 25000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3951273867/10000000000 : ℝ)^39 ≤ (31093477424053/100000000000000 : ℝ)^31 := by
    have hnat : (3951273867 : ℕ)^39*100000000000000^31 ≤ 31093477424053^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3951273867 10000000000 31093477424053 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5810859061/10000000000 : ℝ), (-20337693/78125000 : ℝ), (3951273867/10000000000 : ℝ)] ![(12628133039697/25000000000000 : ℝ), (4598497600551/25000000000000 : ℝ), (31093477424053/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5810859061/10000000000 : ℝ)|^39 ≤ (12628133039697/25000000000000 : ℝ)^31
        have hw : |(5810859061/10000000000 : ℝ)|=(5810859061/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-20337693/78125000 : ℝ)|^39 ≤ (4598497600551/25000000000000 : ℝ)^31
        have hw : |(-20337693/78125000 : ℝ)|=(20337693/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3951273867/10000000000 : ℝ)|^39 ≤ (31093477424053/100000000000000 : ℝ)^31
        have hw : |(3951273867/10000000000 : ℝ)|=(3951273867/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316044_s0_19 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (1784280413/2000000000 : ℝ)*x 0 + (-84189381/625000000 : ℝ)*x 1 + (-487405019/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1784280413/2000000000 : ℝ)^39 ≤ (86624682830787/100000000000000 : ℝ)^31 := by
    have hnat : (1784280413 : ℕ)^39*100000000000000^31 ≤ 86624682830787^31*2000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1784280413 2000000000 86624682830787 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (84189381/625000000 : ℝ)^39 ≤ (8029721322003/100000000000000 : ℝ)^31 := by
    have hnat : (84189381 : ℕ)^39*100000000000000^31 ≤ 8029721322003^31*625000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      84189381 625000000 8029721322003 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (487405019/5000000000 : ℝ)^39 ≤ (5345595833181/100000000000000 : ℝ)^31 := by
    have hnat : (487405019 : ℕ)^39*100000000000000^31 ≤ 5345595833181^31*5000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      487405019 5000000000 5345595833181 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1784280413/2000000000 : ℝ), (-84189381/625000000 : ℝ), (-487405019/5000000000 : ℝ)] ![(86624682830787/100000000000000 : ℝ), (8029721322003/100000000000000 : ℝ), (5345595833181/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1784280413/2000000000 : ℝ)|^39 ≤ (86624682830787/100000000000000 : ℝ)^31
        have hw : |(1784280413/2000000000 : ℝ)|=(1784280413/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-84189381/625000000 : ℝ)|^39 ≤ (8029721322003/100000000000000 : ℝ)^31
        have hw : |(-84189381/625000000 : ℝ)|=(84189381/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-487405019/5000000000 : ℝ)|^39 ≤ (5345595833181/100000000000000 : ℝ)^31
        have hw : |(-487405019/5000000000 : ℝ)|=(487405019/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316044_s0_20 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-2142887/400000000 : ℝ)*x 0 + (-3549657111/5000000000 : ℝ)*x 1 + (-4328692401/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2142887/400000000 : ℝ)^39 ≤ (138950173289/100000000000000 : ℝ)^31 := by
    have hnat : (2142887 : ℕ)^39*100000000000000^31 ≤ 138950173289^31*400000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2142887 400000000 138950173289 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3549657111/5000000000 : ℝ)^39 ≤ (64986123391057/100000000000000 : ℝ)^31 := by
    have hnat : (3549657111 : ℕ)^39*100000000000000^31 ≤ 64986123391057^31*5000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3549657111 5000000000 64986123391057 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4328692401/10000000000 : ℝ)^39 ≤ (34874926429341/100000000000000 : ℝ)^31 := by
    have hnat : (4328692401 : ℕ)^39*100000000000000^31 ≤ 34874926429341^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4328692401 10000000000 34874926429341 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2142887/400000000 : ℝ), (-3549657111/5000000000 : ℝ), (-4328692401/10000000000 : ℝ)] ![(138950173289/100000000000000 : ℝ), (64986123391057/100000000000000 : ℝ), (34874926429341/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2142887/400000000 : ℝ)|^39 ≤ (138950173289/100000000000000 : ℝ)^31
        have hw : |(-2142887/400000000 : ℝ)|=(2142887/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3549657111/5000000000 : ℝ)|^39 ≤ (64986123391057/100000000000000 : ℝ)^31
        have hw : |(-3549657111/5000000000 : ℝ)|=(3549657111/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-4328692401/10000000000 : ℝ)|^39 ≤ (34874926429341/100000000000000 : ℝ)^31
        have hw : |(-4328692401/10000000000 : ℝ)|=(4328692401/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316044_s0_21 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (2908378851/5000000000 : ℝ)*x 0 + (2829839267/10000000000 : ℝ)*x 1 + (-3737527327/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2908378851/5000000000 : ℝ)^39 ≤ (12644262155183/25000000000000 : ℝ)^31 := by
    have hnat : (2908378851 : ℕ)^39*25000000000000^31 ≤ 12644262155183^31*5000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2908378851 5000000000 12644262155183 25000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2829839267/10000000000 : ℝ)^39 ≤ (20430591231919/100000000000000 : ℝ)^31 := by
    have hnat : (2829839267 : ℕ)^39*100000000000000^31 ≤ 20430591231919^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2829839267 10000000000 20430591231919 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3737527327/10000000000 : ℝ)^39 ≤ (28992360132821/100000000000000 : ℝ)^31 := by
    have hnat : (3737527327 : ℕ)^39*100000000000000^31 ≤ 28992360132821^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3737527327 10000000000 28992360132821 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2908378851/5000000000 : ℝ), (2829839267/10000000000 : ℝ), (-3737527327/10000000000 : ℝ)] ![(12644262155183/25000000000000 : ℝ), (20430591231919/100000000000000 : ℝ), (28992360132821/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2908378851/5000000000 : ℝ)|^39 ≤ (12644262155183/25000000000000 : ℝ)^31
        have hw : |(2908378851/5000000000 : ℝ)|=(2908378851/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2829839267/10000000000 : ℝ)|^39 ≤ (20430591231919/100000000000000 : ℝ)^31
        have hw : |(2829839267/10000000000 : ℝ)|=(2829839267/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3737527327/10000000000 : ℝ)|^39 ≤ (28992360132821/100000000000000 : ℝ)^31
        have hw : |(-3737527327/10000000000 : ℝ)|=(3737527327/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316044_s0_22 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (2285901191/5000000000 : ℝ)*x 0 + (-341657377/1000000000 : ℝ)*x 1 + (4512460469/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2285901191/5000000000 : ℝ)^39 ≤ (37356663613883/100000000000000 : ℝ)^31 := by
    have hnat : (2285901191 : ℕ)^39*100000000000000^31 ≤ 37356663613883^31*5000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2285901191 5000000000 37356663613883 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (341657377/1000000000 : ℝ)^39 ≤ (25895669191053/100000000000000 : ℝ)^31 := by
    have hnat : (341657377 : ℕ)^39*100000000000000^31 ≤ 25895669191053^31*1000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      341657377 1000000000 25895669191053 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4512460469/10000000000 : ℝ)^39 ≤ (36747667174181/100000000000000 : ℝ)^31 := by
    have hnat : (4512460469 : ℕ)^39*100000000000000^31 ≤ 36747667174181^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4512460469 10000000000 36747667174181 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2285901191/5000000000 : ℝ), (-341657377/1000000000 : ℝ), (4512460469/10000000000 : ℝ)] ![(37356663613883/100000000000000 : ℝ), (25895669191053/100000000000000 : ℝ), (36747667174181/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2285901191/5000000000 : ℝ)|^39 ≤ (37356663613883/100000000000000 : ℝ)^31
        have hw : |(2285901191/5000000000 : ℝ)|=(2285901191/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-341657377/1000000000 : ℝ)|^39 ≤ (25895669191053/100000000000000 : ℝ)^31
        have hw : |(-341657377/1000000000 : ℝ)|=(341657377/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4512460469/10000000000 : ℝ)|^39 ≤ (36747667174181/100000000000000 : ℝ)^31
        have hw : |(4512460469/10000000000 : ℝ)|=(4512460469/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316044_s0_25 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (8874712171/10000000000 : ℝ)*x 0 + (-1484655017/10000000000 : ℝ)*x 1 + (-905244463/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (8874712171/10000000000 : ℝ)^39 ≤ (43027363898739/50000000000000 : ℝ)^31 := by
    have hnat : (8874712171 : ℕ)^39*50000000000000^31 ≤ 43027363898739^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8874712171 10000000000 43027363898739 50000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1484655017/10000000000 : ℝ)^39 ≤ (14520162653/160000000000 : ℝ)^31 := by
    have hnat : (1484655017 : ℕ)^39*160000000000^31 ≤ 14520162653^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1484655017 10000000000 14520162653 160000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (905244463/10000000000 : ℝ)^39 ≤ (121754263131/2500000000000 : ℝ)^31 := by
    have hnat : (905244463 : ℕ)^39*2500000000000^31 ≤ 121754263131^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      905244463 10000000000 121754263131 2500000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(8874712171/10000000000 : ℝ), (-1484655017/10000000000 : ℝ), (-905244463/10000000000 : ℝ)] ![(43027363898739/50000000000000 : ℝ), (14520162653/160000000000 : ℝ), (121754263131/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(8874712171/10000000000 : ℝ)|^39 ≤ (43027363898739/50000000000000 : ℝ)^31
        have hw : |(8874712171/10000000000 : ℝ)|=(8874712171/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1484655017/10000000000 : ℝ)|^39 ≤ (14520162653/160000000000 : ℝ)^31
        have hw : |(-1484655017/10000000000 : ℝ)|=(1484655017/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-905244463/10000000000 : ℝ)|^39 ≤ (121754263131/2500000000000 : ℝ)^31
        have hw : |(-905244463/10000000000 : ℝ)|=(905244463/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316044_s1_0 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-453008639/2000000000 : ℝ)*x 0 + (-2826897087/5000000000 : ℝ)*x 1 + (-4415710721/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (453008639/2000000000 : ℝ)^39 ≤ (3087980934419/20000000000000 : ℝ)^31 := by
    have hnat : (453008639 : ℕ)^39*20000000000000^31 ≤ 3087980934419^31*2000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      453008639 2000000000 3087980934419 20000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2826897087/5000000000 : ℝ)^39 ≤ (4880088908941/10000000000000 : ℝ)^31 := by
    have hnat : (2826897087 : ℕ)^39*10000000000000^31 ≤ 4880088908941^31*5000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2826897087 5000000000 4880088908941 10000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4415710721/10000000000 : ℝ)^39 ≤ (4469900777477/12500000000000 : ℝ)^31 := by
    have hnat : (4415710721 : ℕ)^39*12500000000000^31 ≤ 4469900777477^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4415710721 10000000000 4469900777477 12500000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-453008639/2000000000 : ℝ), (-2826897087/5000000000 : ℝ), (-4415710721/10000000000 : ℝ)] ![(3087980934419/20000000000000 : ℝ), (4880088908941/10000000000000 : ℝ), (4469900777477/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-453008639/2000000000 : ℝ)|^39 ≤ (3087980934419/20000000000000 : ℝ)^31
        have hw : |(-453008639/2000000000 : ℝ)|=(453008639/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2826897087/5000000000 : ℝ)|^39 ≤ (4880088908941/10000000000000 : ℝ)^31
        have hw : |(-2826897087/5000000000 : ℝ)|=(2826897087/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-4415710721/10000000000 : ℝ)|^39 ≤ (4469900777477/12500000000000 : ℝ)^31
        have hw : |(-4415710721/10000000000 : ℝ)|=(4415710721/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316044_s1_1 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (2366222991/5000000000 : ℝ)*x 0 + (437170551/1250000000 : ℝ)*x 1 + (-4273472971/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2366222991/5000000000 : ℝ)^39 ≤ (312123732629/800000000000 : ℝ)^31 := by
    have hnat : (2366222991 : ℕ)^39*800000000000^31 ≤ 312123732629^31*5000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2366222991 5000000000 312123732629 800000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (437170551/1250000000 : ℝ)^39 ≤ (6667094442941/25000000000000 : ℝ)^31 := by
    have hnat : (437170551 : ℕ)^39*25000000000000^31 ≤ 6667094442941^31*1250000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      437170551 1250000000 6667094442941 25000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4273472971/10000000000 : ℝ)^39 ≤ (17158077821937/50000000000000 : ℝ)^31 := by
    have hnat : (4273472971 : ℕ)^39*50000000000000^31 ≤ 17158077821937^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4273472971 10000000000 17158077821937 50000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2366222991/5000000000 : ℝ), (437170551/1250000000 : ℝ), (-4273472971/10000000000 : ℝ)] ![(312123732629/800000000000 : ℝ), (6667094442941/25000000000000 : ℝ), (17158077821937/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2366222991/5000000000 : ℝ)|^39 ≤ (312123732629/800000000000 : ℝ)^31
        have hw : |(2366222991/5000000000 : ℝ)|=(2366222991/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(437170551/1250000000 : ℝ)|^39 ≤ (6667094442941/25000000000000 : ℝ)^31
        have hw : |(437170551/1250000000 : ℝ)|=(437170551/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-4273472971/10000000000 : ℝ)|^39 ≤ (17158077821937/50000000000000 : ℝ)^31
        have hw : |(-4273472971/10000000000 : ℝ)|=(4273472971/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316044_s1_2 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (4730253099/10000000000 : ℝ)*x 0 + (-3498401089/10000000000 : ℝ)*x 1 + (534342463/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4730253099/10000000000 : ℝ)^39 ≤ (38992723798993/100000000000000 : ℝ)^31 := by
    have hnat : (4730253099 : ℕ)^39*100000000000000^31 ≤ 38992723798993^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4730253099 10000000000 38992723798993 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3498401089/10000000000 : ℝ)^39 ≤ (5335664625737/20000000000000 : ℝ)^31 := by
    have hnat : (3498401089 : ℕ)^39*20000000000000^31 ≤ 5335664625737^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3498401089 10000000000 5335664625737 20000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (534342463/1250000000 : ℝ)^39 ≤ (6865790611897/20000000000000 : ℝ)^31 := by
    have hnat : (534342463 : ℕ)^39*20000000000000^31 ≤ 6865790611897^31*1250000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      534342463 1250000000 6865790611897 20000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4730253099/10000000000 : ℝ), (-3498401089/10000000000 : ℝ), (534342463/1250000000 : ℝ)] ![(38992723798993/100000000000000 : ℝ), (5335664625737/20000000000000 : ℝ), (6865790611897/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4730253099/10000000000 : ℝ)|^39 ≤ (38992723798993/100000000000000 : ℝ)^31
        have hw : |(4730253099/10000000000 : ℝ)|=(4730253099/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3498401089/10000000000 : ℝ)|^39 ≤ (5335664625737/20000000000000 : ℝ)^31
        have hw : |(-3498401089/10000000000 : ℝ)|=(3498401089/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(534342463/1250000000 : ℝ)|^39 ≤ (6865790611897/20000000000000 : ℝ)^31
        have hw : |(534342463/1250000000 : ℝ)|=(534342463/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316044_s1_6 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (5933384341/10000000000 : ℝ)*x 0 + (-3613225633/10000000000 : ℝ)*x 1 + (-2821991511/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5933384341/10000000000 : ℝ)^39 ≤ (25928052651229/50000000000000 : ℝ)^31 := by
    have hnat : (5933384341 : ℕ)^39*50000000000000^31 ≤ 25928052651229^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5933384341 10000000000 25928052651229 50000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3613225633/10000000000 : ℝ)^39 ≤ (3473069738651/12500000000000 : ℝ)^31 := by
    have hnat : (3613225633 : ℕ)^39*12500000000000^31 ≤ 3473069738651^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3613225633 10000000000 3473069738651 12500000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2821991511/10000000000 : ℝ)^39 ≤ (20359336775573/100000000000000 : ℝ)^31 := by
    have hnat : (2821991511 : ℕ)^39*100000000000000^31 ≤ 20359336775573^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2821991511 10000000000 20359336775573 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5933384341/10000000000 : ℝ), (-3613225633/10000000000 : ℝ), (-2821991511/10000000000 : ℝ)] ![(25928052651229/50000000000000 : ℝ), (3473069738651/12500000000000 : ℝ), (20359336775573/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5933384341/10000000000 : ℝ)|^39 ≤ (25928052651229/50000000000000 : ℝ)^31
        have hw : |(5933384341/10000000000 : ℝ)|=(5933384341/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3613225633/10000000000 : ℝ)|^39 ≤ (3473069738651/12500000000000 : ℝ)^31
        have hw : |(-3613225633/10000000000 : ℝ)|=(3613225633/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2821991511/10000000000 : ℝ)|^39 ≤ (20359336775573/100000000000000 : ℝ)^31
        have hw : |(-2821991511/10000000000 : ℝ)|=(2821991511/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c316044 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (177257/100000 : ℝ) (173433/100000 : ℝ) (1587/2000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, false, false]]) : False := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (1587/2000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (1587/2000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (1587/2000 : ℝ)*P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (1587/2000 : ℝ)*P 1 ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (1587/2000 : ℝ)*P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (1587/2000 : ℝ)*P 2 ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((-1 : ℝ)*(X 0 1+X 1 1)) ∧ ((-1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((-1 : ℝ)*pair X 2 1) ∧ ((-1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base10 : ((-1 : ℝ)*X 0 1+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 1).1]
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
  have s0_pow0 : (1 : ℝ) ^ (19/4 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^19 ≤ (1 : ℝ)^4 := by
      have hnat : (1 : ℕ)^19*1^4 ≤ 1^4*1^19 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 19 4 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 19 4 (by norm_num) hpowers
    exact h
  have s0_corner0a : (2 : ℝ) ≤ (11571102372827199/10000000000000000 : ℝ) ^ (19/4 : ℝ) := by
    have hpowers : (2 : ℝ)^4 ≤ (11571102372827199/10000000000000000 : ℝ)^19 := by
      have hnat : (2 : ℕ)^4*10000000000000000^19 ≤ 11571102372827199^19*1^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 11571102372827199 10000000000000000 4 19 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11571102372827199/10000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 19 4 (by norm_num) hpowers
    exact h
  have s0_corner0b : (3 : ℝ) ≤ (12602206158919821/10000000000000000 : ℝ) ^ (19/4 : ℝ) := by
    have hpowers : (3 : ℝ)^4 ≤ (12602206158919821/10000000000000000 : ℝ)^19 := by
      have hnat : (3 : ℕ)^4*10000000000000000^19 ≤ 12602206158919821^19*1^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 12602206158919821 10000000000000000 4 19 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12602206158919821/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 19 4 (by norm_num) hpowers
    exact h
  have major_s0_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(1571102372827199/10000000000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(515551893046311/5000000000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (19/4 : ℝ)) (rho := (1 : ℝ)) (alpha := (1571102372827199/10000000000000000 : ℝ)) (beta := (515551893046311/5000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow0,s0_corner0a]) (by linarith only [s0_pow0,s0_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, false, false]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (1 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order0.2.2])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(1571102372827199/10000000000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(515551893046311/5000000000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow1 : (1 : ℝ) ^ (19/4 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^19 ≤ (1 : ℝ)^4 := by
      have hnat : (1 : ℕ)^19*1^4 ≤ 1^4*1^19 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 19 4 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 19 4 (by norm_num) hpowers
    exact h
  have s0_corner1a : (2 : ℝ) ≤ (11571102372827199/10000000000000000 : ℝ) ^ (19/4 : ℝ) := by
    have hpowers : (2 : ℝ)^4 ≤ (11571102372827199/10000000000000000 : ℝ)^19 := by
      have hnat : (2 : ℕ)^4*10000000000000000^19 ≤ 11571102372827199^19*1^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 11571102372827199 10000000000000000 4 19 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11571102372827199/10000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 19 4 (by norm_num) hpowers
    exact h
  have s0_corner1b : (3 : ℝ) ≤ (12602206158919821/10000000000000000 : ℝ) ^ (19/4 : ℝ) := by
    have hpowers : (3 : ℝ)^4 ≤ (12602206158919821/10000000000000000 : ℝ)^19 := by
      have hnat : (3 : ℕ)^4*10000000000000000^19 ≤ 12602206158919821^19*1^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 12602206158919821 10000000000000000 4 19 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12602206158919821/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 19 4 (by norm_num) hpowers
    exact h
  have major_s0_1 : P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1))+(1571102372827199/10000000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(515551893046311/5000000000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (19/4 : ℝ)) (rho := (1 : ℝ)) (alpha := (1571102372827199/10000000000000000 : ℝ)) (beta := (515551893046311/5000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow1,s0_corner1a]) (by linarith only [s0_pow1,s0_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, false, false]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (1 : ℝ)*((-1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order1.2.2])
    change lpNorm p (pair X 1) ≤ ((-1 : ℝ)*pair X 1 1)+(1571102372827199/10000000000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(515551893046311/5000000000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow2 : (1 : ℝ) ^ (19/4 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^19 ≤ (1 : ℝ)^4 := by
      have hnat : (1 : ℕ)^19*1^4 ≤ 1^4*1^19 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 19 4 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 19 4 (by norm_num) hpowers
    exact h
  have s0_corner2a : (2 : ℝ) ≤ (11571102372827199/10000000000000000 : ℝ) ^ (19/4 : ℝ) := by
    have hpowers : (2 : ℝ)^4 ≤ (11571102372827199/10000000000000000 : ℝ)^19 := by
      have hnat : (2 : ℕ)^4*10000000000000000^19 ≤ 11571102372827199^19*1^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 11571102372827199 10000000000000000 4 19 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11571102372827199/10000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 19 4 (by norm_num) hpowers
    exact h
  have s0_corner2b : (3 : ℝ) ≤ (12602206158919821/10000000000000000 : ℝ) ^ (19/4 : ℝ) := by
    have hpowers : (3 : ℝ)^4 ≤ (12602206158919821/10000000000000000 : ℝ)^19 := by
      have hnat : (3 : ℕ)^4*10000000000000000^19 ≤ 12602206158919821^19*1^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 12602206158919821 10000000000000000 4 19 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12602206158919821/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 19 4 (by norm_num) hpowers
    exact h
  have major_s0_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(1571102372827199/10000000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(515551893046311/5000000000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (19/4 : ℝ)) (rho := (1 : ℝ)) (alpha := (1571102372827199/10000000000000000 : ℝ)) (beta := (515551893046311/5000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow2,s0_corner2a]) (by linarith only [s0_pow2,s0_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, false, false]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (1 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order2.2.2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(1571102372827199/10000000000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(515551893046311/5000000000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s0_0 : ((-768119813/10000000000 : ℝ)*X 0 0+(-103202217/156250000 : ℝ)*X 0 1+(-2253617547/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c316044_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_2 : ((2528498091/5000000000 : ℝ)*X 2 0+(-3099151517/10000000000 : ℝ)*X 2 1+(2154872889/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c316044_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_6 : ((7539924467/10000000000 : ℝ)*X 0 0+(-653105311/2500000000 : ℝ)*X 0 1+(-356545051/2000000000 : ℝ)*X 0 2+(7539924467/10000000000 : ℝ)*X 1 0+(-653105311/2500000000 : ℝ)*X 1 1+(-356545051/2000000000 : ℝ)*X 1 2+(7539924467/10000000000 : ℝ)*X 2 0+(-653105311/2500000000 : ℝ)*X 2 1+(-356545051/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c316044_s0_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_7 : ((-51708217/625000000 : ℝ)*X 0 0+(-6854041689/10000000000 : ℝ)*X 0 1+(-838038443/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c316044_s0_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_8 : ((1219671699/2500000000 : ℝ)*X 1 0+(3672210817/10000000000 : ℝ)*X 1 1+(-988118679/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c316044_s0_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_9 : ((2439343419/5000000000 : ℝ)*X 2 0+(-5027739/19531250 : ℝ)*X 2 1+(4953835371/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c316044_s0_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_13 : ((3837726099/5000000000 : ℝ)*X 0 0+(-2108907581/10000000000 : ℝ)*X 0 1+(-1059484721/5000000000 : ℝ)*X 0 2+(3837726099/5000000000 : ℝ)*X 1 0+(-2108907581/10000000000 : ℝ)*X 1 1+(-1059484721/5000000000 : ℝ)*X 1 2+(3837726099/5000000000 : ℝ)*X 2 0+(-2108907581/10000000000 : ℝ)*X 2 1+(-1059484721/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c316044_s0_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_14 : ((-11894167/2000000000 : ℝ)*X 0 0+(-832177719/1250000000 : ℝ)*X 0 1+(-481779997/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c316044_s0_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_15 : ((4553457887/10000000000 : ℝ)*X 1 0+(629444497/2000000000 : ℝ)*X 1 1+(-4776974473/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c316044_s0_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_16 : ((5810859061/10000000000 : ℝ)*X 2 0+(-20337693/78125000 : ℝ)*X 2 1+(3951273867/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c316044_s0_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_19 : ((1784280413/2000000000 : ℝ)*X 0 0+(-84189381/625000000 : ℝ)*X 0 1+(-487405019/5000000000 : ℝ)*X 0 2+(1784280413/2000000000 : ℝ)*X 1 0+(-84189381/625000000 : ℝ)*X 1 1+(-487405019/5000000000 : ℝ)*X 1 2+(1784280413/2000000000 : ℝ)*X 2 0+(-84189381/625000000 : ℝ)*X 2 1+(-487405019/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c316044_s0_19 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_20 : ((-2142887/400000000 : ℝ)*X 0 0+(-3549657111/5000000000 : ℝ)*X 0 1+(-4328692401/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c316044_s0_20 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_21 : ((2908378851/5000000000 : ℝ)*X 1 0+(2829839267/10000000000 : ℝ)*X 1 1+(-3737527327/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c316044_s0_21 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_22 : ((2285901191/5000000000 : ℝ)*X 2 0+(-341657377/1000000000 : ℝ)*X 2 1+(4512460469/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c316044_s0_22 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_25 : ((8874712171/10000000000 : ℝ)*X 0 0+(-1484655017/10000000000 : ℝ)*X 0 1+(-905244463/10000000000 : ℝ)*X 0 2+(8874712171/10000000000 : ℝ)*X 1 0+(-1484655017/10000000000 : ℝ)*X 1 1+(-905244463/10000000000 : ℝ)*X 1 2+(8874712171/10000000000 : ℝ)*X 2 0+(-1484655017/10000000000 : ℝ)*X 2 1+(-905244463/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c316044_s0_25 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s0_0 : (0 : ℝ) ≤ ((333/5000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(333/5000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (40237207687724138054997/2500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (118452311179/200000000000 : ℝ)*(base39) + (247958297251/500000000000 : ℝ)*(base49) + (1411265319581/500000000000 : ℝ)*(major_s0_0) + (1411265319581/500000000000 : ℝ)*(major_s0_1) + (1411265319581/500000000000 : ℝ)*(major_s0_2) + (382911561/1000000000000 : ℝ)*(sp_s0_0) + (64654719/250000000000 : ℝ)*(sp_s0_6) + (253270282231/62500000000 : ℝ)*(sp_s0_7) + (2026313339851/500000000000 : ℝ)*(sp_s0_8) + (2026310336903/500000000000 : ℝ)*(sp_s0_9) + (1592079420897/1000000000000 : ℝ)*(sp_s0_13) + (2279847/25000000000 : ℝ)*(sp_s0_15) + (2611581/250000000000 : ℝ)*(sp_s0_20) + (3037493/31250000000 : ℝ)*(sp_s0_22) + (796169019887/500000000000 : ℝ)*(f.failure) + (2026358936791/500000000000 : ℝ)*(f.sum) + (1484621375833619/2500000000000000000000000000 : ℝ)*base63 + (2630885162865691/2500000000000000000000000000 : ℝ)*base64 + (1547536163884309/2500000000000000000000000000 : ℝ)*base66 + (4030923699083619/5000000000000000000000000000 : ℝ)*base69 + (1025946088647763/5000000000000000000000000000 : ℝ)*base70 + (532529270384309/2500000000000000000000000000 : ℝ)*base72 + (4096180945083619/5000000000000000000000000000 : ℝ)*base75 + (1642007761416381/5000000000000000000000000000 : ℝ)*base76 + (173187033615691/1250000000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base80 + (9959/50000000000000000 : ℝ)*base87 + (9959/50000000000000000 : ℝ)*base89 + (9959/50000000000000000 : ℝ)*base91 + (1/1000000000000 : ℝ)*base92 + hcertificate_margin
  have ratio_s0_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-9861/25000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(-9861/25000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (17816589192497833530417/5000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1323494535173/500000000000 : ℝ)*(base39) + (1782956308299/1000000000000 : ℝ)*(base40) + (831565982141/1000000000000 : ℝ)*(base49) + (96333/1000000000000 : ℝ)*(base60) + (5538849752673/1000000000000 : ℝ)*(major_s0_0) + (5538849752673/1000000000000 : ℝ)*(major_s0_1) + (5538849752673/1000000000000 : ℝ)*(major_s0_2) + (28706059/500000000000 : ℝ)*(sp_s0_0) + (38420723/1000000000000 : ℝ)*(sp_s0_9) + (3976442167899/500000000000 : ℝ)*(sp_s0_14) + (3976469512767/500000000000 : ℝ)*(sp_s0_15) + (994112915899/125000000000 : ℝ)*(sp_s0_16) + (624951313931/200000000000 : ℝ)*(sp_s0_19) + (2722381/1000000000000 : ℝ)*(sp_s0_21) + (624951313931/200000000000 : ℝ)*(f.failure) + (1590588349583/200000000000 : ℝ)*(f.sum) + (1487279238147073/5000000000000000000000000000 : ℝ)*base62 + (2213275994960697/5000000000000000000000000000 : ℝ)*base65 + (200873093960697/5000000000000000000000000000 : ℝ)*base66 + (3074935777647073/10000000000000000000000000000 : ℝ)*base68 + (2339225310274321/10000000000000000000000000000 : ℝ)*base71 + (124328914539303/5000000000000000000000000000 : ℝ)*base73 + (826151243647073/10000000000000000000000000000 : ℝ)*base74 + (3036177029352927/10000000000000000000000000000 : ℝ)*base77 + (727541066710697/2500000000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base81 + (7267/20000000000000000 : ℝ)*base87 + (7267/20000000000000000 : ℝ)*base89 + (7267/20000000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s0_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-799/2000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-799/2000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (47511421031219377422657/5000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (13513389/1000000000000 : ℝ)*(base10) + (177029488137/62500000000 : ℝ)*(base39) + (150241427049/100000000000 : ℝ)*(base40) + (213803607113/250000000000 : ℝ)*(base49) + (5594228341343/1000000000000 : ℝ)*(major_s0_0) + (5594228341343/1000000000000 : ℝ)*(major_s0_1) + (5594228341343/1000000000000 : ℝ)*(major_s0_2) + (13776259/500000000000 : ℝ)*(sp_s0_2) + (67849653/1000000000000 : ℝ)*(sp_s0_7) + (18217847/500000000000 : ℝ)*(sp_s0_8) + (8032373606969/1000000000000 : ℝ)*(sp_s0_20) + (8032418534317/1000000000000 : ℝ)*(sp_s0_21) + (8032427417493/1000000000000 : ℝ)*(sp_s0_22) + (788999636311/250000000000 : ℝ)*(sp_s0_25) + (788999636311/250000000000 : ℝ)*(f.failure) + (8032454970011/1000000000000 : ℝ)*(f.sum) + (849593639911743/5000000000000000000000000000 : ℝ)*base62 + (751977923435673/5000000000000000000000000000 : ℝ)*base64 + (532109982935673/5000000000000000000000000000 : ℝ)*base67 + (750134644588257/10000000000000000000000000000 : ℝ)*base69 + (1522425192283089/10000000000000000000000000000 : ℝ)*base70 + (1985959782435673/5000000000000000000000000000 : ℝ)*base73 + (995736000588257/10000000000000000000000000000 : ℝ)*base75 + (4261027109411743/10000000000000000000000000000 : ℝ)*base76 + (2993278702685673/2500000000000000000000000000 : ℝ)*base79 + (3927/25000000000000000 : ℝ)*base87 + (3927/25000000000000000 : ℝ)*base89 + (3927/25000000000000000 : ℝ)*base91 + hcertificate_margin
  have s1_pow0 : (333/5000 : ℝ) ^ (19/4 : ℝ) ≤ (128965216900423/50000000000000000000 : ℝ) := by
    have hpowers : (333/5000 : ℝ)^19 ≤ (128965216900423/50000000000000000000 : ℝ)^4 := by
      have hnat : (333 : ℕ)^19*50000000000000000000^4 ≤ 128965216900423^4*5000^19 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        333 5000 128965216900423 50000000000000000000 19 4 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (333/5000 : ℝ)) (X := (128965216900423/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 19 4 (by norm_num) hpowers
    exact h
  have s1_corner0a : (50000128965216900423/50000000000000000000 : ℝ) ≤ (2500001357527217/2500000000000000 : ℝ) ^ (19/4 : ℝ) := by
    have hpowers : (50000128965216900423/50000000000000000000 : ℝ)^4 ≤ (2500001357527217/2500000000000000 : ℝ)^19 := by
      have hnat : (50000128965216900423 : ℕ)^4*2500000000000000^19 ≤ 2500001357527217^19*50000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000128965216900423 50000000000000000000 2500001357527217 2500000000000000 4 19 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500001357527217/2500000000000000 : ℝ)) (X := (50000128965216900423/50000000000000000000 : ℝ)) (by norm_num) 19 4 (by norm_num) hpowers
    exact h
  have s1_corner0b : (25000128965216900423/25000000000000000000 : ℝ) ≤ (5000005430103339/5000000000000000 : ℝ) ^ (19/4 : ℝ) := by
    have hpowers : (25000128965216900423/25000000000000000000 : ℝ)^4 ≤ (5000005430103339/5000000000000000 : ℝ)^19 := by
      have hnat : (25000128965216900423 : ℕ)^4*5000000000000000^19 ≤ 5000005430103339^19*25000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000128965216900423 25000000000000000000 5000005430103339 5000000000000000 4 19 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000005430103339/5000000000000000 : ℝ)) (X := (25000128965216900423/25000000000000000000 : ℝ)) (by norm_num) 19 4 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(1357527217/166500000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(543009781/66600000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (19/4 : ℝ)) (rho := (333/5000 : ℝ)) (alpha := (1357527217/166500000000000 : ℝ)) (beta := (543009781/66600000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, false, false]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (333/5000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(1357527217/166500000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(543009781/66600000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (9861/25000 : ℝ) ^ (19/4 : ℝ) ≤ (1204784892763014199/100000000000000000000 : ℝ) := by
    have hpowers : (9861/25000 : ℝ)^19 ≤ (1204784892763014199/100000000000000000000 : ℝ)^4 := by
      have hnat : (9861 : ℕ)^19*100000000000000000000^4 ≤ 1204784892763014199^4*25000^19 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        9861 25000 1204784892763014199 100000000000000000000 19 4 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (9861/25000 : ℝ)) (X := (1204784892763014199/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 19 4 (by norm_num) hpowers
    exact h
  have s1_corner1a : (101204784892763014199/100000000000000000000 : ℝ) ≤ (401009765131881/400000000000000 : ℝ) ^ (19/4 : ℝ) := by
    have hpowers : (101204784892763014199/100000000000000000000 : ℝ)^4 ≤ (401009765131881/400000000000000 : ℝ)^19 := by
      have hnat : (101204784892763014199 : ℕ)^4*400000000000000^19 ≤ 401009765131881^19*100000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        101204784892763014199 100000000000000000000 401009765131881 400000000000000 4 19 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (401009765131881/400000000000000 : ℝ)) (X := (101204784892763014199/100000000000000000000 : ℝ)) (by norm_num) 19 4 (by norm_num) hpowers
    exact h
  have s1_corner1b : (51204784892763014199/50000000000000000000 : ℝ) ≤ (10050252110078043/10000000000000000 : ℝ) ^ (19/4 : ℝ) := by
    have hpowers : (51204784892763014199/50000000000000000000 : ℝ)^4 ≤ (10050252110078043/10000000000000000 : ℝ)^19 := by
      have hnat : (51204784892763014199 : ℕ)^4*10000000000000000^19 ≤ 10050252110078043^19*50000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        51204784892763014199 50000000000000000000 10050252110078043 10000000000000000 4 19 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10050252110078043/10000000000000000 : ℝ)) (X := (51204784892763014199/50000000000000000000 : ℝ)) (by norm_num) 19 4 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1))+(1009765131881/157776000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(219368261237/34600000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (19/4 : ℝ)) (rho := (9861/25000 : ℝ)) (alpha := (1009765131881/157776000000000 : ℝ)) (beta := (219368261237/34600000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, false, false]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (9861/25000 : ℝ)*((-1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((-1 : ℝ)*pair X 1 1)+(1009765131881/157776000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(219368261237/34600000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (799/2000 : ℝ) ^ (19/4 : ℝ) ≤ (1279984534648922449/100000000000000000000 : ℝ) := by
    have hpowers : (799/2000 : ℝ)^19 ≤ (1279984534648922449/100000000000000000000 : ℝ)^4 := by
      have hnat : (799 : ℕ)^19*100000000000000000000^4 ≤ 1279984534648922449^4*2000^19 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        799 2000 1279984534648922449 100000000000000000000 19 4 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (799/2000 : ℝ)) (X := (1279984534648922449/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 19 4 (by norm_num) hpowers
    exact h
  have s1_corner2a : (101279984534648922449/100000000000000000000 : ℝ) ≤ (5013405960664481/5000000000000000 : ℝ) ^ (19/4 : ℝ) := by
    have hpowers : (101279984534648922449/100000000000000000000 : ℝ)^4 ≤ (5013405960664481/5000000000000000 : ℝ)^19 := by
      have hnat : (101279984534648922449 : ℕ)^4*5000000000000000^19 ≤ 5013405960664481^19*100000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        101279984534648922449 100000000000000000000 5013405960664481 5000000000000000 4 19 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5013405960664481/5000000000000000 : ℝ)) (X := (101279984534648922449/100000000000000000000 : ℝ)) (by norm_num) 19 4 (by norm_num) hpowers
    exact h
  have s1_corner2b : (51279984534648922449/50000000000000000000 : ℝ) ≤ (2513339412209967/2500000000000000 : ℝ) ^ (19/4 : ℝ) := by
    have hpowers : (51279984534648922449/50000000000000000000 : ℝ)^4 ≤ (2513339412209967/2500000000000000 : ℝ)^19 := by
      have hnat : (51279984534648922449 : ℕ)^4*2500000000000000^19 ≤ 2513339412209967^19*50000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        51279984534648922449 50000000000000000000 2513339412209967 2500000000000000 4 19 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2513339412209967/2500000000000000 : ℝ)) (X := (51279984534648922449/50000000000000000000 : ℝ)) (by norm_num) 19 4 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(13405960664481/1997500000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(282401356499/42500000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (19/4 : ℝ)) (rho := (799/2000 : ℝ)) (alpha := (13405960664481/1997500000000000 : ℝ)) (beta := (282401356499/42500000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, false, false]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (799/2000 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(13405960664481/1997500000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(282401356499/42500000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-453008639/2000000000 : ℝ)*X 0 0+(-2826897087/5000000000 : ℝ)*X 0 1+(-4415710721/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c316044_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_1 : ((2366222991/5000000000 : ℝ)*X 1 0+(437170551/1250000000 : ℝ)*X 1 1+(-4273472971/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c316044_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((4730253099/10000000000 : ℝ)*X 2 0+(-3498401089/10000000000 : ℝ)*X 2 1+(534342463/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c316044_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_6 : ((5933384341/10000000000 : ℝ)*X 0 0+(-3613225633/10000000000 : ℝ)*X 0 1+(-2821991511/10000000000 : ℝ)*X 0 2+(5933384341/10000000000 : ℝ)*X 1 0+(-3613225633/10000000000 : ℝ)*X 1 1+(-2821991511/10000000000 : ℝ)*X 1 2+(5933384341/10000000000 : ℝ)*X 2 0+(-3613225633/10000000000 : ℝ)*X 2 1+(-2821991511/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c316044_s1_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have hsep : (-381771/50000 : ℝ) < ((-177257/100000 : ℝ)*P 0+(-177257/100000 : ℝ)*P 1+(-177257/100000 : ℝ)*P 2+(1 : ℝ)*T) := by
    have hcertificate_margin : (-381771/50000 : ℝ) < (-146748004550627362768922933130881/19434716200000000000000000000000 : ℝ) := by norm_num
    linear_combination (587/40000000000 : ℝ)*(base10) + (94545582849/100000000000 : ℝ)*(base39) + (530706650331/1000000000000 : ℝ)*(base40) + (8799/1000000000000 : ℝ)*(base43) + (11491404737/31250000000 : ℝ)*(base49) + (373/250000000000 : ℝ)*(base50) + (3451/1000000000000 : ℝ)*(base59) + (149/62500000000 : ℝ)*(base60) + (177257/100000 : ℝ)*(major_s1_0) + (1772569991201/1000000000000 : ℝ)*(major_s1_1) + (177257/100000 : ℝ)*(major_s1_2) + (2516939303731/1000000000000 : ℝ)*(sp_s1_0) + (503387865441/200000000000 : ℝ)*(sp_s1_1) + (1258469659203/500000000000 : ℝ)*(sp_s1_2) + (1 : ℝ)*(sp_s1_6) + (503387865441/200000000000 : ℝ)*(f.sum) + (2856294895472527/126063024000000000000000000000 : ℝ)*base63 + (43338622851/85000000000000000000000 : ℝ)*base64 + (420320447903/34600000000000000000000000 : ℝ)*base66 + (1699797231/799000000000000000000000 : ℝ)*base69 + (157178188949/1415250000000000000000000 : ℝ)*base71 + (161929394737/666000000000000000000000 : ℝ)*base72 + (177565972471133/788880000000000000000000000 : ℝ)*base75 + (475322898311/1665000000000000000000000 : ℝ)*base77 + (142317413689199/11521800000000000000000000000 : ℝ)*base78 + hcertificate_margin
  linarith only [hsep,f.failure]

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
namespace HlawkaSchatten.DiagonalCutoff4
theorem wide_coarse_distinct_p016_b021 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ))
    (c : Fin 88) (hlo : 44 ≤ c.val) (hhi : c.val < 46)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (177257/100000 : ℝ) (173433/100000 : ℝ) (1587/2000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  have hc : c=44 ∨ c=45 := by omega
  rcases hc with rfl|rfl
  · exact collision_c316044 p hpa (by linarith only [hpb]) X hX
  · exact collision_c316045 p hpa (by linarith only [hpb]) X hX

end HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ))
    (c : Fin 88) (hlo : 44 ≤ c.val) (hhi : c.val < 46)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (177257/100000 : ℝ) (173433/100000 : ℝ) (1587/2000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  exact HlawkaSchatten.DiagonalCutoff4.wide_coarse_distinct_p016_b021 p hpa hpb c hlo hhi hn63 hn87 X hX

#print axioms solution
