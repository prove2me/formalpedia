-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p015_b033
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:55:09.431339+00:00
-- url     : https://prove2.me/submissions/247039aa-e72d-4a3f-9064-9a587f1e6562

import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c315083_s0
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c315083_s1
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c315083_s2
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
theorem HlawkaSchatten.DiagonalCutoff4.collision_c315083 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (174659/100000 : ℝ) (34911/20000 : ℝ) (15821/20000 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![true, true, true]]) : False := by
  have h0 := collision_c315083_s0 p hpa hpb X hX
  have h1 := collision_c315083_s1 p hpa hpb X hX h0
  exact collision_c315083_s2 p hpa hpb X hX h1

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
theorem collision_support_c315082_s0_0 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-3515813083/10000000000 : ℝ)*x 0 + (77182843/250000000 : ℝ)*x 1 + (2930533249/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3515813083/10000000000 : ℝ)^19 ≤ (26605166755687/100000000000000 : ℝ)^15 := by
    have hnat : (3515813083 : ℕ)^19*100000000000000^15 ≤ 26605166755687^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3515813083 10000000000 26605166755687 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (77182843/250000000 : ℝ)^19 ≤ (11283373666257/50000000000000 : ℝ)^15 := by
    have hnat : (77182843 : ℕ)^19*50000000000000^15 ≤ 11283373666257^15*250000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      77182843 250000000 11283373666257 50000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2930533249/5000000000 : ℝ)^19 ≤ (50828085891029/100000000000000 : ℝ)^15 := by
    have hnat : (2930533249 : ℕ)^19*100000000000000^15 ≤ 50828085891029^15*5000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2930533249 5000000000 50828085891029 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-3515813083/10000000000 : ℝ), (77182843/250000000 : ℝ), (2930533249/5000000000 : ℝ)] ![(26605166755687/100000000000000 : ℝ), (11283373666257/50000000000000 : ℝ), (50828085891029/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-3515813083/10000000000 : ℝ)|^19 ≤ (26605166755687/100000000000000 : ℝ)^15
        have hw : |(-3515813083/10000000000 : ℝ)|=(3515813083/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(77182843/250000000 : ℝ)|^19 ≤ (11283373666257/50000000000000 : ℝ)^15
        have hw : |(77182843/250000000 : ℝ)|=(77182843/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2930533249/5000000000 : ℝ)|^19 ≤ (50828085891029/100000000000000 : ℝ)^15
        have hw : |(2930533249/5000000000 : ℝ)|=(2930533249/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c315082_s0_1 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (4212455731/10000000000 : ℝ)*x 0 + (-698338497/2500000000 : ℝ)*x 1 + (54790097/100000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4212455731/10000000000 : ℝ)^19 ≤ (33451180071913/100000000000000 : ℝ)^15 := by
    have hnat : (4212455731 : ℕ)^19*100000000000000^15 ≤ 33451180071913^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4212455731 10000000000 33451180071913 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (698338497/2500000000 : ℝ)^19 ≤ (2485056391229/12500000000000 : ℝ)^15 := by
    have hnat : (698338497 : ℕ)^19*12500000000000^15 ≤ 2485056391229^15*2500000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      698338497 2500000000 2485056391229 12500000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (54790097/100000000 : ℝ)^19 ≤ (46668368786227/100000000000000 : ℝ)^15 := by
    have hnat : (54790097 : ℕ)^19*100000000000000^15 ≤ 46668368786227^15*100000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      54790097 100000000 46668368786227 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4212455731/10000000000 : ℝ), (-698338497/2500000000 : ℝ), (54790097/100000000 : ℝ)] ![(33451180071913/100000000000000 : ℝ), (2485056391229/12500000000000 : ℝ), (46668368786227/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4212455731/10000000000 : ℝ)|^19 ≤ (33451180071913/100000000000000 : ℝ)^15
        have hw : |(4212455731/10000000000 : ℝ)|=(4212455731/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-698338497/2500000000 : ℝ)|^19 ≤ (2485056391229/12500000000000 : ℝ)^15
        have hw : |(-698338497/2500000000 : ℝ)|=(698338497/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(54790097/100000000 : ℝ)|^19 ≤ (46668368786227/100000000000000 : ℝ)^15
        have hw : |(54790097/100000000 : ℝ)|=(54790097/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c315082_s0_7 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-377816109/1250000000 : ℝ)*x 0 + (362361059/2500000000 : ℝ)*x 1 + (3746154719/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (377816109/1250000000 : ℝ)^19 ≤ (21968610057051/100000000000000 : ℝ)^15 := by
    have hnat : (377816109 : ℕ)^19*100000000000000^15 ≤ 21968610057051^15*1250000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      377816109 1250000000 21968610057051 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (362361059/2500000000 : ℝ)^19 ≤ (8660080212599/100000000000000 : ℝ)^15 := by
    have hnat : (362361059 : ℕ)^19*100000000000000^15 ≤ 8660080212599^15*2500000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      362361059 2500000000 8660080212599 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3746154719/5000000000 : ℝ)^19 ≤ (69371309715601/100000000000000 : ℝ)^15 := by
    have hnat : (3746154719 : ℕ)^19*100000000000000^15 ≤ 69371309715601^15*5000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3746154719 5000000000 69371309715601 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-377816109/1250000000 : ℝ), (362361059/2500000000 : ℝ), (3746154719/5000000000 : ℝ)] ![(21968610057051/100000000000000 : ℝ), (8660080212599/100000000000000 : ℝ), (69371309715601/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-377816109/1250000000 : ℝ)|^19 ≤ (21968610057051/100000000000000 : ℝ)^15
        have hw : |(-377816109/1250000000 : ℝ)|=(377816109/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(362361059/2500000000 : ℝ)|^19 ≤ (8660080212599/100000000000000 : ℝ)^15
        have hw : |(362361059/2500000000 : ℝ)|=(362361059/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3746154719/5000000000 : ℝ)|^19 ≤ (69371309715601/100000000000000 : ℝ)^15
        have hw : |(3746154719/5000000000 : ℝ)|=(3746154719/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c315082_s0_8 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (864482137/2000000000 : ℝ)*x 0 + (-284023193/5000000000 : ℝ)*x 1 + (6925777743/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (864482137/2000000000 : ℝ)^19 ≤ (3456100017941/10000000000000 : ℝ)^15 := by
    have hnat : (864482137 : ℕ)^19*10000000000000^15 ≤ 3456100017941^15*2000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      864482137 2000000000 3456100017941 10000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (284023193/5000000000 : ℝ)^19 ≤ (660936125331/25000000000000 : ℝ)^15 := by
    have hnat : (284023193 : ℕ)^19*25000000000000^15 ≤ 660936125331^15*5000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      284023193 5000000000 660936125331 25000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6925777743/10000000000 : ℝ)^19 ≤ (15698813826193/25000000000000 : ℝ)^15 := by
    have hnat : (6925777743 : ℕ)^19*25000000000000^15 ≤ 15698813826193^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6925777743 10000000000 15698813826193 25000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(864482137/2000000000 : ℝ), (-284023193/5000000000 : ℝ), (6925777743/10000000000 : ℝ)] ![(3456100017941/10000000000000 : ℝ), (660936125331/25000000000000 : ℝ), (15698813826193/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(864482137/2000000000 : ℝ)|^19 ≤ (3456100017941/10000000000000 : ℝ)^15
        have hw : |(864482137/2000000000 : ℝ)|=(864482137/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-284023193/5000000000 : ℝ)|^19 ≤ (660936125331/25000000000000 : ℝ)^15
        have hw : |(-284023193/5000000000 : ℝ)|=(284023193/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6925777743/10000000000 : ℝ)|^19 ≤ (15698813826193/25000000000000 : ℝ)^15
        have hw : |(6925777743/10000000000 : ℝ)|=(6925777743/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c315082_s0_9 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (1811194753/5000000000 : ℝ)*x 0 + (3846326113/5000000000 : ℝ)*x 1 + (-92673927/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1811194753/5000000000 : ℝ)^19 ≤ (27630825041279/100000000000000 : ℝ)^15 := by
    have hnat : (1811194753 : ℕ)^19*100000000000000^15 ≤ 27630825041279^15*5000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1811194753 5000000000 27630825041279 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3846326113/5000000000 : ℝ)^19 ≤ (35864633442509/50000000000000 : ℝ)^15 := by
    have hnat : (3846326113 : ℕ)^19*50000000000000^15 ≤ 35864633442509^15*5000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3846326113 5000000000 35864633442509 50000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (92673927/5000000000 : ℝ)^19 ≤ (319954028667/50000000000000 : ℝ)^15 := by
    have hnat : (92673927 : ℕ)^19*50000000000000^15 ≤ 319954028667^15*5000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      92673927 5000000000 319954028667 50000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1811194753/5000000000 : ℝ), (3846326113/5000000000 : ℝ), (-92673927/5000000000 : ℝ)] ![(27630825041279/100000000000000 : ℝ), (35864633442509/50000000000000 : ℝ), (319954028667/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1811194753/5000000000 : ℝ)|^19 ≤ (27630825041279/100000000000000 : ℝ)^15
        have hw : |(1811194753/5000000000 : ℝ)|=(1811194753/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3846326113/5000000000 : ℝ)|^19 ≤ (35864633442509/50000000000000 : ℝ)^15
        have hw : |(3846326113/5000000000 : ℝ)|=(3846326113/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-92673927/5000000000 : ℝ)|^19 ≤ (319954028667/50000000000000 : ℝ)^15
        have hw : |(-92673927/5000000000 : ℝ)|=(92673927/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c315082_s0_13 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (2417297/625000000 : ℝ)*x 0 + (171005499/200000000 : ℝ)*x 1 + (514409127/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2417297/625000000 : ℝ)^19 ≤ (8792316799/10000000000000 : ℝ)^15 := by
    have hnat : (2417297 : ℕ)^19*10000000000000^15 ≤ 8792316799^15*625000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2417297 625000000 8792316799 10000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (171005499/200000000 : ℝ)^19 ≤ (41002604075163/50000000000000 : ℝ)^15 := by
    have hnat : (171005499 : ℕ)^19*50000000000000^15 ≤ 41002604075163^15*200000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      171005499 200000000 41002604075163 50000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (514409127/2000000000 : ℝ)^19 ≤ (8953434335443/50000000000000 : ℝ)^15 := by
    have hnat : (514409127 : ℕ)^19*50000000000000^15 ≤ 8953434335443^15*2000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      514409127 2000000000 8953434335443 50000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2417297/625000000 : ℝ), (171005499/200000000 : ℝ), (514409127/2000000000 : ℝ)] ![(8792316799/10000000000000 : ℝ), (41002604075163/50000000000000 : ℝ), (8953434335443/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2417297/625000000 : ℝ)|^19 ≤ (8792316799/10000000000000 : ℝ)^15
        have hw : |(2417297/625000000 : ℝ)|=(2417297/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(171005499/200000000 : ℝ)|^19 ≤ (41002604075163/50000000000000 : ℝ)^15
        have hw : |(171005499/200000000 : ℝ)|=(171005499/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(514409127/2000000000 : ℝ)|^19 ≤ (8953434335443/50000000000000 : ℝ)^15
        have hw : |(514409127/2000000000 : ℝ)|=(514409127/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c315082_s0_14 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-532245979/2000000000 : ℝ)*x 0 + (34947891/200000000 : ℝ)*x 1 + (757385923/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (532245979/2000000000 : ℝ)^19 ≤ (747878456489/4000000000000 : ℝ)^15 := by
    have hnat : (532245979 : ℕ)^19*4000000000000^15 ≤ 747878456489^15*2000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      532245979 2000000000 747878456489 4000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (34947891/200000000 : ℝ)^19 ≤ (10973922884199/100000000000000 : ℝ)^15 := by
    have hnat : (34947891 : ℕ)^19*100000000000000^15 ≤ 10973922884199^15*200000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      34947891 200000000 10973922884199 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (757385923/1000000000 : ℝ)^19 ≤ (8791139460619/12500000000000 : ℝ)^15 := by
    have hnat : (757385923 : ℕ)^19*12500000000000^15 ≤ 8791139460619^15*1000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      757385923 1000000000 8791139460619 12500000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-532245979/2000000000 : ℝ), (34947891/200000000 : ℝ), (757385923/1000000000 : ℝ)] ![(747878456489/4000000000000 : ℝ), (10973922884199/100000000000000 : ℝ), (8791139460619/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-532245979/2000000000 : ℝ)|^19 ≤ (747878456489/4000000000000 : ℝ)^15
        have hw : |(-532245979/2000000000 : ℝ)|=(532245979/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(34947891/200000000 : ℝ)|^19 ≤ (10973922884199/100000000000000 : ℝ)^15
        have hw : |(34947891/200000000 : ℝ)|=(34947891/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(757385923/1000000000 : ℝ)|^19 ≤ (8791139460619/12500000000000 : ℝ)^15
        have hw : |(757385923/1000000000 : ℝ)|=(757385923/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c315082_s0_15 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (7627858229/10000000000 : ℝ)*x 0 + (-1968745771/10000000000 : ℝ)*x 1 + (149047129/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (7627858229/10000000000 : ℝ)^19 ≤ (2217651665947/3125000000000 : ℝ)^15 := by
    have hnat : (7627858229 : ℕ)^19*3125000000000^15 ≤ 2217651665947^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7627858229 10000000000 2217651665947 3125000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1968745771/10000000000 : ℝ)^19 ≤ (12763610475629/100000000000000 : ℝ)^15 := by
    have hnat : (1968745771 : ℕ)^19*100000000000000^15 ≤ 12763610475629^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1968745771 10000000000 12763610475629 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (149047129/625000000 : ℝ)^19 ≤ (8135768103553/50000000000000 : ℝ)^15 := by
    have hnat : (149047129 : ℕ)^19*50000000000000^15 ≤ 8135768103553^15*625000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      149047129 625000000 8135768103553 50000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(7627858229/10000000000 : ℝ), (-1968745771/10000000000 : ℝ), (149047129/625000000 : ℝ)] ![(2217651665947/3125000000000 : ℝ), (12763610475629/100000000000000 : ℝ), (8135768103553/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(7627858229/10000000000 : ℝ)|^19 ≤ (2217651665947/3125000000000 : ℝ)^15
        have hw : |(7627858229/10000000000 : ℝ)|=(7627858229/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1968745771/10000000000 : ℝ)|^19 ≤ (12763610475629/100000000000000 : ℝ)^15
        have hw : |(-1968745771/10000000000 : ℝ)|=(1968745771/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(149047129/625000000 : ℝ)|^19 ≤ (8135768103553/50000000000000 : ℝ)^15
        have hw : |(149047129/625000000 : ℝ)|=(149047129/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c315082_s0_16 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (8424428403/10000000000 : ℝ)*x 0 + (2614049527/10000000000 : ℝ)*x 1 + (-19560877/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (8424428403/10000000000 : ℝ)^19 ≤ (5029960555223/6250000000000 : ℝ)^15 := by
    have hnat : (8424428403 : ℕ)^19*6250000000000^15 ≤ 5029960555223^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8424428403 10000000000 5029960555223 6250000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2614049527/10000000000 : ℝ)^19 ≤ (182780907021/1000000000000 : ℝ)^15 := by
    have hnat : (2614049527 : ℕ)^19*1000000000000^15 ≤ 182780907021^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2614049527 10000000000 182780907021 1000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (19560877/625000000 : ℝ)^19 ≤ (155317550431/12500000000000 : ℝ)^15 := by
    have hnat : (19560877 : ℕ)^19*12500000000000^15 ≤ 155317550431^15*625000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      19560877 625000000 155317550431 12500000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(8424428403/10000000000 : ℝ), (2614049527/10000000000 : ℝ), (-19560877/625000000 : ℝ)] ![(5029960555223/6250000000000 : ℝ), (182780907021/1000000000000 : ℝ), (155317550431/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(8424428403/10000000000 : ℝ)|^19 ≤ (5029960555223/6250000000000 : ℝ)^15
        have hw : |(8424428403/10000000000 : ℝ)|=(8424428403/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2614049527/10000000000 : ℝ)|^19 ≤ (182780907021/1000000000000 : ℝ)^15
        have hw : |(2614049527/10000000000 : ℝ)|=(2614049527/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-19560877/625000000 : ℝ)|^19 ≤ (155317550431/12500000000000 : ℝ)^15
        have hw : |(-19560877/625000000 : ℝ)|=(19560877/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c315082_s0_20 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-3381/5000000000 : ℝ)*x 0 + (1915970397/5000000000 : ℝ)*x 1 + (757385923/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3381/5000000000 : ℝ)^19 ≤ (1530249/100000000000000 : ℝ)^15 := by
    have hnat : (3381 : ℕ)^19*100000000000000^15 ≤ 1530249^15*5000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3381 5000000000 1530249 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1915970397/5000000000 : ℝ)^19 ≤ (1483544138763/5000000000000 : ℝ)^15 := by
    have hnat : (1915970397 : ℕ)^19*5000000000000^15 ≤ 1483544138763^15*5000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1915970397 5000000000 1483544138763 5000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (757385923/1000000000 : ℝ)^19 ≤ (8791139460619/12500000000000 : ℝ)^15 := by
    have hnat : (757385923 : ℕ)^19*12500000000000^15 ≤ 8791139460619^15*1000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      757385923 1000000000 8791139460619 12500000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-3381/5000000000 : ℝ), (1915970397/5000000000 : ℝ), (757385923/1000000000 : ℝ)] ![(1530249/100000000000000 : ℝ), (1483544138763/5000000000000 : ℝ), (8791139460619/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-3381/5000000000 : ℝ)|^19 ≤ (1530249/100000000000000 : ℝ)^15
        have hw : |(-3381/5000000000 : ℝ)|=(3381/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1915970397/5000000000 : ℝ)|^19 ≤ (1483544138763/5000000000000 : ℝ)^15
        have hw : |(1915970397/5000000000 : ℝ)|=(1915970397/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(757385923/1000000000 : ℝ)|^19 ≤ (8791139460619/12500000000000 : ℝ)^15
        have hw : |(757385923/1000000000 : ℝ)|=(757385923/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c315082_s0_21 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-5797304703/10000000000 : ℝ)*x 0 + (41471551/156250000 : ℝ)*x 1 + (3990758213/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5797304703/10000000000 : ℝ)^19 ≤ (6266087294299/12500000000000 : ℝ)^15 := by
    have hnat : (5797304703 : ℕ)^19*12500000000000^15 ≤ 6266087294299^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5797304703 10000000000 6266087294299 12500000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (41471551/156250000 : ℝ)^19 ≤ (18634238614101/100000000000000 : ℝ)^15 := by
    have hnat : (41471551 : ℕ)^19*100000000000000^15 ≤ 18634238614101^15*156250000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      41471551 156250000 18634238614101 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3990758213/10000000000 : ℝ)^19 ≤ (12201977741/39062500000 : ℝ)^15 := by
    have hnat : (3990758213 : ℕ)^19*39062500000^15 ≤ 12201977741^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3990758213 10000000000 12201977741 39062500000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-5797304703/10000000000 : ℝ), (41471551/156250000 : ℝ), (3990758213/10000000000 : ℝ)] ![(6266087294299/12500000000000 : ℝ), (18634238614101/100000000000000 : ℝ), (12201977741/39062500000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-5797304703/10000000000 : ℝ)|^19 ≤ (6266087294299/12500000000000 : ℝ)^15
        have hw : |(-5797304703/10000000000 : ℝ)|=(5797304703/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(41471551/156250000 : ℝ)|^19 ≤ (18634238614101/100000000000000 : ℝ)^15
        have hw : |(41471551/156250000 : ℝ)|=(41471551/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3990758213/10000000000 : ℝ)|^19 ≤ (12201977741/39062500000 : ℝ)^15
        have hw : |(3990758213/10000000000 : ℝ)|=(3990758213/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c315082_s0_22 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (4006424863/10000000000 : ℝ)*x 0 + (-45004163/156250000 : ℝ)*x 1 + (1399142447/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4006424863/10000000000 : ℝ)^19 ≤ (15696236749373/50000000000000 : ℝ)^15 := by
    have hnat : (4006424863 : ℕ)^19*50000000000000^15 ≤ 15696236749373^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4006424863 10000000000 15696236749373 50000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (45004163/156250000 : ℝ)^19 ≤ (20667187192019/100000000000000 : ℝ)^15 := by
    have hnat : (45004163 : ℕ)^19*100000000000000^15 ≤ 20667187192019^15*156250000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      45004163 156250000 20667187192019 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1399142447/2500000000 : ℝ)^19 ≤ (23970169643889/50000000000000 : ℝ)^15 := by
    have hnat : (1399142447 : ℕ)^19*50000000000000^15 ≤ 23970169643889^15*2500000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1399142447 2500000000 23970169643889 50000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4006424863/10000000000 : ℝ), (-45004163/156250000 : ℝ), (1399142447/2500000000 : ℝ)] ![(15696236749373/50000000000000 : ℝ), (20667187192019/100000000000000 : ℝ), (23970169643889/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4006424863/10000000000 : ℝ)|^19 ≤ (15696236749373/50000000000000 : ℝ)^15
        have hw : |(4006424863/10000000000 : ℝ)|=(4006424863/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-45004163/156250000 : ℝ)|^19 ≤ (20667187192019/100000000000000 : ℝ)^15
        have hw : |(-45004163/156250000 : ℝ)|=(45004163/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1399142447/2500000000 : ℝ)|^19 ≤ (23970169643889/50000000000000 : ℝ)^15
        have hw : |(1399142447/2500000000 : ℝ)|=(1399142447/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c315082_s0_23 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (7952587201/10000000000 : ℝ)*x 0 + (3281691221/10000000000 : ℝ)*x 1 + (-222306427/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (7952587201/10000000000 : ℝ)^19 ≤ (74813049422981/100000000000000 : ℝ)^15 := by
    have hnat : (7952587201 : ℕ)^19*100000000000000^15 ≤ 74813049422981^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7952587201 10000000000 74813049422981 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3281691221/10000000000 : ℝ)^19 ≤ (1523832119119/6250000000000 : ℝ)^15 := by
    have hnat : (3281691221 : ℕ)^19*6250000000000^15 ≤ 1523832119119^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3281691221 10000000000 1523832119119 6250000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (222306427/10000000000 : ℝ)^19 ≤ (805636665983/100000000000000 : ℝ)^15 := by
    have hnat : (222306427 : ℕ)^19*100000000000000^15 ≤ 805636665983^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      222306427 10000000000 805636665983 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(7952587201/10000000000 : ℝ), (3281691221/10000000000 : ℝ), (-222306427/10000000000 : ℝ)] ![(74813049422981/100000000000000 : ℝ), (1523832119119/6250000000000 : ℝ), (805636665983/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(7952587201/10000000000 : ℝ)|^19 ≤ (74813049422981/100000000000000 : ℝ)^15
        have hw : |(7952587201/10000000000 : ℝ)|=(7952587201/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3281691221/10000000000 : ℝ)|^19 ≤ (1523832119119/6250000000000 : ℝ)^15
        have hw : |(3281691221/10000000000 : ℝ)|=(3281691221/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-222306427/10000000000 : ℝ)|^19 ≤ (805636665983/100000000000000 : ℝ)^15
        have hw : |(-222306427/10000000000 : ℝ)|=(222306427/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c315082_s0_27 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-35508091/10000000000 : ℝ)*x 0 + (7433647343/10000000000 : ℝ)*x 1 + (3990758213/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (35508091/10000000000 : ℝ)^19 ≤ (78900776503/100000000000000 : ℝ)^15 := by
    have hnat : (35508091 : ℕ)^19*100000000000000^15 ≤ 78900776503^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      35508091 10000000000 78900776503 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (7433647343/10000000000 : ℝ)^19 ≤ (13736807240189/20000000000000 : ℝ)^15 := by
    have hnat : (7433647343 : ℕ)^19*20000000000000^15 ≤ 13736807240189^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7433647343 10000000000 13736807240189 20000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3990758213/10000000000 : ℝ)^19 ≤ (12201977741/39062500000 : ℝ)^15 := by
    have hnat : (3990758213 : ℕ)^19*39062500000^15 ≤ 12201977741^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3990758213 10000000000 12201977741 39062500000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-35508091/10000000000 : ℝ), (7433647343/10000000000 : ℝ), (3990758213/10000000000 : ℝ)] ![(78900776503/100000000000000 : ℝ), (13736807240189/20000000000000 : ℝ), (12201977741/39062500000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-35508091/10000000000 : ℝ)|^19 ≤ (78900776503/100000000000000 : ℝ)^15
        have hw : |(-35508091/10000000000 : ℝ)|=(35508091/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(7433647343/10000000000 : ℝ)|^19 ≤ (13736807240189/20000000000000 : ℝ)^15
        have hw : |(7433647343/10000000000 : ℝ)|=(7433647343/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3990758213/10000000000 : ℝ)|^19 ≤ (12201977741/39062500000 : ℝ)^15
        have hw : |(3990758213/10000000000 : ℝ)|=(3990758213/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c315082_s1_0 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-1968412851/5000000000 : ℝ)*x 0 + (664390351/2000000000 : ℝ)*x 1 + (660048481/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1968412851/5000000000 : ℝ)^19 ≤ (30703308100881/100000000000000 : ℝ)^15 := by
    have hnat : (1968412851 : ℕ)^19*100000000000000^15 ≤ 30703308100881^15*5000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1968412851 5000000000 30703308100881 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (664390351/2000000000 : ℝ)^19 ≤ (24760811450721/100000000000000 : ℝ)^15 := by
    have hnat : (664390351 : ℕ)^19*100000000000000^15 ≤ 24760811450721^15*2000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      664390351 2000000000 24760811450721 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (660048481/1250000000 : ℝ)^19 ≤ (8907176087321/20000000000000 : ℝ)^15 := by
    have hnat : (660048481 : ℕ)^19*20000000000000^15 ≤ 8907176087321^15*1250000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      660048481 1250000000 8907176087321 20000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1968412851/5000000000 : ℝ), (664390351/2000000000 : ℝ), (660048481/1250000000 : ℝ)] ![(30703308100881/100000000000000 : ℝ), (24760811450721/100000000000000 : ℝ), (8907176087321/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1968412851/5000000000 : ℝ)|^19 ≤ (30703308100881/100000000000000 : ℝ)^15
        have hw : |(-1968412851/5000000000 : ℝ)|=(1968412851/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(664390351/2000000000 : ℝ)|^19 ≤ (24760811450721/100000000000000 : ℝ)^15
        have hw : |(664390351/2000000000 : ℝ)|=(664390351/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(660048481/1250000000 : ℝ)|^19 ≤ (8907176087321/20000000000000 : ℝ)^15
        have hw : |(660048481/1250000000 : ℝ)|=(660048481/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c315082_s1_1 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (4166261173/10000000000 : ℝ)*x 0 + (-336512631/1000000000 : ℝ)*x 1 + (314171307/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4166261173/10000000000 : ℝ)^19 ≤ (32987207757459/100000000000000 : ℝ)^15 := by
    have hnat : (4166261173 : ℕ)^19*100000000000000^15 ≤ 32987207757459^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4166261173 10000000000 32987207757459 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (336512631/1000000000 : ℝ)^19 ≤ (25169141487517/100000000000000 : ℝ)^15 := by
    have hnat : (336512631 : ℕ)^19*100000000000000^15 ≤ 25169141487517^15*1000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      336512631 1000000000 25169141487517 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (314171307/625000000 : ℝ)^19 ≤ (41843650739369/100000000000000 : ℝ)^15 := by
    have hnat : (314171307 : ℕ)^19*100000000000000^15 ≤ 41843650739369^15*625000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      314171307 625000000 41843650739369 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4166261173/10000000000 : ℝ), (-336512631/1000000000 : ℝ), (314171307/625000000 : ℝ)] ![(32987207757459/100000000000000 : ℝ), (25169141487517/100000000000000 : ℝ), (41843650739369/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4166261173/10000000000 : ℝ)|^19 ≤ (32987207757459/100000000000000 : ℝ)^15
        have hw : |(4166261173/10000000000 : ℝ)|=(4166261173/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-336512631/1000000000 : ℝ)|^19 ≤ (25169141487517/100000000000000 : ℝ)^15
        have hw : |(-336512631/1000000000 : ℝ)|=(336512631/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(314171307/625000000 : ℝ)|^19 ≤ (41843650739369/100000000000000 : ℝ)^15
        have hw : |(314171307/625000000 : ℝ)|=(314171307/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c315082_s1_2 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (686476103/1250000000 : ℝ)*x 0 + (5284045141/10000000000 : ℝ)*x 1 + (-180494099/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (686476103/1250000000 : ℝ)^19 ≤ (46806502062313/100000000000000 : ℝ)^15 := by
    have hnat : (686476103 : ℕ)^19*100000000000000^15 ≤ 46806502062313^15*1250000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      686476103 1250000000 46806502062313 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5284045141/10000000000 : ℝ)^19 ≤ (44574956104887/100000000000000 : ℝ)^15 := by
    have hnat : (5284045141 : ℕ)^19*100000000000000^15 ≤ 44574956104887^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5284045141 10000000000 44574956104887 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (180494099/1250000000 : ℝ)^19 ≤ (1723708364521/20000000000000 : ℝ)^15 := by
    have hnat : (180494099 : ℕ)^19*20000000000000^15 ≤ 1723708364521^15*1250000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      180494099 1250000000 1723708364521 20000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(686476103/1250000000 : ℝ), (5284045141/10000000000 : ℝ), (-180494099/1250000000 : ℝ)] ![(46806502062313/100000000000000 : ℝ), (44574956104887/100000000000000 : ℝ), (1723708364521/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(686476103/1250000000 : ℝ)|^19 ≤ (46806502062313/100000000000000 : ℝ)^15
        have hw : |(686476103/1250000000 : ℝ)|=(686476103/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5284045141/10000000000 : ℝ)|^19 ≤ (44574956104887/100000000000000 : ℝ)^15
        have hw : |(5284045141/10000000000 : ℝ)|=(5284045141/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-180494099/1250000000 : ℝ)|^19 ≤ (1723708364521/20000000000000 : ℝ)^15
        have hw : |(-180494099/1250000000 : ℝ)|=(180494099/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c315082_s1_6 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (586777789/5000000000 : ℝ)*x 0 + (5205636209/10000000000 : ℝ)*x 1 + (2876016841/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (586777789/5000000000 : ℝ)^19 ≤ (25889957643/390625000000 : ℝ)^15 := by
    have hnat : (586777789 : ℕ)^19*390625000000^15 ≤ 25889957643^15*5000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      586777789 5000000000 25889957643 390625000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5205636209/10000000000 : ℝ)^19 ≤ (43738796782539/100000000000000 : ℝ)^15 := by
    have hnat : (5205636209 : ℕ)^19*100000000000000^15 ≤ 43738796782539^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5205636209 10000000000 43738796782539 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2876016841/5000000000 : ℝ)^19 ≤ (6204171755567/12500000000000 : ℝ)^15 := by
    have hnat : (2876016841 : ℕ)^19*12500000000000^15 ≤ 6204171755567^15*5000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2876016841 5000000000 6204171755567 12500000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(586777789/5000000000 : ℝ), (5205636209/10000000000 : ℝ), (2876016841/5000000000 : ℝ)] ![(25889957643/390625000000 : ℝ), (43738796782539/100000000000000 : ℝ), (6204171755567/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(586777789/5000000000 : ℝ)|^19 ≤ (25889957643/390625000000 : ℝ)^15
        have hw : |(586777789/5000000000 : ℝ)|=(586777789/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5205636209/10000000000 : ℝ)|^19 ≤ (43738796782539/100000000000000 : ℝ)^15
        have hw : |(5205636209/10000000000 : ℝ)|=(5205636209/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2876016841/5000000000 : ℝ)|^19 ≤ (6204171755567/12500000000000 : ℝ)^15
        have hw : |(2876016841/5000000000 : ℝ)|=(2876016841/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c315082 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (174659/100000 : ℝ) (34911/20000 : ℝ) (15821/20000 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![false, true, true]]) : False := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (15821/20000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (15821/20000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (15821/20000 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (15821/20000 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 0+X 2 0)) ∧ ((-1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 0) ∧ ((-1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (15821/20000 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (15821/20000 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((-1 : ℝ)*(X 0 0+X 1 0)) ∧ ((-1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((-1 : ℝ)*pair X 2 0) ∧ ((-1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base1 : ((1 : ℝ)*N 0+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 0]
  have base7 : ((1 : ℝ)*T) ≤ (34911/20000 : ℝ) := by
    linarith only [f.Tcap]
  have base8 : ((-1 : ℝ)*X 0 0+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 0).1]
  have base19 : ((1 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 2).2]
  have base21 : ((1 : ℝ)*X 2 0+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 0).2]
  have base29 : ((1 : ℝ)*X 0 1+(1 : ℝ)*X 1 1+(1 : ℝ)*X 2 1+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [(f.column 1).2]
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base44 : ((-1 : ℝ)*N 1+(1 : ℝ)*P 1+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ptotal 1]
  have base49 : ((1 : ℝ)*X 0 0+(1 : ℝ)*X 2 0) ≤ (0 : ℝ) := by
    linarith only [order1.1]
  have base50 : ((-1 : ℝ)*X 0 0+(-1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 0+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.2.1]
  have base53 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 1+(1 : ℝ)*P 2) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 2,f.sum]
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
  have s0_pow0 : (1 : ℝ) ^ (75/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^75 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^75*1^16 ≤ 1^16*1^75 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 75 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 75 16 (by norm_num) hpowers
    exact h
  have s0_corner0a : (2 : ℝ) ≤ (5796818954377947/5000000000000000 : ℝ) ^ (75/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (5796818954377947/5000000000000000 : ℝ)^75 := by
      have hnat : (2 : ℕ)^16*5000000000000000^75 ≤ 5796818954377947^75*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 5796818954377947 5000000000000000 16 75 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5796818954377947/5000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 75 16 (by norm_num) hpowers
    exact h
  have s0_corner0b : (3 : ℝ) ≤ (3160282282318219/2500000000000000 : ℝ) ^ (75/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (3160282282318219/2500000000000000 : ℝ)^75 := by
      have hnat : (3 : ℕ)^16*2500000000000000^75 ≤ 3160282282318219^75*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 3160282282318219 2500000000000000 16 75 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (3160282282318219/2500000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 75 16 (by norm_num) hpowers
    exact h
  have major_s0_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(796818954377947/5000000000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(523745610258491/5000000000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (75/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (796818954377947/5000000000000000 : ℝ)) (beta := (523745610258491/5000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow0,s0_corner0a]) (by linarith only [s0_pow0,s0_corner0b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![false, true, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (1 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order0.2.2])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(796818954377947/5000000000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(523745610258491/5000000000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow1 : (1 : ℝ) ^ (75/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^75 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^75*1^16 ≤ 1^16*1^75 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 75 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 75 16 (by norm_num) hpowers
    exact h
  have s0_corner1a : (2 : ℝ) ≤ (5796818954377947/5000000000000000 : ℝ) ^ (75/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (5796818954377947/5000000000000000 : ℝ)^75 := by
      have hnat : (2 : ℕ)^16*5000000000000000^75 ≤ 5796818954377947^75*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 5796818954377947 5000000000000000 16 75 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5796818954377947/5000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 75 16 (by norm_num) hpowers
    exact h
  have s0_corner1b : (3 : ℝ) ≤ (3160282282318219/2500000000000000 : ℝ) ^ (75/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (3160282282318219/2500000000000000 : ℝ)^75 := by
      have hnat : (3 : ℕ)^16*2500000000000000^75 ≤ 3160282282318219^75*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 3160282282318219 2500000000000000 16 75 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (3160282282318219/2500000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 75 16 (by norm_num) hpowers
    exact h
  have major_s0_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(796818954377947/5000000000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2))+(523745610258491/5000000000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 2 0)) := by
    have hh := chart_majorant (a := (75/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (796818954377947/5000000000000000 : ℝ)) (beta := (523745610258491/5000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow1,s0_corner1a]) (by linarith only [s0_pow1,s0_corner1b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![false, true, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 2) ≤ (1 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order1.2.2])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(796818954377947/5000000000000000 : ℝ)*((1 : ℝ)*pair X 1 2)+(523745610258491/5000000000000000 : ℝ)*((-1 : ℝ)*pair X 1 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow2 : (1 : ℝ) ^ (75/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^75 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^75*1^16 ≤ 1^16*1^75 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 75 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 75 16 (by norm_num) hpowers
    exact h
  have s0_corner2a : (2 : ℝ) ≤ (5796818954377947/5000000000000000 : ℝ) ^ (75/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (5796818954377947/5000000000000000 : ℝ)^75 := by
      have hnat : (2 : ℕ)^16*5000000000000000^75 ≤ 5796818954377947^75*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 5796818954377947 5000000000000000 16 75 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5796818954377947/5000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 75 16 (by norm_num) hpowers
    exact h
  have s0_corner2b : (3 : ℝ) ≤ (3160282282318219/2500000000000000 : ℝ) ^ (75/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (3160282282318219/2500000000000000 : ℝ)^75 := by
      have hnat : (3 : ℕ)^16*2500000000000000^75 ≤ 3160282282318219^75*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 3160282282318219 2500000000000000 16 75 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (3160282282318219/2500000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 75 16 (by norm_num) hpowers
    exact h
  have major_s0_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(796818954377947/5000000000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 1 0))+(523745610258491/5000000000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (75/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (796818954377947/5000000000000000 : ℝ)) (beta := (523745610258491/5000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow2,s0_corner2a]) (by linarith only [s0_pow2,s0_corner2b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![false, true, true]] hX 2 (by
        change ((-1 : ℝ)*pair X 2 0) ≤ (1 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order2.2.2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(796818954377947/5000000000000000 : ℝ)*((-1 : ℝ)*pair X 2 0)+(523745610258491/5000000000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s0_0 : ((-3515813083/10000000000 : ℝ)*X 0 0+(77182843/250000000 : ℝ)*X 0 1+(2930533249/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c315082_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_1 : ((4212455731/10000000000 : ℝ)*X 1 0+(-698338497/2500000000 : ℝ)*X 1 1+(54790097/100000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c315082_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_7 : ((-377816109/1250000000 : ℝ)*X 0 0+(362361059/2500000000 : ℝ)*X 0 1+(3746154719/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c315082_s0_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_8 : ((864482137/2000000000 : ℝ)*X 1 0+(-284023193/5000000000 : ℝ)*X 1 1+(6925777743/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c315082_s0_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_9 : ((1811194753/5000000000 : ℝ)*X 2 0+(3846326113/5000000000 : ℝ)*X 2 1+(-92673927/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c315082_s0_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_13 : ((2417297/625000000 : ℝ)*X 0 0+(171005499/200000000 : ℝ)*X 0 1+(514409127/2000000000 : ℝ)*X 0 2+(2417297/625000000 : ℝ)*X 1 0+(171005499/200000000 : ℝ)*X 1 1+(514409127/2000000000 : ℝ)*X 1 2+(2417297/625000000 : ℝ)*X 2 0+(171005499/200000000 : ℝ)*X 2 1+(514409127/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c315082_s0_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_14 : ((-532245979/2000000000 : ℝ)*X 0 0+(34947891/200000000 : ℝ)*X 0 1+(757385923/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c315082_s0_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_15 : ((7627858229/10000000000 : ℝ)*X 1 0+(-1968745771/10000000000 : ℝ)*X 1 1+(149047129/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c315082_s0_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_16 : ((8424428403/10000000000 : ℝ)*X 2 0+(2614049527/10000000000 : ℝ)*X 2 1+(-19560877/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c315082_s0_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_20 : ((-3381/5000000000 : ℝ)*X 0 0+(1915970397/5000000000 : ℝ)*X 0 1+(757385923/1000000000 : ℝ)*X 0 2+(-3381/5000000000 : ℝ)*X 1 0+(1915970397/5000000000 : ℝ)*X 1 1+(757385923/1000000000 : ℝ)*X 1 2+(-3381/5000000000 : ℝ)*X 2 0+(1915970397/5000000000 : ℝ)*X 2 1+(757385923/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c315082_s0_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_21 : ((-5797304703/10000000000 : ℝ)*X 0 0+(41471551/156250000 : ℝ)*X 0 1+(3990758213/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c315082_s0_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_22 : ((4006424863/10000000000 : ℝ)*X 1 0+(-45004163/156250000 : ℝ)*X 1 1+(1399142447/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c315082_s0_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_23 : ((7952587201/10000000000 : ℝ)*X 2 0+(3281691221/10000000000 : ℝ)*X 2 1+(-222306427/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c315082_s0_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_27 : ((-35508091/10000000000 : ℝ)*X 0 0+(7433647343/10000000000 : ℝ)*X 0 1+(3990758213/10000000000 : ℝ)*X 0 2+(-35508091/10000000000 : ℝ)*X 1 0+(7433647343/10000000000 : ℝ)*X 1 1+(3990758213/10000000000 : ℝ)*X 1 2+(-35508091/10000000000 : ℝ)*X 2 0+(7433647343/10000000000 : ℝ)*X 2 1+(3990758213/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c315082_s0_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s0_0 : (0 : ℝ) ≤ ((68351/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(68351/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (5136882892821000267/400000000000000000000000 : ℝ) := by norm_num
    linear_combination (206903330087/250000000000 : ℝ)*(base7) + (69572853423/1000000000000 : ℝ)*(base49) + (58923194923/250000000000 : ℝ)*(base53) + (1773468699/500000000000 : ℝ)*(base60) + (773822731233/500000000000 : ℝ)*(major_s0_0) + (773822731233/500000000000 : ℝ)*(major_s0_1) + (655976341387/500000000000 : ℝ)*(major_s0_2) + (3732857/500000000000 : ℝ)*(sp_s0_0) + (59670037709/40000000000 : ℝ)*(sp_s0_7) + (149195159807/100000000000 : ℝ)*(sp_s0_8) + (863822188881/500000000000 : ℝ)*(sp_s0_9) + (342740414223/200000000000 : ℝ)*(sp_s0_13) + (193189631/1000000000000 : ℝ)*(sp_s0_14) + (6705217/1000000000000 : ℝ)*(sp_s0_27) + (886095455983/1000000000000 : ℝ)*(f.failure) + (863822188881/500000000000 : ℝ)*(f.sum) + (14990655789527/625000000000000000000000000 : ℝ)*base63 + (1669570446282983/2500000000000000000000000000 : ℝ)*base64 + (439245541181349/2500000000000000000000000000 : ℝ)*base66 + (45335916942489/2500000000000000000000000000 : ℝ)*base68 + (395027262616083/625000000000000000000000000 : ℝ)*base70 + (504097814850597/2500000000000000000000000000 : ℝ)*base72 + (501557924600597/2500000000000000000000000000 : ℝ)*base75 + (902218889931349/2500000000000000000000000000 : ℝ)*base76 + (288991521015973/1250000000000000000000000000 : ℝ)*base78 + (65203/100000000000000000 : ℝ)*base86 + (65203/100000000000000000 : ℝ)*base88 + (65203/100000000000000000 : ℝ)*base90 + (1/1000000000000 : ℝ)*base93 + hcertificate_margin
  have ratio_s0_1 : (0 : ℝ) ≤ ((79119/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(79119/100000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (3040801554916392759081/500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (3077829651/40000000000 : ℝ)*(base1) + (282927500347/250000000000 : ℝ)*(base7) + (112126691/2500000000 : ℝ)*(base39) + (3482749/1000000000000 : ℝ)*(base53) + (54223205767/1000000000000 : ℝ)*(base60) + (225651700953/125000000000 : ℝ)*(major_s0_0) + (225651700953/125000000000 : ℝ)*(major_s0_1) + (14441680999/8000000000 : ℝ)*(major_s0_2) + (2267069/50000000000 : ℝ)*(sp_s0_7) + (1995272033487/1000000000000 : ℝ)*(sp_s0_14) + (239796454199/125000000000 : ℝ)*(sp_s0_15) + (479588997107/250000000000 : ℝ)*(sp_s0_16) + (130520554219/62500000000 : ℝ)*(sp_s0_20) + (19127913/1000000000000 : ℝ)*(sp_s0_23) + (1033564607391/1000000000000 : ℝ)*(f.failure) + (1918375116341/1000000000000 : ℝ)*(f.sum) + (847693467967009/5000000000000000000000000000 : ℝ)*base62 + (16136394288509/40000000000000000000000000 : ℝ)*base65 + (330431496458491/625000000000000000000000000 : ℝ)*base67 + (16523079390947/40000000000000000000000000 : ℝ)*base69 + (367282423731553/5000000000000000000000000000 : ℝ)*base71 + (154351423041923/625000000000000000000000000 : ℝ)*base73 + (111618592145577/625000000000000000000000000 : ℝ)*base75 + (199797613020991/625000000000000000000000000 : ℝ)*base77 + (79887016156457/312500000000000000000000000 : ℝ)*base79 + (95331/100000000000000000 : ℝ)*base86 + (95331/100000000000000000 : ℝ)*base88 + (95331/100000000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s0_2 : (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(36101/50000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(36101/50000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (28540118145017132482173/2500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (36038227643/250000000000 : ℝ)*(base1) + (476711390987/500000000000 : ℝ)*(base7) + (68387439227/1000000000000 : ℝ)*(base39) + (105219802921/200000000000 : ℝ)*(base44) + (2090199366703/1000000000000 : ℝ)*(major_s0_0) + (1564100352099/1000000000000 : ℝ)*(major_s0_1) + (2090199366703/1000000000000 : ℝ)*(major_s0_2) + (163450583/1000000000000 : ℝ)*(sp_s0_1) + (820967/62500000000 : ℝ)*(sp_s0_13) + (7230643/500000000000 : ℝ)*(sp_s0_16) + (2573067237899/1000000000000 : ℝ)*(sp_s0_21) + (95132593107/50000000000 : ℝ)*(sp_s0_22) + (1214449933021/500000000000 : ℝ)*(sp_s0_23) + (739944638179/500000000000 : ℝ)*(sp_s0_27) + (149591444379/125000000000 : ℝ)*(f.failure) + (75903572729/31250000000 : ℝ)*(f.sum) + (21421317964427/100000000000000000000000000 : ℝ)*base62 + (1115063563425173/5000000000000000000000000000 : ℝ)*base65 + (1493883509739247/5000000000000000000000000000 : ℝ)*base66 + (2024949888798741/5000000000000000000000000000 : ℝ)*base68 + (257137408638043/2500000000000000000000000000 : ℝ)*base70 + (1290438868574827/5000000000000000000000000000 : ℝ)*base72 + (4258884037422609/5000000000000000000000000000 : ℝ)*base74 + (255017389701259/5000000000000000000000000000 : ℝ)*base76 + (695655302592963/2500000000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base80 + (4261/12500000000000000 : ℝ)*base87 + (8239/12500000000000000 : ℝ)*base88 + (4261/12500000000000000 : ℝ)*base91 + (1/1000000000000 : ℝ)*base93 + hcertificate_margin
  have s1_pow0 : (68351/100000 : ℝ) ^ (75/16 : ℝ) ≤ (16802217081859493227/100000000000000000000 : ℝ) := by
    have hpowers : (68351/100000 : ℝ)^75 ≤ (16802217081859493227/100000000000000000000 : ℝ)^16 := by
      have hnat : (68351 : ℕ)^75*100000000000000000000^16 ≤ 16802217081859493227^16*100000^75 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        68351 100000 16802217081859493227 100000000000000000000 75 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (68351/100000 : ℝ)) (X := (16802217081859493227/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 75 16 (by norm_num) hpowers
    exact h
  have s1_corner0a : (116802217081859493227/100000000000000000000 : ℝ) ≤ (10336882153777023/10000000000000000 : ℝ) ^ (75/16 : ℝ) := by
    have hpowers : (116802217081859493227/100000000000000000000 : ℝ)^16 ≤ (10336882153777023/10000000000000000 : ℝ)^75 := by
      have hnat : (116802217081859493227 : ℕ)^16*10000000000000000^75 ≤ 10336882153777023^75*100000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        116802217081859493227 100000000000000000000 10336882153777023 10000000000000000 16 75 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10336882153777023/10000000000000000 : ℝ)) (X := (116802217081859493227/100000000000000000000 : ℝ)) (by norm_num) 75 16 (by norm_num) hpowers
    exact h
  have s1_corner0b : (66802217081859493227/50000000000000000000 : ℝ) ≤ (5318777101772549/5000000000000000 : ℝ) ^ (75/16 : ℝ) := by
    have hpowers : (66802217081859493227/50000000000000000000 : ℝ)^16 ≤ (5318777101772549/5000000000000000 : ℝ)^75 := by
      have hnat : (66802217081859493227 : ℕ)^16*5000000000000000^75 ≤ 5318777101772549^75*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        66802217081859493227 50000000000000000000 5318777101772549 5000000000000000 16 75 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5318777101772549/5000000000000000 : ℝ)) (X := (66802217081859493227/50000000000000000000 : ℝ)) (by norm_num) 75 16 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(336882153777023/6835100000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(12026881990723/273404000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (75/16 : ℝ)) (rho := (68351/100000 : ℝ)) (alpha := (336882153777023/6835100000000000 : ℝ)) (beta := (12026881990723/273404000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![false, true, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (68351/100000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(336882153777023/6835100000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(12026881990723/273404000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (79119/100000 : ℝ) ^ (75/16 : ℝ) ≤ (8339330951509519959/25000000000000000000 : ℝ) := by
    have hpowers : (79119/100000 : ℝ)^75 ≤ (8339330951509519959/25000000000000000000 : ℝ)^16 := by
      have hnat : (79119 : ℕ)^75*25000000000000000000^16 ≤ 8339330951509519959^16*100000^75 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        79119 100000 8339330951509519959 25000000000000000000 75 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (79119/100000 : ℝ)) (X := (8339330951509519959/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 75 16 (by norm_num) hpowers
    exact h
  have s1_corner1a : (33339330951509519959/25000000000000000000 : ℝ) ≤ (2126670768226353/2000000000000000 : ℝ) ^ (75/16 : ℝ) := by
    have hpowers : (33339330951509519959/25000000000000000000 : ℝ)^16 ≤ (2126670768226353/2000000000000000 : ℝ)^75 := by
      have hnat : (33339330951509519959 : ℕ)^16*2000000000000000^75 ≤ 2126670768226353^75*25000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        33339330951509519959 25000000000000000000 2126670768226353 2000000000000000 16 75 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2126670768226353/2000000000000000 : ℝ)) (X := (33339330951509519959/25000000000000000000 : ℝ)) (by norm_num) 75 16 (by norm_num) hpowers
    exact h
  have s1_corner1b : (20839330951509519959/12500000000000000000 : ℝ) ≤ (5576021070725851/5000000000000000 : ℝ) ^ (75/16 : ℝ) := by
    have hpowers : (20839330951509519959/12500000000000000000 : ℝ)^16 ≤ (5576021070725851/5000000000000000 : ℝ)^75 := by
      have hnat : (20839330951509519959 : ℕ)^16*5000000000000000^75 ≤ 5576021070725851^75*12500000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20839330951509519959 12500000000000000000 5576021070725851 5000000000000000 16 75 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5576021070725851/5000000000000000 : ℝ)) (X := (20839330951509519959/12500000000000000000 : ℝ)) (by norm_num) 75 16 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(126670768226353/1582380000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2))+(518688300319937/7911900000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 2 0)) := by
    have hh := chart_majorant (a := (75/16 : ℝ)) (rho := (79119/100000 : ℝ)) (alpha := (126670768226353/1582380000000000 : ℝ)) (beta := (518688300319937/7911900000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![false, true, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 2) ≤ (79119/100000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(126670768226353/1582380000000000 : ℝ)*((1 : ℝ)*pair X 1 2)+(518688300319937/7911900000000000 : ℝ)*((-1 : ℝ)*pair X 1 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (36101/50000 : ℝ) ^ (75/16 : ℝ) ≤ (10862242876968734573/50000000000000000000 : ℝ) := by
    have hpowers : (36101/50000 : ℝ)^75 ≤ (10862242876968734573/50000000000000000000 : ℝ)^16 := by
      have hnat : (36101 : ℕ)^75*50000000000000000000^16 ≤ 10862242876968734573^16*50000^75 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        36101 50000 10862242876968734573 50000000000000000000 75 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (36101/50000 : ℝ)) (X := (10862242876968734573/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 75 16 (by norm_num) hpowers
    exact h
  have s1_corner2a : (60862242876968734573/50000000000000000000 : ℝ) ≤ (162942354810097/156250000000000 : ℝ) ^ (75/16 : ℝ) := by
    have hpowers : (60862242876968734573/50000000000000000000 : ℝ)^16 ≤ (162942354810097/156250000000000 : ℝ)^75 := by
      have hnat : (60862242876968734573 : ℕ)^16*156250000000000^75 ≤ 162942354810097^75*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        60862242876968734573 50000000000000000000 162942354810097 156250000000000 16 75 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (162942354810097/156250000000000 : ℝ)) (X := (60862242876968734573/50000000000000000000 : ℝ)) (by norm_num) 75 16 (by norm_num) hpowers
    exact h
  have s1_corner2b : (35862242876968734573/25000000000000000000 : ℝ) ≤ (10800125122664219/10000000000000000 : ℝ) ^ (75/16 : ℝ) := by
    have hpowers : (35862242876968734573/25000000000000000000 : ℝ)^16 ≤ (10800125122664219/10000000000000000 : ℝ)^75 := by
      have hnat : (35862242876968734573 : ℕ)^16*10000000000000000^75 ≤ 10800125122664219^75*25000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        35862242876968734573 25000000000000000000 10800125122664219 10000000000000000 16 75 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10800125122664219/10000000000000000 : ℝ)) (X := (35862242876968734573/25000000000000000000 : ℝ)) (by norm_num) 75 16 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(6692354810097/112815625000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 1 0))+(371814414818011/7220200000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (75/16 : ℝ)) (rho := (36101/50000 : ℝ)) (alpha := (6692354810097/112815625000000 : ℝ)) (beta := (371814414818011/7220200000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![false, true, true]] hX 2 (by
        change ((-1 : ℝ)*pair X 2 0) ≤ (36101/50000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(6692354810097/112815625000000 : ℝ)*((-1 : ℝ)*pair X 2 0)+(371814414818011/7220200000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-1968412851/5000000000 : ℝ)*X 0 0+(664390351/2000000000 : ℝ)*X 0 1+(660048481/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c315082_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_1 : ((4166261173/10000000000 : ℝ)*X 1 0+(-336512631/1000000000 : ℝ)*X 1 1+(314171307/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c315082_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((686476103/1250000000 : ℝ)*X 2 0+(5284045141/10000000000 : ℝ)*X 2 1+(-180494099/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c315082_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_6 : ((586777789/5000000000 : ℝ)*X 0 0+(5205636209/10000000000 : ℝ)*X 0 1+(2876016841/5000000000 : ℝ)*X 0 2+(586777789/5000000000 : ℝ)*X 1 0+(5205636209/10000000000 : ℝ)*X 1 1+(2876016841/5000000000 : ℝ)*X 1 2+(586777789/5000000000 : ℝ)*X 2 0+(5205636209/10000000000 : ℝ)*X 2 1+(2876016841/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c315082_s1_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have hsep : (-373977/50000 : ℝ) < ((-174659/100000 : ℝ)*P 0+(-174659/100000 : ℝ)*P 1+(-174659/100000 : ℝ)*P 2+(1 : ℝ)*T) := by
    have hcertificate_margin : (-373977/50000 : ℝ) < (-4847846554623747567825317273858154467/650764179412230000000000000000000000 : ℝ) := by norm_num
    linear_combination (3241/200000000000 : ℝ)*(base8) + (3663/200000000000 : ℝ)*(base19) + (21721/500000000000 : ℝ)*(base21) + (4717/1000000000000 : ℝ)*(base29) + (4319/500000000000 : ℝ)*(base40) + (151029810877/1000000000000 : ℝ)*(base49) + (23721/1000000000000 : ℝ)*(base50) + (491077126187/1000000000000 : ℝ)*(base60) + (174659/100000 : ℝ)*(major_s1_0) + (174659/100000 : ℝ)*(major_s1_1) + (174659/100000 : ℝ)*(major_s1_2) + (155197236967/62500000000 : ℝ)*(sp_s1_0) + (1241577894681/500000000000 : ℝ)*(sp_s1_1) + (620788941059/250000000000 : ℝ)*(sp_s1_2) + (999999995283/1000000000000 : ℝ)*(sp_s1_6) + (1241577903839/500000000000 : ℝ)*(f.sum) + (2932056300299542937/2856275019000000000000000000000 : ℝ)*base62 + (211979735738207/361010000000000000000000000 : ℝ)*base64 + (30447689127589/395595000000000000000000000 : ℝ)*base66 + (652095833001/1805050000000000000000000 : ℝ)*base68 + (27158212116134408077/24675394510000000000000000000000 : ℝ)*base70 + (14381640456947/13670200000000000000000000 : ℝ)*base73 + (194178116544761/395595000000000000000000000 : ℝ)*base74 + (494483017941473/683510000000000000000000000 : ℝ)*base76 + (5582111559878662357/27039313845000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base80 + (1/1000000000000 : ℝ)*base82 + hcertificate_margin
  linarith only [hsep,f.failure]

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem collision_support_c315084_s0_0 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-829147229/2000000000 : ℝ)*x 0 + (-1007099121/2000000000 : ℝ)*x 1 + (105534011/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (829147229/2000000000 : ℝ)^19 ≤ (3278149583943/10000000000000 : ℝ)^15 := by
    have hnat : (829147229 : ℕ)^19*10000000000000^15 ≤ 3278149583943^15*2000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      829147229 2000000000 3278149583943 10000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1007099121/2000000000 : ℝ)^19 ≤ (41935981651517/100000000000000 : ℝ)^15 := by
    have hnat : (1007099121 : ℕ)^19*100000000000000^15 ≤ 41935981651517^15*2000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1007099121 2000000000 41935981651517 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (105534011/312500000 : ℝ)^19 ≤ (12641261247049/50000000000000 : ℝ)^15 := by
    have hnat : (105534011 : ℕ)^19*50000000000000^15 ≤ 12641261247049^15*312500000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      105534011 312500000 12641261247049 50000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-829147229/2000000000 : ℝ), (-1007099121/2000000000 : ℝ), (105534011/312500000 : ℝ)] ![(3278149583943/10000000000000 : ℝ), (41935981651517/100000000000000 : ℝ), (12641261247049/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-829147229/2000000000 : ℝ)|^19 ≤ (3278149583943/10000000000000 : ℝ)^15
        have hw : |(-829147229/2000000000 : ℝ)|=(829147229/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1007099121/2000000000 : ℝ)|^19 ≤ (41935981651517/100000000000000 : ℝ)^15
        have hw : |(-1007099121/2000000000 : ℝ)|=(1007099121/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(105534011/312500000 : ℝ)|^19 ≤ (12641261247049/50000000000000 : ℝ)^15
        have hw : |(105534011/312500000 : ℝ)|=(105534011/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c315084_s0_1 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (105534011/312500000 : ℝ)*x 0 + (829147229/2000000000 : ℝ)*x 1 + (1007099121/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (105534011/312500000 : ℝ)^19 ≤ (12641261247049/50000000000000 : ℝ)^15 := by
    have hnat : (105534011 : ℕ)^19*50000000000000^15 ≤ 12641261247049^15*312500000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      105534011 312500000 12641261247049 50000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (829147229/2000000000 : ℝ)^19 ≤ (3278149583943/10000000000000 : ℝ)^15 := by
    have hnat : (829147229 : ℕ)^19*10000000000000^15 ≤ 3278149583943^15*2000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      829147229 2000000000 3278149583943 10000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1007099121/2000000000 : ℝ)^19 ≤ (41935981651517/100000000000000 : ℝ)^15 := by
    have hnat : (1007099121 : ℕ)^19*100000000000000^15 ≤ 41935981651517^15*2000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1007099121 2000000000 41935981651517 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(105534011/312500000 : ℝ), (829147229/2000000000 : ℝ), (1007099121/2000000000 : ℝ)] ![(12641261247049/50000000000000 : ℝ), (3278149583943/10000000000000 : ℝ), (41935981651517/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(105534011/312500000 : ℝ)|^19 ≤ (12641261247049/50000000000000 : ℝ)^15
        have hw : |(105534011/312500000 : ℝ)|=(105534011/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(829147229/2000000000 : ℝ)|^19 ≤ (3278149583943/10000000000000 : ℝ)^15
        have hw : |(829147229/2000000000 : ℝ)|=(829147229/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1007099121/2000000000 : ℝ)|^19 ≤ (41935981651517/100000000000000 : ℝ)^15
        have hw : |(1007099121/2000000000 : ℝ)|=(1007099121/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c315084_s0_2 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (1007099121/2000000000 : ℝ)*x 0 + (-105534011/312500000 : ℝ)*x 1 + (-829147229/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1007099121/2000000000 : ℝ)^19 ≤ (41935981651517/100000000000000 : ℝ)^15 := by
    have hnat : (1007099121 : ℕ)^19*100000000000000^15 ≤ 41935981651517^15*2000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1007099121 2000000000 41935981651517 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (105534011/312500000 : ℝ)^19 ≤ (12641261247049/50000000000000 : ℝ)^15 := by
    have hnat : (105534011 : ℕ)^19*50000000000000^15 ≤ 12641261247049^15*312500000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      105534011 312500000 12641261247049 50000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (829147229/2000000000 : ℝ)^19 ≤ (3278149583943/10000000000000 : ℝ)^15 := by
    have hnat : (829147229 : ℕ)^19*10000000000000^15 ≤ 3278149583943^15*2000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      829147229 2000000000 3278149583943 10000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1007099121/2000000000 : ℝ), (-105534011/312500000 : ℝ), (-829147229/2000000000 : ℝ)] ![(41935981651517/100000000000000 : ℝ), (12641261247049/50000000000000 : ℝ), (3278149583943/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1007099121/2000000000 : ℝ)|^19 ≤ (41935981651517/100000000000000 : ℝ)^15
        have hw : |(1007099121/2000000000 : ℝ)|=(1007099121/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-105534011/312500000 : ℝ)|^19 ≤ (12641261247049/50000000000000 : ℝ)^15
        have hw : |(-105534011/312500000 : ℝ)|=(105534011/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-829147229/2000000000 : ℝ)|^19 ≤ (3278149583943/10000000000000 : ℝ)^15
        have hw : |(-829147229/2000000000 : ℝ)|=(829147229/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c315084_s0_6 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (2100367693/5000000000 : ℝ)*x 0 + (-2100367693/5000000000 : ℝ)*x 1 + (2100367693/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2100367693/5000000000 : ℝ)^19 ≤ (8333333332563/25000000000000 : ℝ)^15 := by
    have hnat : (2100367693 : ℕ)^19*25000000000000^15 ≤ 8333333332563^15*5000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2100367693 5000000000 8333333332563 25000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2100367693/5000000000 : ℝ)^19 ≤ (8333333332563/25000000000000 : ℝ)^15 := by
    have hnat : (2100367693 : ℕ)^19*25000000000000^15 ≤ 8333333332563^15*5000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2100367693 5000000000 8333333332563 25000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2100367693/5000000000 : ℝ)^19 ≤ (8333333332563/25000000000000 : ℝ)^15 := by
    have hnat : (2100367693 : ℕ)^19*25000000000000^15 ≤ 8333333332563^15*5000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2100367693 5000000000 8333333332563 25000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2100367693/5000000000 : ℝ), (-2100367693/5000000000 : ℝ), (2100367693/5000000000 : ℝ)] ![(8333333332563/25000000000000 : ℝ), (8333333332563/25000000000000 : ℝ), (8333333332563/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2100367693/5000000000 : ℝ)|^19 ≤ (8333333332563/25000000000000 : ℝ)^15
        have hw : |(2100367693/5000000000 : ℝ)|=(2100367693/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2100367693/5000000000 : ℝ)|^19 ≤ (8333333332563/25000000000000 : ℝ)^15
        have hw : |(-2100367693/5000000000 : ℝ)|=(2100367693/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2100367693/5000000000 : ℝ)|^19 ≤ (8333333332563/25000000000000 : ℝ)^15
        have hw : |(2100367693/5000000000 : ℝ)|=(2100367693/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c315084 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (174659/100000 : ℝ) (34911/20000 : ℝ) (15821/20000 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![true, false, false], ![false, false, true]]) : False := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (15821/20000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (15821/20000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (15821/20000 : ℝ)*P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (15821/20000 : ℝ)*P 1 ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((-1 : ℝ)*(X 0 2+X 2 2)) ∧ ((-1 : ℝ)*(X 0 2+X 2 2)) ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((-1 : ℝ)*pair X 1 2) ∧ ((-1 : ℝ)*pair X 1 2) ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (15821/20000 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (15821/20000 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
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
  have s0_pow0 : (1 : ℝ) ^ (75/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^75 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^75*1^16 ≤ 1^16*1^75 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 75 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 75 16 (by norm_num) hpowers
    exact h
  have s0_corner0a : (2 : ℝ) ≤ (5796818954377947/5000000000000000 : ℝ) ^ (75/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (5796818954377947/5000000000000000 : ℝ)^75 := by
      have hnat : (2 : ℕ)^16*5000000000000000^75 ≤ 5796818954377947^75*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 5796818954377947 5000000000000000 16 75 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5796818954377947/5000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 75 16 (by norm_num) hpowers
    exact h
  have s0_corner0b : (3 : ℝ) ≤ (3160282282318219/2500000000000000 : ℝ) ^ (75/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (3160282282318219/2500000000000000 : ℝ)^75 := by
      have hnat : (3 : ℕ)^16*2500000000000000^75 ≤ 3160282282318219^75*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 3160282282318219 2500000000000000 16 75 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (3160282282318219/2500000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 75 16 (by norm_num) hpowers
    exact h
  have major_s0_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(796818954377947/5000000000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(523745610258491/5000000000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (75/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (796818954377947/5000000000000000 : ℝ)) (beta := (523745610258491/5000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow0,s0_corner0a]) (by linarith only [s0_pow0,s0_corner0b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![true, false, false], ![false, false, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (1 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order0.2.2])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(796818954377947/5000000000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(523745610258491/5000000000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow1 : (1 : ℝ) ^ (75/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^75 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^75*1^16 ≤ 1^16*1^75 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 75 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 75 16 (by norm_num) hpowers
    exact h
  have s0_corner1a : (2 : ℝ) ≤ (5796818954377947/5000000000000000 : ℝ) ^ (75/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (5796818954377947/5000000000000000 : ℝ)^75 := by
      have hnat : (2 : ℕ)^16*5000000000000000^75 ≤ 5796818954377947^75*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 5796818954377947 5000000000000000 16 75 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5796818954377947/5000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 75 16 (by norm_num) hpowers
    exact h
  have s0_corner1b : (3 : ℝ) ≤ (3160282282318219/2500000000000000 : ℝ) ^ (75/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (3160282282318219/2500000000000000 : ℝ)^75 := by
      have hnat : (3 : ℕ)^16*2500000000000000^75 ≤ 3160282282318219^75*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 3160282282318219 2500000000000000 16 75 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (3160282282318219/2500000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 75 16 (by norm_num) hpowers
    exact h
  have major_s0_1 : P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1))+(796818954377947/5000000000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2))+(523745610258491/5000000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0)) := by
    have hh := chart_majorant (a := (75/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (796818954377947/5000000000000000 : ℝ)) (beta := (523745610258491/5000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow1,s0_corner1a]) (by linarith only [s0_pow1,s0_corner1b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![true, false, false], ![false, false, true]] hX 1 (by
        change ((-1 : ℝ)*pair X 1 2) ≤ (1 : ℝ)*((-1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order1.2.2])
    change lpNorm p (pair X 1) ≤ ((-1 : ℝ)*pair X 1 1)+(796818954377947/5000000000000000 : ℝ)*((-1 : ℝ)*pair X 1 2)+(523745610258491/5000000000000000 : ℝ)*((1 : ℝ)*pair X 1 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow2 : (1 : ℝ) ^ (75/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^75 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^75*1^16 ≤ 1^16*1^75 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 75 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 75 16 (by norm_num) hpowers
    exact h
  have s0_corner2a : (2 : ℝ) ≤ (5796818954377947/5000000000000000 : ℝ) ^ (75/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (5796818954377947/5000000000000000 : ℝ)^75 := by
      have hnat : (2 : ℕ)^16*5000000000000000^75 ≤ 5796818954377947^75*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 5796818954377947 5000000000000000 16 75 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5796818954377947/5000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 75 16 (by norm_num) hpowers
    exact h
  have s0_corner2b : (3 : ℝ) ≤ (3160282282318219/2500000000000000 : ℝ) ^ (75/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (3160282282318219/2500000000000000 : ℝ)^75 := by
      have hnat : (3 : ℕ)^16*2500000000000000^75 ≤ 3160282282318219^75*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 3160282282318219 2500000000000000 16 75 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (3160282282318219/2500000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 75 16 (by norm_num) hpowers
    exact h
  have major_s0_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(796818954377947/5000000000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 1 0))+(523745610258491/5000000000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (75/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (796818954377947/5000000000000000 : ℝ)) (beta := (523745610258491/5000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow2,s0_corner2a]) (by linarith only [s0_pow2,s0_corner2b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![true, false, false], ![false, false, true]] hX 2 (by
        change ((-1 : ℝ)*pair X 2 0) ≤ (1 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order2.2.2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(796818954377947/5000000000000000 : ℝ)*((-1 : ℝ)*pair X 2 0)+(523745610258491/5000000000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s0_0 : ((-829147229/2000000000 : ℝ)*X 0 0+(-1007099121/2000000000 : ℝ)*X 0 1+(105534011/312500000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c315084_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_1 : ((105534011/312500000 : ℝ)*X 1 0+(829147229/2000000000 : ℝ)*X 1 1+(1007099121/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c315084_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_2 : ((1007099121/2000000000 : ℝ)*X 2 0+(-105534011/312500000 : ℝ)*X 2 1+(-829147229/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c315084_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_6 : ((2100367693/5000000000 : ℝ)*X 0 0+(-2100367693/5000000000 : ℝ)*X 0 1+(2100367693/5000000000 : ℝ)*X 0 2+(2100367693/5000000000 : ℝ)*X 1 0+(-2100367693/5000000000 : ℝ)*X 1 1+(2100367693/5000000000 : ℝ)*X 1 2+(2100367693/5000000000 : ℝ)*X 2 0+(-2100367693/5000000000 : ℝ)*X 2 1+(2100367693/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c315084_s0_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have hsep : (-373977/50000 : ℝ) < ((-174659/100000 : ℝ)*P 0+(-174659/100000 : ℝ)*P 1+(-174659/100000 : ℝ)*P 2+(1 : ℝ)*T) := by
    have hcertificate_margin : (-373977/50000 : ℝ) < (-18361747261710296930811/2500000000000000000000 : ℝ) := by norm_num
    linear_combination (499999997007/500000000000 : ℝ)*(base6) + (528887278923/1000000000000 : ℝ)*(base40) + (528887278923/1000000000000 : ℝ)*(base50) + (528887278923/1000000000000 : ℝ)*(base60) + (174659/100000 : ℝ)*(major_s0_0) + (174659/100000 : ℝ)*(major_s0_1) + (174659/100000 : ℝ)*(major_s0_2) + (695391574891/250000000000 : ℝ)*(sp_s0_0) + (695391574891/250000000000 : ℝ)*(sp_s0_1) + (695391574891/250000000000 : ℝ)*(sp_s0_2) + (2993/500000000000 : ℝ)*(sp_s0_6) + (695391574891/250000000000 : ℝ)*(f.sum) + (53848737/1250000000000000000000 : ℝ)*base62 + (870461359/2500000000000000000000 : ℝ)*base65 + (360750073/1250000000000000000000 : ℝ)*base66 + (360750073/1250000000000000000000 : ℝ)*base68 + (53848737/1250000000000000000000 : ℝ)*base71 + (870461359/2500000000000000000000 : ℝ)*base72 + (870461359/2500000000000000000000 : ℝ)*base74 + (360750073/1250000000000000000000 : ℝ)*base77 + (53848737/1250000000000000000000 : ℝ)*base78 + hcertificate_margin
  linarith only [hsep,f.failure]

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
namespace HlawkaSchatten.DiagonalCutoff4
theorem coarse_distinct_p015_b033 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ))
    (c : Fin 88) (hlo : 82 ≤ c.val) (hhi : c.val < 85)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (174659/100000 : ℝ) (34911/20000 : ℝ) (15821/20000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  have hc : c=82 ∨ c=83 ∨ c=84 := by omega
  rcases hc with rfl|rfl|rfl
  · exact collision_c315082 p hpa (by linarith only [hpb]) X hX
  · exact collision_c315083 p hpa (by linarith only [hpb]) X hX
  · exact collision_c315084 p hpa (by linarith only [hpb]) X hX

end HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ))
    (c : Fin 88) (hlo : 82 ≤ c.val) (hhi : c.val < 85)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (174659/100000 : ℝ) (34911/20000 : ℝ) (15821/20000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  exact HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p015_b033 p hpa hpb c hlo hhi hn63 hn87 X hX

#print axioms solution
