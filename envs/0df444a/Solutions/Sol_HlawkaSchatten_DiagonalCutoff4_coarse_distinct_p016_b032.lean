-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p016_b032
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T01:02:30.371263+00:00
-- url     : https://prove2.me/submissions/eff476fb-7384-4e20-b1ae-7deaa7cd6a23

import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c316080_s0
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c316080_s1
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c316080_s2
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
theorem HlawkaSchatten.DiagonalCutoff4.collision_c316080 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (77/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (177257/100000 : ℝ) (173433/100000 : ℝ) (1587/2000 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![true, true, true]]) : False := by
  have h0 := collision_c316080_s0 p hpa hpb X hX
  have h1 := collision_c316080_s1 p hpa hpb X hX h0
  exact collision_c316080_s2 p hpa hpb X hX h1

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
theorem collision_support_c316078_s0_0 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (77/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-735887893/2500000000 : ℝ)*x 0 + (735887893/2500000000 : ℝ)*x 1 + (-6431509029/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (735887893/2500000000 : ℝ)^77 ≤ (1334871043323/6250000000000 : ℝ)^61 := by
    have hnat : (735887893 : ℕ)^77*6250000000000^61 ≤ 1334871043323^61*2500000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      735887893 2500000000 1334871043323 6250000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (735887893/2500000000 : ℝ)^77 ≤ (1334871043323/6250000000000 : ℝ)^61 := by
    have hnat : (735887893 : ℕ)^77*6250000000000^61 ≤ 1334871043323^61*2500000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      735887893 2500000000 1334871043323 6250000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6431509029/10000000000 : ℝ)^77 ≤ (28642063293483/50000000000000 : ℝ)^61 := by
    have hnat : (6431509029 : ℕ)^77*50000000000000^61 ≤ 28642063293483^61*10000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6431509029 10000000000 28642063293483 50000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (77/16 : ℝ)) 77 61 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-735887893/2500000000 : ℝ), (735887893/2500000000 : ℝ), (-6431509029/10000000000 : ℝ)] ![(1334871043323/6250000000000 : ℝ), (1334871043323/6250000000000 : ℝ), (28642063293483/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-735887893/2500000000 : ℝ)|^77 ≤ (1334871043323/6250000000000 : ℝ)^61
        have hw : |(-735887893/2500000000 : ℝ)|=(735887893/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(735887893/2500000000 : ℝ)|^77 ≤ (1334871043323/6250000000000 : ℝ)^61
        have hw : |(735887893/2500000000 : ℝ)|=(735887893/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-6431509029/10000000000 : ℝ)|^77 ≤ (28642063293483/50000000000000 : ℝ)^61
        have hw : |(-6431509029/10000000000 : ℝ)|=(6431509029/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316078_s0_1 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (77/16 : ℝ)) (x : Fin 3 → ℝ) :
    (6431509029/10000000000 : ℝ)*x 0 + (-735887893/2500000000 : ℝ)*x 1 + (-735887893/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6431509029/10000000000 : ℝ)^77 ≤ (28642063293483/50000000000000 : ℝ)^61 := by
    have hnat : (6431509029 : ℕ)^77*50000000000000^61 ≤ 28642063293483^61*10000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6431509029 10000000000 28642063293483 50000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (735887893/2500000000 : ℝ)^77 ≤ (1334871043323/6250000000000 : ℝ)^61 := by
    have hnat : (735887893 : ℕ)^77*6250000000000^61 ≤ 1334871043323^61*2500000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      735887893 2500000000 1334871043323 6250000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (735887893/2500000000 : ℝ)^77 ≤ (1334871043323/6250000000000 : ℝ)^61 := by
    have hnat : (735887893 : ℕ)^77*6250000000000^61 ≤ 1334871043323^61*2500000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      735887893 2500000000 1334871043323 6250000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (77/16 : ℝ)) 77 61 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6431509029/10000000000 : ℝ), (-735887893/2500000000 : ℝ), (-735887893/2500000000 : ℝ)] ![(28642063293483/50000000000000 : ℝ), (1334871043323/6250000000000 : ℝ), (1334871043323/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6431509029/10000000000 : ℝ)|^77 ≤ (28642063293483/50000000000000 : ℝ)^61
        have hw : |(6431509029/10000000000 : ℝ)|=(6431509029/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-735887893/2500000000 : ℝ)|^77 ≤ (1334871043323/6250000000000 : ℝ)^61
        have hw : |(-735887893/2500000000 : ℝ)|=(735887893/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-735887893/2500000000 : ℝ)|^77 ≤ (1334871043323/6250000000000 : ℝ)^61
        have hw : |(-735887893/2500000000 : ℝ)|=(735887893/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316078_s0_2 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (77/16 : ℝ)) (x : Fin 3 → ℝ) :
    (735887893/2500000000 : ℝ)*x 0 + (6431509029/10000000000 : ℝ)*x 1 + (735887893/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (735887893/2500000000 : ℝ)^77 ≤ (1334871043323/6250000000000 : ℝ)^61 := by
    have hnat : (735887893 : ℕ)^77*6250000000000^61 ≤ 1334871043323^61*2500000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      735887893 2500000000 1334871043323 6250000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6431509029/10000000000 : ℝ)^77 ≤ (28642063293483/50000000000000 : ℝ)^61 := by
    have hnat : (6431509029 : ℕ)^77*50000000000000^61 ≤ 28642063293483^61*10000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6431509029 10000000000 28642063293483 50000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (735887893/2500000000 : ℝ)^77 ≤ (1334871043323/6250000000000 : ℝ)^61 := by
    have hnat : (735887893 : ℕ)^77*6250000000000^61 ≤ 1334871043323^61*2500000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      735887893 2500000000 1334871043323 6250000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (77/16 : ℝ)) 77 61 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(735887893/2500000000 : ℝ), (6431509029/10000000000 : ℝ), (735887893/2500000000 : ℝ)] ![(1334871043323/6250000000000 : ℝ), (28642063293483/50000000000000 : ℝ), (1334871043323/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(735887893/2500000000 : ℝ)|^77 ≤ (1334871043323/6250000000000 : ℝ)^61
        have hw : |(735887893/2500000000 : ℝ)|=(735887893/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6431509029/10000000000 : ℝ)|^77 ≤ (28642063293483/50000000000000 : ℝ)^61
        have hw : |(6431509029/10000000000 : ℝ)|=(6431509029/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(735887893/2500000000 : ℝ)|^77 ≤ (1334871043323/6250000000000 : ℝ)^61
        have hw : |(735887893/2500000000 : ℝ)|=(735887893/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316078_s0_6 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (77/16 : ℝ)) (x : Fin 3 → ℝ) :
    (837627293/2000000000 : ℝ)*x 0 + (837627293/2000000000 : ℝ)*x 1 + (-837627293/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (837627293/2000000000 : ℝ)^77 ≤ (8333333332781/25000000000000 : ℝ)^61 := by
    have hnat : (837627293 : ℕ)^77*25000000000000^61 ≤ 8333333332781^61*2000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      837627293 2000000000 8333333332781 25000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (837627293/2000000000 : ℝ)^77 ≤ (8333333332781/25000000000000 : ℝ)^61 := by
    have hnat : (837627293 : ℕ)^77*25000000000000^61 ≤ 8333333332781^61*2000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      837627293 2000000000 8333333332781 25000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (837627293/2000000000 : ℝ)^77 ≤ (8333333332781/25000000000000 : ℝ)^61 := by
    have hnat : (837627293 : ℕ)^77*25000000000000^61 ≤ 8333333332781^61*2000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      837627293 2000000000 8333333332781 25000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (77/16 : ℝ)) 77 61 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(837627293/2000000000 : ℝ), (837627293/2000000000 : ℝ), (-837627293/2000000000 : ℝ)] ![(8333333332781/25000000000000 : ℝ), (8333333332781/25000000000000 : ℝ), (8333333332781/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(837627293/2000000000 : ℝ)|^77 ≤ (8333333332781/25000000000000 : ℝ)^61
        have hw : |(837627293/2000000000 : ℝ)|=(837627293/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(837627293/2000000000 : ℝ)|^77 ≤ (8333333332781/25000000000000 : ℝ)^61
        have hw : |(837627293/2000000000 : ℝ)|=(837627293/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-837627293/2000000000 : ℝ)|^77 ≤ (8333333332781/25000000000000 : ℝ)^61
        have hw : |(-837627293/2000000000 : ℝ)|=(837627293/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c316078 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (77/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (177257/100000 : ℝ) (173433/100000 : ℝ) (1587/2000 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![true, false, false]]) : False := by
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
  have main1 : (1587/2000 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (1587/2000 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 0+X 2 0)) ∧ ((-1 : ℝ)*(X 0 0+X 2 0)) ≤ ((-1 : ℝ)*(X 0 2+X 2 2)) ∧ ((-1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 0) ∧ ((-1 : ℝ)*pair X 1 0) ≤ ((-1 : ℝ)*pair X 1 2) ∧ ((-1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (1587/2000 : ℝ)*P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (1587/2000 : ℝ)*P 2 ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((-1 : ℝ)*(X 0 1+X 1 1)) ∧ ((-1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((-1 : ℝ)*pair X 2 1) ∧ ((-1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base25 : ((1 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 2).2]
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
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
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![true, false, false]] hX 0 (by
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
  have major_s0_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(1571102372827199/10000000000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2))+(515551893046311/5000000000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 2 0)) := by
    have hh := chart_majorant (a := (19/4 : ℝ)) (rho := (1 : ℝ)) (alpha := (1571102372827199/10000000000000000 : ℝ)) (beta := (515551893046311/5000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow1,s0_corner1a]) (by linarith only [s0_pow1,s0_corner1b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![true, false, false]] hX 1 (by
        change ((-1 : ℝ)*pair X 1 2) ≤ (1 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order1.2.2])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(1571102372827199/10000000000000000 : ℝ)*((-1 : ℝ)*pair X 1 2)+(515551893046311/5000000000000000 : ℝ)*((-1 : ℝ)*pair X 1 0) at hh
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
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![true, false, false]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (1 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order2.2.2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(1571102372827199/10000000000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(515551893046311/5000000000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s0_0 : ((-735887893/2500000000 : ℝ)*X 0 0+(735887893/2500000000 : ℝ)*X 0 1+(-6431509029/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c316078_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_1 : ((6431509029/10000000000 : ℝ)*X 1 0+(-735887893/2500000000 : ℝ)*X 1 1+(-735887893/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c316078_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_2 : ((735887893/2500000000 : ℝ)*X 2 0+(6431509029/10000000000 : ℝ)*X 2 1+(735887893/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c316078_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_6 : ((837627293/2000000000 : ℝ)*X 0 0+(837627293/2000000000 : ℝ)*X 0 1+(-837627293/2000000000 : ℝ)*X 0 2+(837627293/2000000000 : ℝ)*X 1 0+(837627293/2000000000 : ℝ)*X 1 1+(-837627293/2000000000 : ℝ)*X 1 2+(837627293/2000000000 : ℝ)*X 2 0+(837627293/2000000000 : ℝ)*X 2 1+(-837627293/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c316078_s0_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have hsep : (-381771/50000 : ℝ) < ((-177257/100000 : ℝ)*P 0+(-177257/100000 : ℝ)*P 1+(-177257/100000 : ℝ)*P 2+(1 : ℝ)*T) := by
    have hcertificate_margin : (-381771/50000 : ℝ) < (-19034163379044381843753787791/2500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (587/1000000000000 : ℝ)*(base25) + (105986359227/250000000000 : ℝ)*(base39) + (84789087419/200000000000 : ℝ)*(base49) + (267/1000000000000 : ℝ)*(base50) + (21197271857/50000000000 : ℝ)*(base59) + (129/200000000000 : ℝ)*(base60) + (1772570000227/1000000000000 : ℝ)*(major_s0_0) + (177257/100000 : ℝ)*(major_s0_1) + (177257/100000 : ℝ)*(major_s0_2) + (2537888448431/1000000000000 : ℝ)*(sp_s0_0) + (253788844937/100000000000 : ℝ)*(sp_s0_1) + (253788844807/100000000000 : ℝ)*(sp_s0_2) + (1 : ℝ)*(sp_s0_6) + (2537888448431/1000000000000 : ℝ)*(f.sum) + (1089931789/5000000000000000000000 : ℝ)*base62 + (488745259/1250000000000000000000 : ℝ)*base64 + (6469252069/10000000000000000000000 : ℝ)*base67 + (43437697/100000000000000000000 : ℝ)*base69 + (1544698838225827/10000000000000000000000000000 : ℝ)*base70 + (3565982723811512597/5000000000000000000000000000 : ℝ)*base73 + (64392229/500000000000000000000 : ℝ)*base74 + (1945746031774173/10000000000000000000000000000 : ℝ)*base77 + (4431270256512597/5000000000000000000000000000 : ℝ)*base79 + (939/1000000000000 : ℝ)*base83 + (113/500000000000 : ℝ)*base85 + (227/1000000000000 : ℝ)*base86 + hcertificate_margin
  linarith only [hsep,f.failure]

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem collision_support_c316079_s0_1 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (77/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3964975971/5000000000 : ℝ)*x 0 + (-1518040007/10000000000 : ℝ)*x 1 + (-2355710727/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3964975971/5000000000 : ℝ)^77 ≤ (2984762012613/4000000000000 : ℝ)^61 := by
    have hnat : (3964975971 : ℕ)^77*4000000000000^61 ≤ 2984762012613^61*5000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3964975971 5000000000 2984762012613 4000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1518040007/10000000000 : ℝ)^77 ≤ (9258440324043/100000000000000 : ℝ)^61 := by
    have hnat : (1518040007 : ℕ)^77*100000000000000^61 ≤ 9258440324043^61*10000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1518040007 10000000000 9258440324043 100000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2355710727/10000000000 : ℝ)^77 ≤ (16122509349867/100000000000000 : ℝ)^61 := by
    have hnat : (2355710727 : ℕ)^77*100000000000000^61 ≤ 16122509349867^61*10000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2355710727 10000000000 16122509349867 100000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (77/16 : ℝ)) 77 61 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3964975971/5000000000 : ℝ), (-1518040007/10000000000 : ℝ), (-2355710727/10000000000 : ℝ)] ![(2984762012613/4000000000000 : ℝ), (9258440324043/100000000000000 : ℝ), (16122509349867/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3964975971/5000000000 : ℝ)|^77 ≤ (2984762012613/4000000000000 : ℝ)^61
        have hw : |(3964975971/5000000000 : ℝ)|=(3964975971/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1518040007/10000000000 : ℝ)|^77 ≤ (9258440324043/100000000000000 : ℝ)^61
        have hw : |(-1518040007/10000000000 : ℝ)|=(1518040007/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2355710727/10000000000 : ℝ)|^77 ≤ (16122509349867/100000000000000 : ℝ)^61
        have hw : |(-2355710727/10000000000 : ℝ)|=(2355710727/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316079_s0_2 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (77/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3086403401/10000000000 : ℝ)*x 0 + (737789803/1250000000 : ℝ)*x 1 + (3432018521/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3086403401/10000000000 : ℝ)^77 ≤ (22674548081101/100000000000000 : ℝ)^61 := by
    have hnat : (3086403401 : ℕ)^77*100000000000000^61 ≤ 22674548081101^61*10000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3086403401 10000000000 22674548081101 100000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (737789803/1250000000 : ℝ)^77 ≤ (1284999644823/2500000000000 : ℝ)^61 := by
    have hnat : (737789803 : ℕ)^77*2500000000000^61 ≤ 1284999644823^61*1250000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      737789803 1250000000 1284999644823 2500000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3432018521/10000000000 : ℝ)^77 ≤ (6481366525741/25000000000000 : ℝ)^61 := by
    have hnat : (3432018521 : ℕ)^77*25000000000000^61 ≤ 6481366525741^61*10000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3432018521 10000000000 6481366525741 25000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (77/16 : ℝ)) 77 61 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3086403401/10000000000 : ℝ), (737789803/1250000000 : ℝ), (3432018521/10000000000 : ℝ)] ![(22674548081101/100000000000000 : ℝ), (1284999644823/2500000000000 : ℝ), (6481366525741/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3086403401/10000000000 : ℝ)|^77 ≤ (22674548081101/100000000000000 : ℝ)^61
        have hw : |(3086403401/10000000000 : ℝ)|=(3086403401/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(737789803/1250000000 : ℝ)|^77 ≤ (1284999644823/2500000000000 : ℝ)^61
        have hw : |(737789803/1250000000 : ℝ)|=(737789803/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3432018521/10000000000 : ℝ)|^77 ≤ (6481366525741/25000000000000 : ℝ)^61
        have hw : |(3432018521/10000000000 : ℝ)|=(3432018521/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316079_s0_7 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (77/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-444221959/2500000000 : ℝ)*x 0 + (12483261/40000000 : ℝ)*x 1 + (-717027413/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (444221959/2500000000 : ℝ)^77 ≤ (1129404532453/10000000000000 : ℝ)^61 := by
    have hnat : (444221959 : ℕ)^77*10000000000000^61 ≤ 1129404532453^61*2500000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      444221959 2500000000 1129404532453 10000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (12483261/40000000 : ℝ)^77 ≤ (22994134042777/100000000000000 : ℝ)^61 := by
    have hnat : (12483261 : ℕ)^77*100000000000000^61 ≤ 22994134042777^61*40000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      12483261 40000000 22994134042777 100000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (717027413/1000000000 : ℝ)^77 ≤ (4106988788439/6250000000000 : ℝ)^61 := by
    have hnat : (717027413 : ℕ)^77*6250000000000^61 ≤ 4106988788439^61*1000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      717027413 1000000000 4106988788439 6250000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (77/16 : ℝ)) 77 61 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-444221959/2500000000 : ℝ), (12483261/40000000 : ℝ), (-717027413/1000000000 : ℝ)] ![(1129404532453/10000000000000 : ℝ), (22994134042777/100000000000000 : ℝ), (4106988788439/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-444221959/2500000000 : ℝ)|^77 ≤ (1129404532453/10000000000000 : ℝ)^61
        have hw : |(-444221959/2500000000 : ℝ)|=(444221959/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(12483261/40000000 : ℝ)|^77 ≤ (22994134042777/100000000000000 : ℝ)^61
        have hw : |(12483261/40000000 : ℝ)|=(12483261/40000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-717027413/1000000000 : ℝ)|^77 ≤ (4106988788439/6250000000000 : ℝ)^61
        have hw : |(-717027413/1000000000 : ℝ)|=(717027413/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316079_s0_8 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (77/16 : ℝ)) (x : Fin 3 → ℝ) :
    (8014864879/10000000000 : ℝ)*x 0 + (-106023821/2500000000 : ℝ)*x 1 + (-3069698757/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (8014864879/10000000000 : ℝ)^77 ≤ (75629051249801/100000000000000 : ℝ)^61 := by
    have hnat : (8014864879 : ℕ)^77*100000000000000^61 ≤ 75629051249801^61*10000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8014864879 10000000000 75629051249801 100000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (106023821/2500000000 : ℝ)^77 ≤ (925601092831/50000000000000 : ℝ)^61 := by
    have hnat : (106023821 : ℕ)^77*50000000000000^61 ≤ 925601092831^61*2500000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      106023821 2500000000 925601092831 50000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3069698757/10000000000 : ℝ)^77 ≤ (22519746541187/100000000000000 : ℝ)^61 := by
    have hnat : (3069698757 : ℕ)^77*100000000000000^61 ≤ 22519746541187^61*10000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3069698757 10000000000 22519746541187 100000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (77/16 : ℝ)) 77 61 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(8014864879/10000000000 : ℝ), (-106023821/2500000000 : ℝ), (-3069698757/10000000000 : ℝ)] ![(75629051249801/100000000000000 : ℝ), (925601092831/50000000000000 : ℝ), (22519746541187/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(8014864879/10000000000 : ℝ)|^77 ≤ (75629051249801/100000000000000 : ℝ)^61
        have hw : |(8014864879/10000000000 : ℝ)|=(8014864879/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-106023821/2500000000 : ℝ)|^77 ≤ (925601092831/50000000000000 : ℝ)^61
        have hw : |(-106023821/2500000000 : ℝ)|=(106023821/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3069698757/10000000000 : ℝ)|^77 ≤ (22519746541187/100000000000000 : ℝ)^61
        have hw : |(-3069698757/10000000000 : ℝ)|=(3069698757/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316079_s0_9 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (77/16 : ℝ)) (x : Fin 3 → ℝ) :
    (414032537/2500000000 : ℝ)*x 0 + (7505103861/10000000000 : ℝ)*x 1 + (175039433/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (414032537/2500000000 : ℝ)^77 ≤ (2066792024267/20000000000000 : ℝ)^61 := by
    have hnat : (414032537 : ℕ)^77*20000000000000^61 ≤ 2066792024267^61*2500000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      414032537 2500000000 2066792024267 20000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (7505103861/10000000000 : ℝ)^77 ≤ (13921735539011/20000000000000 : ℝ)^61 := by
    have hnat : (7505103861 : ℕ)^77*20000000000000^61 ≤ 13921735539011^61*10000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7505103861 10000000000 13921735539011 20000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (175039433/625000000 : ℝ)^77 ≤ (5014340541151/25000000000000 : ℝ)^61 := by
    have hnat : (175039433 : ℕ)^77*25000000000000^61 ≤ 5014340541151^61*625000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      175039433 625000000 5014340541151 25000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (77/16 : ℝ)) 77 61 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(414032537/2500000000 : ℝ), (7505103861/10000000000 : ℝ), (175039433/625000000 : ℝ)] ![(2066792024267/20000000000000 : ℝ), (13921735539011/20000000000000 : ℝ), (5014340541151/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(414032537/2500000000 : ℝ)|^77 ≤ (2066792024267/20000000000000 : ℝ)^61
        have hw : |(414032537/2500000000 : ℝ)|=(414032537/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(7505103861/10000000000 : ℝ)|^77 ≤ (13921735539011/20000000000000 : ℝ)^61
        have hw : |(7505103861/10000000000 : ℝ)|=(7505103861/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(175039433/625000000 : ℝ)|^77 ≤ (5014340541151/25000000000000 : ℝ)^61
        have hw : |(175039433/625000000 : ℝ)|=(175039433/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316079_s0_13 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (77/16 : ℝ)) (x : Fin 3 → ℝ) :
    (61854633/250000000 : ℝ)*x 0 + (7327566403/10000000000 : ℝ)*x 1 + (-565309281/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (61854633/250000000 : ℝ)^77 ≤ (8576349799369/50000000000000 : ℝ)^61 := by
    have hnat : (61854633 : ℕ)^77*50000000000000^61 ≤ 8576349799369^61*250000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      61854633 250000000 8576349799369 50000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (7327566403/10000000000 : ℝ)^77 ≤ (67536627915119/100000000000000 : ℝ)^61 := by
    have hnat : (7327566403 : ℕ)^77*100000000000000^61 ≤ 67536627915119^61*10000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7327566403 10000000000 67536627915119 100000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (565309281/2500000000 : ℝ)^77 ≤ (7655336235763/50000000000000 : ℝ)^61 := by
    have hnat : (565309281 : ℕ)^77*50000000000000^61 ≤ 7655336235763^61*2500000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      565309281 2500000000 7655336235763 50000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (77/16 : ℝ)) 77 61 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(61854633/250000000 : ℝ), (7327566403/10000000000 : ℝ), (-565309281/2500000000 : ℝ)] ![(8576349799369/50000000000000 : ℝ), (67536627915119/100000000000000 : ℝ), (7655336235763/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(61854633/250000000 : ℝ)|^77 ≤ (8576349799369/50000000000000 : ℝ)^61
        have hw : |(61854633/250000000 : ℝ)|=(61854633/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(7327566403/10000000000 : ℝ)|^77 ≤ (67536627915119/100000000000000 : ℝ)^61
        have hw : |(7327566403/10000000000 : ℝ)|=(7327566403/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-565309281/2500000000 : ℝ)|^77 ≤ (7655336235763/50000000000000 : ℝ)^61
        have hw : |(-565309281/2500000000 : ℝ)|=(565309281/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316079_s0_14 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (77/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-404491983/10000000000 : ℝ)*x 0 + (1810657227/5000000000 : ℝ)*x 1 + (-947778099/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (404491983/10000000000 : ℝ)^77 ≤ (1743850463839/100000000000000 : ℝ)^61 := by
    have hnat : (404491983 : ℕ)^77*100000000000000^61 ≤ 1743850463839^61*10000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      404491983 10000000000 1743850463839 100000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1810657227/5000000000 : ℝ)^77 ≤ (13871678865437/50000000000000 : ℝ)^61 := by
    have hnat : (1810657227 : ℕ)^77*50000000000000^61 ≤ 13871678865437^61*5000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1810657227 5000000000 13871678865437 50000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (947778099/1250000000 : ℝ)^77 ≤ (70512791793909/100000000000000 : ℝ)^61 := by
    have hnat : (947778099 : ℕ)^77*100000000000000^61 ≤ 70512791793909^61*1250000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      947778099 1250000000 70512791793909 100000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (77/16 : ℝ)) 77 61 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-404491983/10000000000 : ℝ), (1810657227/5000000000 : ℝ), (-947778099/1250000000 : ℝ)] ![(1743850463839/100000000000000 : ℝ), (13871678865437/50000000000000 : ℝ), (70512791793909/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-404491983/10000000000 : ℝ)|^77 ≤ (1743850463839/100000000000000 : ℝ)^61
        have hw : |(-404491983/10000000000 : ℝ)|=(404491983/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1810657227/5000000000 : ℝ)|^77 ≤ (13871678865437/50000000000000 : ℝ)^61
        have hw : |(1810657227/5000000000 : ℝ)|=(1810657227/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-947778099/1250000000 : ℝ)|^77 ≤ (70512791793909/100000000000000 : ℝ)^61
        have hw : |(-947778099/1250000000 : ℝ)|=(947778099/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316079_s0_15 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (77/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1113124953/1250000000 : ℝ)*x 0 + (-715141219/5000000000 : ℝ)*x 1 + (-58513/625000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1113124953/1250000000 : ℝ)^77 ≤ (5398873402953/6250000000000 : ℝ)^61 := by
    have hnat : (1113124953 : ℕ)^77*6250000000000^61 ≤ 5398873402953^61*1250000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1113124953 1250000000 5398873402953 6250000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (715141219/5000000000 : ℝ)^77 ≤ (2147005258783/25000000000000 : ℝ)^61 := by
    have hnat : (715141219 : ℕ)^77*25000000000000^61 ≤ 2147005258783^61*5000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      715141219 5000000000 2147005258783 25000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (58513/625000 : ℝ)^77 ≤ (1257501124973/25000000000000 : ℝ)^61 := by
    have hnat : (58513 : ℕ)^77*25000000000000^61 ≤ 1257501124973^61*625000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      58513 625000 1257501124973 25000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (77/16 : ℝ)) 77 61 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1113124953/1250000000 : ℝ), (-715141219/5000000000 : ℝ), (-58513/625000 : ℝ)] ![(5398873402953/6250000000000 : ℝ), (2147005258783/25000000000000 : ℝ), (1257501124973/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1113124953/1250000000 : ℝ)|^77 ≤ (5398873402953/6250000000000 : ℝ)^61
        have hw : |(1113124953/1250000000 : ℝ)|=(1113124953/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-715141219/5000000000 : ℝ)|^77 ≤ (2147005258783/25000000000000 : ℝ)^61
        have hw : |(-715141219/5000000000 : ℝ)|=(715141219/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-58513/625000 : ℝ)|^77 ≤ (1257501124973/25000000000000 : ℝ)^61
        have hw : |(-58513/625000 : ℝ)|=(58513/625000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316079_s0_16 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (77/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3595729289/10000000000 : ℝ)*x 0 + (5867506619/10000000000 : ℝ)*x 1 + (29575499/100000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3595729289/10000000000 : ℝ)^77 ≤ (5499232669387/20000000000000 : ℝ)^61 := by
    have hnat : (3595729289 : ℕ)^77*20000000000000^61 ≤ 5499232669387^61*10000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3595729289 10000000000 5499232669387 20000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5867506619/10000000000 : ℝ)^77 ≤ (51017609245769/100000000000000 : ℝ)^61 := by
    have hnat : (5867506619 : ℕ)^77*100000000000000^61 ≤ 51017609245769^61*10000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5867506619 10000000000 51017609245769 100000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (29575499/100000000 : ℝ)^77 ≤ (10743113694913/50000000000000 : ℝ)^61 := by
    have hnat : (29575499 : ℕ)^77*50000000000000^61 ≤ 10743113694913^61*100000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      29575499 100000000 10743113694913 50000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (77/16 : ℝ)) 77 61 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3595729289/10000000000 : ℝ), (5867506619/10000000000 : ℝ), (29575499/100000000 : ℝ)] ![(5499232669387/20000000000000 : ℝ), (51017609245769/100000000000000 : ℝ), (10743113694913/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3595729289/10000000000 : ℝ)|^77 ≤ (5499232669387/20000000000000 : ℝ)^61
        have hw : |(3595729289/10000000000 : ℝ)|=(3595729289/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5867506619/10000000000 : ℝ)|^77 ≤ (51017609245769/100000000000000 : ℝ)^61
        have hw : |(5867506619/10000000000 : ℝ)|=(5867506619/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(29575499/100000000 : ℝ)|^77 ≤ (10743113694913/50000000000000 : ℝ)^61
        have hw : |(29575499/100000000 : ℝ)|=(29575499/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316079_s0_20 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (77/16 : ℝ)) (x : Fin 3 → ℝ) :
    (325725871/1250000000 : ℝ)*x 0 + (54580841/156250000 : ℝ)*x 1 + (-6243416787/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (325725871/1250000000 : ℝ)^77 ≤ (18312463130461/100000000000000 : ℝ)^61 := by
    have hnat : (325725871 : ℕ)^77*100000000000000^61 ≤ 18312463130461^61*1250000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      325725871 1250000000 18312463130461 100000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (54580841/156250000 : ℝ)^77 ≤ (26509961760927/100000000000000 : ℝ)^61 := by
    have hnat : (54580841 : ℕ)^77*100000000000000^61 ≤ 26509961760927^61*156250000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      54580841 156250000 26509961760927 100000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6243416787/10000000000 : ℝ)^77 ≤ (6897196886233/12500000000000 : ℝ)^61 := by
    have hnat : (6243416787 : ℕ)^77*12500000000000^61 ≤ 6897196886233^61*10000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6243416787 10000000000 6897196886233 12500000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (77/16 : ℝ)) 77 61 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(325725871/1250000000 : ℝ), (54580841/156250000 : ℝ), (-6243416787/10000000000 : ℝ)] ![(18312463130461/100000000000000 : ℝ), (26509961760927/100000000000000 : ℝ), (6897196886233/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(325725871/1250000000 : ℝ)|^77 ≤ (18312463130461/100000000000000 : ℝ)^61
        have hw : |(325725871/1250000000 : ℝ)|=(325725871/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(54580841/156250000 : ℝ)|^77 ≤ (26509961760927/100000000000000 : ℝ)^61
        have hw : |(54580841/156250000 : ℝ)|=(54580841/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-6243416787/10000000000 : ℝ)|^77 ≤ (6897196886233/12500000000000 : ℝ)^61
        have hw : |(-6243416787/10000000000 : ℝ)|=(6243416787/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316079_s0_21 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (77/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-480653143/10000000000 : ℝ)*x 0 + (2725051883/5000000000 : ℝ)*x 1 + (-1474488147/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (480653143/10000000000 : ℝ)^77 ≤ (2168117160763/100000000000000 : ℝ)^61 := by
    have hnat : (480653143 : ℕ)^77*100000000000000^61 ≤ 2168117160763^61*10000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      480653143 10000000000 2168117160763 100000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2725051883/5000000000 : ℝ)^77 ≤ (726248193013/1562500000000 : ℝ)^61 := by
    have hnat : (2725051883 : ℕ)^77*1562500000000^61 ≤ 726248193013^61*5000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2725051883 5000000000 726248193013 1562500000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1474488147/2500000000 : ℝ)^77 ≤ (2567599923449/5000000000000 : ℝ)^61 := by
    have hnat : (1474488147 : ℕ)^77*5000000000000^61 ≤ 2567599923449^61*2500000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1474488147 2500000000 2567599923449 5000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (77/16 : ℝ)) 77 61 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-480653143/10000000000 : ℝ), (2725051883/5000000000 : ℝ), (-1474488147/2500000000 : ℝ)] ![(2168117160763/100000000000000 : ℝ), (726248193013/1562500000000 : ℝ), (2567599923449/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-480653143/10000000000 : ℝ)|^77 ≤ (2168117160763/100000000000000 : ℝ)^61
        have hw : |(-480653143/10000000000 : ℝ)|=(480653143/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2725051883/5000000000 : ℝ)|^77 ≤ (726248193013/1562500000000 : ℝ)^61
        have hw : |(2725051883/5000000000 : ℝ)|=(2725051883/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1474488147/2500000000 : ℝ)|^77 ≤ (2567599923449/5000000000000 : ℝ)^61
        have hw : |(-1474488147/2500000000 : ℝ)|=(1474488147/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316079_s0_22 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (77/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1176442841/1250000000 : ℝ)*x 0 + (-420226079/10000000000 : ℝ)*x 1 + (-126330293/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1176442841/1250000000 : ℝ)^77 ≤ (92630110135951/100000000000000 : ℝ)^61 := by
    have hnat : (1176442841 : ℕ)^77*100000000000000^61 ≤ 92630110135951^61*1250000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1176442841 1250000000 92630110135951 100000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (420226079/10000000000 : ℝ)^77 ≤ (1829908447053/100000000000000 : ℝ)^61 := by
    have hnat : (420226079 : ℕ)^77*100000000000000^61 ≤ 1829908447053^61*10000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      420226079 10000000000 1829908447053 100000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (126330293/1250000000 : ℝ)^77 ≤ (2769990705921/50000000000000 : ℝ)^61 := by
    have hnat : (126330293 : ℕ)^77*50000000000000^61 ≤ 2769990705921^61*1250000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      126330293 1250000000 2769990705921 50000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (77/16 : ℝ)) 77 61 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1176442841/1250000000 : ℝ), (-420226079/10000000000 : ℝ), (-126330293/1250000000 : ℝ)] ![(92630110135951/100000000000000 : ℝ), (1829908447053/100000000000000 : ℝ), (2769990705921/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1176442841/1250000000 : ℝ)|^77 ≤ (92630110135951/100000000000000 : ℝ)^61
        have hw : |(1176442841/1250000000 : ℝ)|=(1176442841/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-420226079/10000000000 : ℝ)|^77 ≤ (1829908447053/100000000000000 : ℝ)^61
        have hw : |(-420226079/10000000000 : ℝ)|=(420226079/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-126330293/1250000000 : ℝ)|^77 ≤ (2769990705921/50000000000000 : ℝ)^61
        have hw : |(-126330293/1250000000 : ℝ)|=(126330293/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316079_s0_23 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (77/16 : ℝ)) (x : Fin 3 → ℝ) :
    (25964959/100000000 : ℝ)*x 0 + (5851087787/10000000000 : ℝ)*x 1 + (1973668523/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (25964959/100000000 : ℝ)^77 ≤ (2278738093713/12500000000000 : ℝ)^61 := by
    have hnat : (25964959 : ℕ)^77*12500000000000^61 ≤ 2278738093713^61*100000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      25964959 100000000 2278738093713 12500000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5851087787/10000000000 : ℝ)^77 ≤ (6354683656397/12500000000000 : ℝ)^61 := by
    have hnat : (5851087787 : ℕ)^77*12500000000000^61 ≤ 6354683656397^61*10000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5851087787 10000000000 6354683656397 12500000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1973668523/5000000000 : ℝ)^77 ≤ (30932625975967/100000000000000 : ℝ)^61 := by
    have hnat : (1973668523 : ℕ)^77*100000000000000^61 ≤ 30932625975967^61*5000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1973668523 5000000000 30932625975967 100000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (77/16 : ℝ)) 77 61 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(25964959/100000000 : ℝ), (5851087787/10000000000 : ℝ), (1973668523/5000000000 : ℝ)] ![(2278738093713/12500000000000 : ℝ), (6354683656397/12500000000000 : ℝ), (30932625975967/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(25964959/100000000 : ℝ)|^77 ≤ (2278738093713/12500000000000 : ℝ)^61
        have hw : |(25964959/100000000 : ℝ)|=(25964959/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5851087787/10000000000 : ℝ)|^77 ≤ (6354683656397/12500000000000 : ℝ)^61
        have hw : |(5851087787/10000000000 : ℝ)|=(5851087787/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1973668523/5000000000 : ℝ)|^77 ≤ (30932625975967/100000000000000 : ℝ)^61
        have hw : |(1973668523/5000000000 : ℝ)|=(1973668523/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316079_s0_27 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (77/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3665929519/10000000000 : ℝ)*x 0 + (2809375677/5000000000 : ℝ)*x 1 + (-158870663/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3665929519/10000000000 : ℝ)^77 ≤ (28175507454803/100000000000000 : ℝ)^61 := by
    have hnat : (3665929519 : ℕ)^77*100000000000000^61 ≤ 28175507454803^61*10000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3665929519 10000000000 28175507454803 100000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2809375677/5000000000 : ℝ)^77 ≤ (2415135893943/5000000000000 : ℝ)^61 := by
    have hnat : (2809375677 : ℕ)^77*5000000000000^61 ≤ 2415135893943^61*5000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2809375677 5000000000 2415135893943 5000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (158870663/500000000 : ℝ)^77 ≤ (23521774648943/100000000000000 : ℝ)^61 := by
    have hnat : (158870663 : ℕ)^77*100000000000000^61 ≤ 23521774648943^61*500000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      158870663 500000000 23521774648943 100000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (77/16 : ℝ)) 77 61 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3665929519/10000000000 : ℝ), (2809375677/5000000000 : ℝ), (-158870663/500000000 : ℝ)] ![(28175507454803/100000000000000 : ℝ), (2415135893943/5000000000000 : ℝ), (23521774648943/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3665929519/10000000000 : ℝ)|^77 ≤ (28175507454803/100000000000000 : ℝ)^61
        have hw : |(3665929519/10000000000 : ℝ)|=(3665929519/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2809375677/5000000000 : ℝ)|^77 ≤ (2415135893943/5000000000000 : ℝ)^61
        have hw : |(2809375677/5000000000 : ℝ)|=(2809375677/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-158870663/500000000 : ℝ)|^77 ≤ (23521774648943/100000000000000 : ℝ)^61
        have hw : |(-158870663/500000000 : ℝ)|=(158870663/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316079_s1_0 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (77/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-2563296777/10000000000 : ℝ)*x 0 + (1086783757/2500000000 : ℝ)*x 1 + (-344372779/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2563296777/10000000000 : ℝ)^77 ≤ (17936171515457/100000000000000 : ℝ)^61 := by
    have hnat : (2563296777 : ℕ)^77*100000000000000^61 ≤ 17936171515457^61*10000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2563296777 10000000000 17936171515457 100000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1086783757/2500000000 : ℝ)^77 ≤ (17469303695579/50000000000000 : ℝ)^61 := by
    have hnat : (1086783757 : ℕ)^77*50000000000000^61 ≤ 17469303695579^61*2500000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1086783757 2500000000 17469303695579 50000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (344372779/625000000 : ℝ)^77 ≤ (23562610540783/50000000000000 : ℝ)^61 := by
    have hnat : (344372779 : ℕ)^77*50000000000000^61 ≤ 23562610540783^61*625000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      344372779 625000000 23562610540783 50000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (77/16 : ℝ)) 77 61 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2563296777/10000000000 : ℝ), (1086783757/2500000000 : ℝ), (-344372779/625000000 : ℝ)] ![(17936171515457/100000000000000 : ℝ), (17469303695579/50000000000000 : ℝ), (23562610540783/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2563296777/10000000000 : ℝ)|^77 ≤ (17936171515457/100000000000000 : ℝ)^61
        have hw : |(-2563296777/10000000000 : ℝ)|=(2563296777/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1086783757/2500000000 : ℝ)|^77 ≤ (17469303695579/50000000000000 : ℝ)^61
        have hw : |(1086783757/2500000000 : ℝ)|=(1086783757/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-344372779/625000000 : ℝ)|^77 ≤ (23562610540783/50000000000000 : ℝ)^61
        have hw : |(-344372779/625000000 : ℝ)|=(344372779/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316079_s1_1 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (77/16 : ℝ)) (x : Fin 3 → ℝ) :
    (6384458291/10000000000 : ℝ)*x 0 + (-1336050089/5000000000 : ℝ)*x 1 + (-3264861427/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6384458291/10000000000 : ℝ)^77 ≤ (56755643474833/100000000000000 : ℝ)^61 := by
    have hnat : (6384458291 : ℕ)^77*100000000000000^61 ≤ 56755643474833^61*10000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6384458291 10000000000 56755643474833 100000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1336050089/5000000000 : ℝ)^77 ≤ (18902490452101/100000000000000 : ℝ)^61 := by
    have hnat : (1336050089 : ℕ)^77*100000000000000^61 ≤ 18902490452101^61*5000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1336050089 5000000000 18902490452101 100000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3264861427/10000000000 : ℝ)^77 ≤ (24341866061083/100000000000000 : ℝ)^61 := by
    have hnat : (3264861427 : ℕ)^77*100000000000000^61 ≤ 24341866061083^61*10000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3264861427 10000000000 24341866061083 100000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (77/16 : ℝ)) 77 61 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6384458291/10000000000 : ℝ), (-1336050089/5000000000 : ℝ), (-3264861427/10000000000 : ℝ)] ![(56755643474833/100000000000000 : ℝ), (18902490452101/100000000000000 : ℝ), (24341866061083/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6384458291/10000000000 : ℝ)|^77 ≤ (56755643474833/100000000000000 : ℝ)^61
        have hw : |(6384458291/10000000000 : ℝ)|=(6384458291/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1336050089/5000000000 : ℝ)|^77 ≤ (18902490452101/100000000000000 : ℝ)^61
        have hw : |(-1336050089/5000000000 : ℝ)|=(1336050089/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3264861427/10000000000 : ℝ)|^77 ≤ (24341866061083/100000000000000 : ℝ)^61
        have hw : |(-3264861427/10000000000 : ℝ)|=(3264861427/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316079_s1_2 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (77/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3672911551/10000000000 : ℝ)*x 0 + (2563821873/5000000000 : ℝ)*x 1 + (3722028771/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3672911551/10000000000 : ℝ)^77 ≤ (28243262053071/100000000000000 : ℝ)^61 := by
    have hnat : (3672911551 : ℕ)^77*100000000000000^61 ≤ 28243262053071^61*10000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3672911551 10000000000 28243262053071 100000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2563821873/5000000000 : ℝ)^77 ≤ (1344871353037/3125000000000 : ℝ)^61 := by
    have hnat : (2563821873 : ℕ)^77*3125000000000^61 ≤ 1344871353037^61*5000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2563821873 5000000000 1344871353037 3125000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3722028771/10000000000 : ℝ)^77 ≤ (2872085463477/10000000000000 : ℝ)^61 := by
    have hnat : (3722028771 : ℕ)^77*10000000000000^61 ≤ 2872085463477^61*10000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3722028771 10000000000 2872085463477 10000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (77/16 : ℝ)) 77 61 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3672911551/10000000000 : ℝ), (2563821873/5000000000 : ℝ), (3722028771/10000000000 : ℝ)] ![(28243262053071/100000000000000 : ℝ), (1344871353037/3125000000000 : ℝ), (2872085463477/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3672911551/10000000000 : ℝ)|^77 ≤ (28243262053071/100000000000000 : ℝ)^61
        have hw : |(3672911551/10000000000 : ℝ)|=(3672911551/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2563821873/5000000000 : ℝ)|^77 ≤ (1344871353037/3125000000000 : ℝ)^61
        have hw : |(2563821873/5000000000 : ℝ)|=(2563821873/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3722028771/10000000000 : ℝ)|^77 ≤ (2872085463477/10000000000000 : ℝ)^61
        have hw : |(3722028771/10000000000 : ℝ)|=(3722028771/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316079_s1_6 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (77/16 : ℝ)) (x : Fin 3 → ℝ) :
    (459843799/1250000000 : ℝ)*x 0 + (4871515301/10000000000 : ℝ)*x 1 + (-3990448137/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (459843799/1250000000 : ℝ)^77 ≤ (28299948916059/100000000000000 : ℝ)^61 := by
    have hnat : (459843799 : ℕ)^77*100000000000000^61 ≤ 28299948916059^61*1250000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      459843799 1250000000 28299948916059 100000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4871515301/10000000000 : ℝ)^77 ≤ (40340371452591/100000000000000 : ℝ)^61 := by
    have hnat : (4871515301 : ℕ)^77*100000000000000^61 ≤ 40340371452591^61*10000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4871515301 10000000000 40340371452591 100000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3990448137/10000000000 : ℝ)^77 ≤ (15679839810859/50000000000000 : ℝ)^61 := by
    have hnat : (3990448137 : ℕ)^77*50000000000000^61 ≤ 15679839810859^61*10000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3990448137 10000000000 15679839810859 50000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (77/16 : ℝ)) 77 61 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(459843799/1250000000 : ℝ), (4871515301/10000000000 : ℝ), (-3990448137/10000000000 : ℝ)] ![(28299948916059/100000000000000 : ℝ), (40340371452591/100000000000000 : ℝ), (15679839810859/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(459843799/1250000000 : ℝ)|^77 ≤ (28299948916059/100000000000000 : ℝ)^61
        have hw : |(459843799/1250000000 : ℝ)|=(459843799/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4871515301/10000000000 : ℝ)|^77 ≤ (40340371452591/100000000000000 : ℝ)^61
        have hw : |(4871515301/10000000000 : ℝ)|=(4871515301/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3990448137/10000000000 : ℝ)|^77 ≤ (15679839810859/50000000000000 : ℝ)^61
        have hw : |(-3990448137/10000000000 : ℝ)|=(3990448137/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c316079 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (77/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (177257/100000 : ℝ) (173433/100000 : ℝ) (1587/2000 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![true, true, false]]) : False := by
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
  have main1 : (1587/2000 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (1587/2000 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 0+X 2 0)) ∧ ((-1 : ℝ)*(X 0 0+X 2 0)) ≤ ((-1 : ℝ)*(X 0 2+X 2 2)) ∧ ((-1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 0) ∧ ((-1 : ℝ)*pair X 1 0) ≤ ((-1 : ℝ)*pair X 1 2) ∧ ((-1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (1587/2000 : ℝ)*P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (1587/2000 : ℝ)*P 2 ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base11 : ((1 : ℝ)*X 0 1+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 1).2]
  have base18 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 2).1]
  have base23 : ((1 : ℝ)*X 2 1+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 1).2]
  have base25 : ((1 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 2).2]
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base43 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 2+(1 : ℝ)*P 1) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 1,f.sum]
  have base49 : ((1 : ℝ)*X 0 0+(1 : ℝ)*X 2 0) ≤ (0 : ℝ) := by
    linarith only [order1.1]
  have base50 : ((-1 : ℝ)*X 0 0+(1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 0+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.2.1]
  have base53 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 1+(1 : ℝ)*P 2) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 2,f.sum]
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
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![true, true, false]] hX 0 (by
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
  have major_s0_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(1571102372827199/10000000000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2))+(515551893046311/5000000000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 2 0)) := by
    have hh := chart_majorant (a := (19/4 : ℝ)) (rho := (1 : ℝ)) (alpha := (1571102372827199/10000000000000000 : ℝ)) (beta := (515551893046311/5000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow1,s0_corner1a]) (by linarith only [s0_pow1,s0_corner1b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![true, true, false]] hX 1 (by
        change ((-1 : ℝ)*pair X 1 2) ≤ (1 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order1.2.2])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(1571102372827199/10000000000000000 : ℝ)*((-1 : ℝ)*pair X 1 2)+(515551893046311/5000000000000000 : ℝ)*((-1 : ℝ)*pair X 1 0) at hh
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
  have major_s0_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(1571102372827199/10000000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(515551893046311/5000000000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (19/4 : ℝ)) (rho := (1 : ℝ)) (alpha := (1571102372827199/10000000000000000 : ℝ)) (beta := (515551893046311/5000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow2,s0_corner2a]) (by linarith only [s0_pow2,s0_corner2b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![true, true, false]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (1 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order2.2.2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(1571102372827199/10000000000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(515551893046311/5000000000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s0_1 : ((3964975971/5000000000 : ℝ)*X 1 0+(-1518040007/10000000000 : ℝ)*X 1 1+(-2355710727/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c316079_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_2 : ((3086403401/10000000000 : ℝ)*X 2 0+(737789803/1250000000 : ℝ)*X 2 1+(3432018521/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c316079_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_7 : ((-444221959/2500000000 : ℝ)*X 0 0+(12483261/40000000 : ℝ)*X 0 1+(-717027413/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c316079_s0_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_8 : ((8014864879/10000000000 : ℝ)*X 1 0+(-106023821/2500000000 : ℝ)*X 1 1+(-3069698757/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c316079_s0_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_9 : ((414032537/2500000000 : ℝ)*X 2 0+(7505103861/10000000000 : ℝ)*X 2 1+(175039433/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c316079_s0_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_13 : ((61854633/250000000 : ℝ)*X 0 0+(7327566403/10000000000 : ℝ)*X 0 1+(-565309281/2500000000 : ℝ)*X 0 2+(61854633/250000000 : ℝ)*X 1 0+(7327566403/10000000000 : ℝ)*X 1 1+(-565309281/2500000000 : ℝ)*X 1 2+(61854633/250000000 : ℝ)*X 2 0+(7327566403/10000000000 : ℝ)*X 2 1+(-565309281/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c316079_s0_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_14 : ((-404491983/10000000000 : ℝ)*X 0 0+(1810657227/5000000000 : ℝ)*X 0 1+(-947778099/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c316079_s0_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_15 : ((1113124953/1250000000 : ℝ)*X 1 0+(-715141219/5000000000 : ℝ)*X 1 1+(-58513/625000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c316079_s0_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_16 : ((3595729289/10000000000 : ℝ)*X 2 0+(5867506619/10000000000 : ℝ)*X 2 1+(29575499/100000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c316079_s0_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_20 : ((325725871/1250000000 : ℝ)*X 0 0+(54580841/156250000 : ℝ)*X 0 1+(-6243416787/10000000000 : ℝ)*X 0 2+(325725871/1250000000 : ℝ)*X 1 0+(54580841/156250000 : ℝ)*X 1 1+(-6243416787/10000000000 : ℝ)*X 1 2+(325725871/1250000000 : ℝ)*X 2 0+(54580841/156250000 : ℝ)*X 2 1+(-6243416787/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c316079_s0_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_21 : ((-480653143/10000000000 : ℝ)*X 0 0+(2725051883/5000000000 : ℝ)*X 0 1+(-1474488147/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c316079_s0_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_22 : ((1176442841/1250000000 : ℝ)*X 1 0+(-420226079/10000000000 : ℝ)*X 1 1+(-126330293/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c316079_s0_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_23 : ((25964959/100000000 : ℝ)*X 2 0+(5851087787/10000000000 : ℝ)*X 2 1+(1973668523/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c316079_s0_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_27 : ((3665929519/10000000000 : ℝ)*X 0 0+(2809375677/5000000000 : ℝ)*X 0 1+(-158870663/500000000 : ℝ)*X 0 2+(3665929519/10000000000 : ℝ)*X 1 0+(2809375677/5000000000 : ℝ)*X 1 1+(-158870663/500000000 : ℝ)*X 1 2+(3665929519/10000000000 : ℝ)*X 2 0+(2809375677/5000000000 : ℝ)*X 2 1+(-158870663/500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c316079_s0_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s0_0 : (0 : ℝ) ≤ ((1014/3125 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(1014/3125 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (17414694907704907103013/1250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (433463/125000000000 : ℝ)*(base18) + (196804641063/200000000000 : ℝ)*(base39) + (246288839359/200000000000 : ℝ)*(base49) + (1170457/250000000000 : ℝ)*(base53) + (361825406759/500000000000 : ℝ)*(base60) + (1497483258881/500000000000 : ℝ)*(major_s0_0) + (1497483258881/500000000000 : ℝ)*(major_s0_1) + (1497480917967/500000000000 : ℝ)*(major_s0_2) + (40513109/1000000000000 : ℝ)*(sp_s0_1) + (2150127788533/500000000000 : ℝ)*(sp_s0_7) + (430026153743/100000000000 : ℝ)*(sp_s0_8) + (4300310200071/1000000000000 : ℝ)*(sp_s0_9) + (1689618191531/1000000000000 : ℝ)*(sp_s0_13) + (24970589/500000000000 : ℝ)*(sp_s0_14) + (1689618191531/1000000000000 : ℝ)*(f.failure) + (4300310200071/1000000000000 : ℝ)*(f.sum) + (1343727830308451/5000000000000000000000000000 : ℝ)*base63 + (145343753280263/2500000000000000000000000000 : ℝ)*base64 + (2141172204895681/5000000000000000000000000000 : ℝ)*base67 + (1110608801384433/5000000000000000000000000000 : ℝ)*base69 + (451529913956207/5000000000000000000000000000 : ℝ)*base70 + (22693165712009/2500000000000000000000000000 : ℝ)*base72 + (1130599707962009/2500000000000000000000000000 : ℝ)*base75 + (1586166433104319/5000000000000000000000000000 : ℝ)*base77 + (2035898352971663/5000000000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base81 + (10467/100000000000000000 : ℝ)*base87 + (10467/100000000000000000 : ℝ)*base89 + (10467/100000000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s0_1 : (0 : ℝ) ≤ ((41423/100000 : ℝ)*X 0 1+(1 : ℝ)*X 0 2+(41423/100000 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (78895896638329146353211/5000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (144550534067/100000000000 : ℝ)*(base39) + (1170741/200000000000 : ℝ)*(base40) + (411536087649/500000000000 : ℝ)*(base49) + (236534649391/250000000000 : ℝ)*(base60) + (3523560755863/1000000000000 : ℝ)*(major_s0_0) + (3523560755863/1000000000000 : ℝ)*(major_s0_1) + (3523560755863/1000000000000 : ℝ)*(major_s0_2) + (16319/312500000 : ℝ)*(sp_s0_1) + (12110829/250000000000 : ℝ)*(sp_s0_7) + (5059241795679/1000000000000 : ℝ)*(sp_s0_14) + (2529569097667/500000000000 : ℝ)*(sp_s0_15) + (2529645119497/500000000000 : ℝ)*(sp_s0_16) + (1987826013/1000000000 : ℝ)*(sp_s0_20) + (99822861/1000000000000 : ℝ)*(sp_s0_22) + (1987826013/1000000000 : ℝ)*(f.failure) + (2529645119497/500000000000 : ℝ)*(f.sum) + (1994760710574951/10000000000000000000000000000 : ℝ)*base63 + (1387141809228607/5000000000000000000000000000 : ℝ)*base64 + (7720579122882263/10000000000000000000000000000 : ℝ)*base67 + (9114496098882263/10000000000000000000000000000 : ℝ)*base68 + (1298552283660523/10000000000000000000000000000 : ℝ)*base71 + (1706146215771393/5000000000000000000000000000 : ℝ)*base73 + (1342739543228607/5000000000000000000000000000 : ℝ)*base75 + (112472560882263/10000000000000000000000000000 : ℝ)*base76 + (2361531322425049/10000000000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base81 + (1/1000000000000 : ℝ)*base83 + (41/100000000000000 : ℝ)*base87 + (41/100000000000000 : ℝ)*base89 + (41/100000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s0_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-16479/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-16479/50000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (95309989533950783697/10000000000000000000000000 : ℝ) := by norm_num
    linear_combination (4025793/1000000000000 : ℝ)*(base11) + (222158940497/200000000000 : ℝ)*(base39) + (159633532329/200000000000 : ℝ)*(base49) + (1006893/1000000000000 : ℝ)*(base50) + (1798708231/200000000000 : ℝ)*(base60) + (25158389811/10000000000 : ℝ)*(major_s0_0) + (25158389811/10000000000 : ℝ)*(major_s0_1) + (25158389811/10000000000 : ℝ)*(major_s0_2) + (53956791/500000000000 : ℝ)*(sp_s0_2) + (1912573/250000000000 : ℝ)*(sp_s0_13) + (3612353620391/1000000000000 : ℝ)*(sp_s0_21) + (3612357646183/1000000000000 : ℝ)*(sp_s0_22) + (3612249732601/1000000000000 : ℝ)*(sp_s0_23) + (1419309488721/1000000000000 : ℝ)*(sp_s0_27) + (1419317139013/1000000000000 : ℝ)*(f.failure) + (3612357646183/1000000000000 : ℝ)*(f.sum) + (48496460934947/100000000000000000000000000 : ℝ)*base63 + (19539138542779/50000000000000000000000000 : ℝ)*base64 + (8989559509389/100000000000000000000000000 : ℝ)*base66 + (7095173360611/100000000000000000000000000 : ℝ)*base68 + (13397297813831/100000000000000000000000000 : ℝ)*base71 + (17350318362779/50000000000000000000000000 : ℝ)*base72 + (40111101857779/50000000000000000000000000 : ℝ)*base75 + (3914381380611/100000000000000000000000000 : ℝ)*base76 + (71651840194947/100000000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base81 + (27341/100000000000000000 : ℝ)*base87 + (27341/100000000000000000 : ℝ)*base89 + (27341/100000000000000000 : ℝ)*base91 + hcertificate_margin
  have s1_pow0 : (1014/3125 : ℝ) ^ (19/4 : ℝ) ≤ (238293769659689439/50000000000000000000 : ℝ) := by
    have hpowers : (1014/3125 : ℝ)^19 ≤ (238293769659689439/50000000000000000000 : ℝ)^4 := by
      have hnat : (1014 : ℕ)^19*50000000000000000000^4 ≤ 238293769659689439^4*3125^19 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1014 3125 238293769659689439 50000000000000000000 19 4 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1014/3125 : ℝ)) (X := (238293769659689439/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 19 4 (by norm_num) hpowers
    exact h
  have s1_corner0a : (50238293769659689439/50000000000000000000 : ℝ) ≤ (500500729991033/500000000000000 : ℝ) ^ (19/4 : ℝ) := by
    have hpowers : (50238293769659689439/50000000000000000000 : ℝ)^4 ≤ (500500729991033/500000000000000 : ℝ)^19 := by
      have hnat : (50238293769659689439 : ℕ)^4*500000000000000^19 ≤ 500500729991033^19*50000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50238293769659689439 50000000000000000000 500500729991033 500000000000000 4 19 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (500500729991033/500000000000000 : ℝ)) (X := (50238293769659689439/50000000000000000000 : ℝ)) (by norm_num) 19 4 (by norm_num) hpowers
    exact h
  have s1_corner0b : (25238293769659689439/25000000000000000000 : ℝ) ≤ (5009995884018697/5000000000000000 : ℝ) ^ (19/4 : ℝ) := by
    have hpowers : (25238293769659689439/25000000000000000000 : ℝ)^4 ≤ (5009995884018697/5000000000000000 : ℝ)^19 := by
      have hnat : (25238293769659689439 : ℕ)^4*5000000000000000^19 ≤ 5009995884018697^19*25000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25238293769659689439 25000000000000000000 5009995884018697 5000000000000000 4 19 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5009995884018697/5000000000000000 : ℝ)) (X := (25238293769659689439/25000000000000000000 : ℝ)) (by norm_num) 19 4 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(166909997011/54080000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(4988584108367/1622400000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (19/4 : ℝ)) (rho := (1014/3125 : ℝ)) (alpha := (166909997011/54080000000000 : ℝ)) (beta := (4988584108367/1622400000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![true, true, false]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (1014/3125 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(166909997011/54080000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(4988584108367/1622400000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (41423/100000 : ℝ) ^ (19/4 : ℝ) ≤ (60807527978452383/4000000000000000000 : ℝ) := by
    have hpowers : (41423/100000 : ℝ)^19 ≤ (60807527978452383/4000000000000000000 : ℝ)^4 := by
      have hnat : (41423 : ℕ)^19*4000000000000000000^4 ≤ 60807527978452383^4*100000^19 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        41423 100000 60807527978452383 4000000000000000000 19 4 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (41423/100000 : ℝ)) (X := (60807527978452383/4000000000000000000 : ℝ)) (by norm_num) (by norm_num) 19 4 (by norm_num) hpowers
    exact h
  have s1_corner1a : (4060807527978452383/4000000000000000000 : ℝ) ≤ (10031813637741081/10000000000000000 : ℝ) ^ (19/4 : ℝ) := by
    have hpowers : (4060807527978452383/4000000000000000000 : ℝ)^4 ≤ (10031813637741081/10000000000000000 : ℝ)^19 := by
      have hnat : (4060807527978452383 : ℕ)^4*10000000000000000^19 ≤ 10031813637741081^19*4000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4060807527978452383 4000000000000000000 10031813637741081 10000000000000000 4 19 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10031813637741081/10000000000000000 : ℝ)) (X := (4060807527978452383/4000000000000000000 : ℝ)) (by norm_num) 19 4 (by norm_num) hpowers
    exact h
  have s1_corner1b : (2060807527978452383/2000000000000000000 : ℝ) ≤ (10063253376828577/10000000000000000 : ℝ) ^ (19/4 : ℝ) := by
    have hpowers : (2060807527978452383/2000000000000000000 : ℝ)^4 ≤ (10063253376828577/10000000000000000 : ℝ)^19 := by
      have hnat : (2060807527978452383 : ℕ)^4*10000000000000000^19 ≤ 10063253376828577^19*2000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2060807527978452383 2000000000000000000 10063253376828577 10000000000000000 4 19 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10063253376828577/10000000000000000 : ℝ)) (X := (2060807527978452383/2000000000000000000 : ℝ)) (by norm_num) 19 4 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(31813637741081/4142300000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2))+(3929967385937/517787500000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 2 0)) := by
    have hh := chart_majorant (a := (19/4 : ℝ)) (rho := (41423/100000 : ℝ)) (alpha := (31813637741081/4142300000000000 : ℝ)) (beta := (3929967385937/517787500000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![true, true, false]] hX 1 (by
        change ((-1 : ℝ)*pair X 1 2) ≤ (41423/100000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(31813637741081/4142300000000000 : ℝ)*((-1 : ℝ)*pair X 1 2)+(3929967385937/517787500000000 : ℝ)*((-1 : ℝ)*pair X 1 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (16479/50000 : ℝ) ^ (19/4 : ℝ) ≤ (513232363838837161/100000000000000000000 : ℝ) := by
    have hpowers : (16479/50000 : ℝ)^19 ≤ (513232363838837161/100000000000000000000 : ℝ)^4 := by
      have hnat : (16479 : ℕ)^19*100000000000000000000^4 ≤ 513232363838837161^4*50000^19 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        16479 50000 513232363838837161 100000000000000000000 19 4 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (16479/50000 : ℝ)) (X := (513232363838837161/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 19 4 (by norm_num) hpowers
    exact h
  have s1_corner2a : (100513232363838837161/100000000000000000000 : ℝ) ≤ (1001078306882799/1000000000000000 : ℝ) ^ (19/4 : ℝ) := by
    have hpowers : (100513232363838837161/100000000000000000000 : ℝ)^4 ≤ (1001078306882799/1000000000000000 : ℝ)^19 := by
      have hnat : (100513232363838837161 : ℕ)^4*1000000000000000^19 ≤ 1001078306882799^19*100000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100513232363838837161 100000000000000000000 1001078306882799 1000000000000000 4 19 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1001078306882799/1000000000000000 : ℝ)) (X := (100513232363838837161/100000000000000000000 : ℝ)) (by norm_num) 19 4 (by norm_num) hpowers
    exact h
  have s1_corner2b : (50513232363838837161/50000000000000000000 : ℝ) ≤ (5010761378385903/5000000000000000 : ℝ) ^ (19/4 : ℝ) := by
    have hpowers : (50513232363838837161/50000000000000000000 : ℝ)^4 ≤ (5010761378385903/5000000000000000 : ℝ)^19 := by
      have hnat : (50513232363838837161 : ℕ)^4*5000000000000000^19 ≤ 5010761378385903^19*50000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50513232363838837161 50000000000000000000 5010761378385903 5000000000000000 4 19 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5010761378385903/5000000000000000 : ℝ)) (X := (50513232363838837161/50000000000000000000 : ℝ)) (by norm_num) 19 4 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(1078306882799/329580000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(149162332553/45775000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (19/4 : ℝ)) (rho := (16479/50000 : ℝ)) (alpha := (1078306882799/329580000000000 : ℝ)) (beta := (149162332553/45775000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![true, true, false]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (16479/50000 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(1078306882799/329580000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(149162332553/45775000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-2563296777/10000000000 : ℝ)*X 0 0+(1086783757/2500000000 : ℝ)*X 0 1+(-344372779/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c316079_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_1 : ((6384458291/10000000000 : ℝ)*X 1 0+(-1336050089/5000000000 : ℝ)*X 1 1+(-3264861427/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c316079_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((3672911551/10000000000 : ℝ)*X 2 0+(2563821873/5000000000 : ℝ)*X 2 1+(3722028771/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c316079_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_6 : ((459843799/1250000000 : ℝ)*X 0 0+(4871515301/10000000000 : ℝ)*X 0 1+(-3990448137/10000000000 : ℝ)*X 0 2+(459843799/1250000000 : ℝ)*X 1 0+(4871515301/10000000000 : ℝ)*X 1 1+(-3990448137/10000000000 : ℝ)*X 1 2+(459843799/1250000000 : ℝ)*X 2 0+(4871515301/10000000000 : ℝ)*X 2 1+(-3990448137/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c316079_s1_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have hsep : (-381771/50000 : ℝ) < ((-177257/100000 : ℝ)*P 0+(-177257/100000 : ℝ)*P 1+(-177257/100000 : ℝ)*P 2+(1 : ℝ)*T) := by
    have hcertificate_margin : (-381771/50000 : ℝ) < (-4840374856394011895757659277444097/640894584850000000000000000000000 : ℝ) := by norm_num
    linear_combination (2071/250000000000 : ℝ)*(base23) + (3207/500000000000 : ℝ)*(base25) + (546142853231/1000000000000 : ℝ)*(base39) + (19/7812500000 : ℝ)*(base40) + (2449/1000000000000 : ℝ)*(base43) + (466582279007/1000000000000 : ℝ)*(base49) + (196799134853/1000000000000 : ℝ)*(base60) + (47/40000000000 : ℝ)*(ratio_s0_2) + (177257/100000 : ℝ)*(major_s1_0) + (1772569997551/1000000000000 : ℝ)*(major_s1_1) + (177257/100000 : ℝ)*(major_s1_2) + (2517509621759/1000000000000 : ℝ)*(sp_s1_0) + (157344351513/62500000000 : ℝ)*(sp_s1_1) + (2517509607061/1000000000000 : ℝ)*(sp_s1_2) + (1 : ℝ)*(sp_s1_6) + (157344351513/62500000000 : ℝ)*(f.sum) + (7551421330214180737/34130480850000000000000000000000 : ℝ)*base62 + (904566438853/4577500000000000000000000 : ℝ)*base64 + (623944641628151/4142300000000000000000000000 : ℝ)*base66 + (4783217647943/10299375000000000000000000 : ℝ)*base69 + (518771072864991/773597500000000000000000000 : ℝ)*base70 + (146450500231/2535000000000000000000000 : ℝ)*base73 + (635519677923413/2071150000000000000000000000 : ℝ)*base74 + (378028929007/845000000000000000000000 : ℝ)*base76 + (1285056116544675673/2100146100000000000000000000000 : ℝ)*base79 + hcertificate_margin
  linarith only [hsep,f.failure]

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
namespace HlawkaSchatten.DiagonalCutoff4
theorem coarse_distinct_p016_b032 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (77/16 : ℝ))
    (c : Fin 88) (hlo : 78 ≤ c.val) (hhi : c.val < 81)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (177257/100000 : ℝ) (173433/100000 : ℝ) (1587/2000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  have hc : c=78 ∨ c=79 ∨ c=80 := by omega
  rcases hc with rfl|rfl|rfl
  · exact collision_c316078 p hpa (by linarith only [hpb]) X hX
  · exact collision_c316079 p hpa (by linarith only [hpb]) X hX
  · exact collision_c316080 p hpa (by linarith only [hpb]) X hX

end HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (77/16 : ℝ))
    (c : Fin 88) (hlo : 78 ≤ c.val) (hhi : c.val < 81)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (177257/100000 : ℝ) (173433/100000 : ℝ) (1587/2000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  exact HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p016_b032 p hpa hpb c hlo hhi hn63 hn87 X hX

#print axioms solution
