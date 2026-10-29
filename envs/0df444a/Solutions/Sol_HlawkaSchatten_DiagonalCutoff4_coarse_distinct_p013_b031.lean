-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p013_b031
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:32:15.29068+00:00
-- url     : https://prove2.me/submissions/83716174-ed65-4027-abee-b9324fd23702

import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c313080_s0
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c313080_s1
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c313080_s2
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
theorem HlawkaSchatten.DiagonalCutoff4.collision_c313080 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (169487/100000 : ℝ) (176973/100000 : ℝ) (78599/100000 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![true, true, true]]) : False := by
  have h0 := collision_c313080_s0 p hpa hpb X hX
  have h1 := collision_c313080_s1 p hpa hpb X hX h0
  exact collision_c313080_s2 p hpa hpb X hX h1

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
theorem collision_support_c313078_s0_0 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-2965205337/10000000000 : ℝ)*x 0 + (2965205337/10000000000 : ℝ)*x 1 + (-6488996319/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2965205337/10000000000 : ℝ)^37 ≤ (21203849377773/100000000000000 : ℝ)^29 := by
    have hnat : (2965205337 : ℕ)^37*100000000000000^29 ≤ 21203849377773^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2965205337 10000000000 21203849377773 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2965205337/10000000000 : ℝ)^37 ≤ (21203849377773/100000000000000 : ℝ)^29 := by
    have hnat : (2965205337 : ℕ)^37*100000000000000^29 ≤ 21203849377773^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2965205337 10000000000 21203849377773 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6488996319/10000000000 : ℝ)^37 ≤ (11518460244077/20000000000000 : ℝ)^29 := by
    have hnat : (6488996319 : ℕ)^37*20000000000000^29 ≤ 11518460244077^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6488996319 10000000000 11518460244077 20000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2965205337/10000000000 : ℝ), (2965205337/10000000000 : ℝ), (-6488996319/10000000000 : ℝ)] ![(21203849377773/100000000000000 : ℝ), (21203849377773/100000000000000 : ℝ), (11518460244077/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2965205337/10000000000 : ℝ)|^37 ≤ (21203849377773/100000000000000 : ℝ)^29
        have hw : |(-2965205337/10000000000 : ℝ)|=(2965205337/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2965205337/10000000000 : ℝ)|^37 ≤ (21203849377773/100000000000000 : ℝ)^29
        have hw : |(2965205337/10000000000 : ℝ)|=(2965205337/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-6488996319/10000000000 : ℝ)|^37 ≤ (11518460244077/20000000000000 : ℝ)^29
        have hw : |(-6488996319/10000000000 : ℝ)|=(6488996319/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c313078_s0_1 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (6488996319/10000000000 : ℝ)*x 0 + (-2965205337/10000000000 : ℝ)*x 1 + (-2965205337/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6488996319/10000000000 : ℝ)^37 ≤ (11518460244077/20000000000000 : ℝ)^29 := by
    have hnat : (6488996319 : ℕ)^37*20000000000000^29 ≤ 11518460244077^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6488996319 10000000000 11518460244077 20000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2965205337/10000000000 : ℝ)^37 ≤ (21203849377773/100000000000000 : ℝ)^29 := by
    have hnat : (2965205337 : ℕ)^37*100000000000000^29 ≤ 21203849377773^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2965205337 10000000000 21203849377773 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2965205337/10000000000 : ℝ)^37 ≤ (21203849377773/100000000000000 : ℝ)^29 := by
    have hnat : (2965205337 : ℕ)^37*100000000000000^29 ≤ 21203849377773^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2965205337 10000000000 21203849377773 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6488996319/10000000000 : ℝ), (-2965205337/10000000000 : ℝ), (-2965205337/10000000000 : ℝ)] ![(11518460244077/20000000000000 : ℝ), (21203849377773/100000000000000 : ℝ), (21203849377773/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6488996319/10000000000 : ℝ)|^37 ≤ (11518460244077/20000000000000 : ℝ)^29
        have hw : |(6488996319/10000000000 : ℝ)|=(6488996319/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2965205337/10000000000 : ℝ)|^37 ≤ (21203849377773/100000000000000 : ℝ)^29
        have hw : |(-2965205337/10000000000 : ℝ)|=(2965205337/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2965205337/10000000000 : ℝ)|^37 ≤ (21203849377773/100000000000000 : ℝ)^29
        have hw : |(-2965205337/10000000000 : ℝ)|=(2965205337/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c313078_s0_2 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (2965205337/10000000000 : ℝ)*x 0 + (6488996319/10000000000 : ℝ)*x 1 + (2965205337/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2965205337/10000000000 : ℝ)^37 ≤ (21203849377773/100000000000000 : ℝ)^29 := by
    have hnat : (2965205337 : ℕ)^37*100000000000000^29 ≤ 21203849377773^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2965205337 10000000000 21203849377773 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6488996319/10000000000 : ℝ)^37 ≤ (11518460244077/20000000000000 : ℝ)^29 := by
    have hnat : (6488996319 : ℕ)^37*20000000000000^29 ≤ 11518460244077^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6488996319 10000000000 11518460244077 20000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2965205337/10000000000 : ℝ)^37 ≤ (21203849377773/100000000000000 : ℝ)^29 := by
    have hnat : (2965205337 : ℕ)^37*100000000000000^29 ≤ 21203849377773^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2965205337 10000000000 21203849377773 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2965205337/10000000000 : ℝ), (6488996319/10000000000 : ℝ), (2965205337/10000000000 : ℝ)] ![(21203849377773/100000000000000 : ℝ), (11518460244077/20000000000000 : ℝ), (21203849377773/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2965205337/10000000000 : ℝ)|^37 ≤ (21203849377773/100000000000000 : ℝ)^29
        have hw : |(2965205337/10000000000 : ℝ)|=(2965205337/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6488996319/10000000000 : ℝ)|^37 ≤ (11518460244077/20000000000000 : ℝ)^29
        have hw : |(6488996319/10000000000 : ℝ)|=(6488996319/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2965205337/10000000000 : ℝ)|^37 ≤ (21203849377773/100000000000000 : ℝ)^29
        have hw : |(2965205337/10000000000 : ℝ)|=(2965205337/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c313078_s0_6 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (4227076403/10000000000 : ℝ)*x 0 + (4227076403/10000000000 : ℝ)*x 1 + (-4227076403/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4227076403/10000000000 : ℝ)^37 ≤ (6666666666199/20000000000000 : ℝ)^29 := by
    have hnat : (4227076403 : ℕ)^37*20000000000000^29 ≤ 6666666666199^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4227076403 10000000000 6666666666199 20000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4227076403/10000000000 : ℝ)^37 ≤ (6666666666199/20000000000000 : ℝ)^29 := by
    have hnat : (4227076403 : ℕ)^37*20000000000000^29 ≤ 6666666666199^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4227076403 10000000000 6666666666199 20000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4227076403/10000000000 : ℝ)^37 ≤ (6666666666199/20000000000000 : ℝ)^29 := by
    have hnat : (4227076403 : ℕ)^37*20000000000000^29 ≤ 6666666666199^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4227076403 10000000000 6666666666199 20000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4227076403/10000000000 : ℝ), (4227076403/10000000000 : ℝ), (-4227076403/10000000000 : ℝ)] ![(6666666666199/20000000000000 : ℝ), (6666666666199/20000000000000 : ℝ), (6666666666199/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4227076403/10000000000 : ℝ)|^37 ≤ (6666666666199/20000000000000 : ℝ)^29
        have hw : |(4227076403/10000000000 : ℝ)|=(4227076403/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4227076403/10000000000 : ℝ)|^37 ≤ (6666666666199/20000000000000 : ℝ)^29
        have hw : |(4227076403/10000000000 : ℝ)|=(4227076403/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-4227076403/10000000000 : ℝ)|^37 ≤ (6666666666199/20000000000000 : ℝ)^29
        have hw : |(-4227076403/10000000000 : ℝ)|=(4227076403/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c313078 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (169487/100000 : ℝ) (176973/100000 : ℝ) (78599/100000 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![true, false, false]]) : False := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (78599/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (78599/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (78599/100000 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (78599/100000 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 0+X 2 0)) ∧ ((-1 : ℝ)*(X 0 0+X 2 0)) ≤ ((-1 : ℝ)*(X 0 2+X 2 2)) ∧ ((-1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 0) ∧ ((-1 : ℝ)*pair X 1 0) ≤ ((-1 : ℝ)*pair X 1 2) ∧ ((-1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (78599/100000 : ℝ)*P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (78599/100000 : ℝ)*P 2 ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((-1 : ℝ)*(X 0 1+X 1 1)) ∧ ((-1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((-1 : ℝ)*pair X 2 1) ∧ ((-1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base33 : ((-1 : ℝ)*N 1+(-1 : ℝ)*N 2+(1 : ℝ)*P 0) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 0,f.sum]
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base49 : ((1 : ℝ)*X 0 0+(1 : ℝ)*X 2 0) ≤ (0 : ℝ) := by
    linarith only [order1.1]
  have base50 : ((-1 : ℝ)*X 0 0+(1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 0+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.2.1]
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
  have s0_pow0 : (1 : ℝ) ^ (73/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^73 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^73*1^16 ≤ 1^16*1^73 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 73 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 73 16 (by norm_num) hpowers
    exact h
  have s0_corner0a : (2 : ℝ) ≤ (5820351075331079/5000000000000000 : ℝ) ^ (73/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (5820351075331079/5000000000000000 : ℝ)^73 := by
      have hnat : (2 : ℕ)^16*5000000000000000^73 ≤ 5820351075331079^73*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 5820351075331079 5000000000000000 16 73 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5820351075331079/5000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 73 16 (by norm_num) hpowers
    exact h
  have s0_corner0b : (3 : ℝ) ≤ (12722560406774351/10000000000000000 : ℝ) ^ (73/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (12722560406774351/10000000000000000 : ℝ)^73 := by
      have hnat : (3 : ℕ)^16*10000000000000000^73 ≤ 12722560406774351^73*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 12722560406774351 10000000000000000 16 73 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12722560406774351/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 73 16 (by norm_num) hpowers
    exact h
  have major_s0_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(820351075331079/5000000000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(1081858256112193/10000000000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (73/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (820351075331079/5000000000000000 : ℝ)) (beta := (1081858256112193/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow0,s0_corner0a]) (by linarith only [s0_pow0,s0_corner0b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![true, false, false]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (1 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order0.2.2])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(820351075331079/5000000000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(1081858256112193/10000000000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow1 : (1 : ℝ) ^ (73/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^73 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^73*1^16 ≤ 1^16*1^73 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 73 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 73 16 (by norm_num) hpowers
    exact h
  have s0_corner1a : (2 : ℝ) ≤ (5820351075331079/5000000000000000 : ℝ) ^ (73/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (5820351075331079/5000000000000000 : ℝ)^73 := by
      have hnat : (2 : ℕ)^16*5000000000000000^73 ≤ 5820351075331079^73*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 5820351075331079 5000000000000000 16 73 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5820351075331079/5000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 73 16 (by norm_num) hpowers
    exact h
  have s0_corner1b : (3 : ℝ) ≤ (12722560406774351/10000000000000000 : ℝ) ^ (73/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (12722560406774351/10000000000000000 : ℝ)^73 := by
      have hnat : (3 : ℕ)^16*10000000000000000^73 ≤ 12722560406774351^73*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 12722560406774351 10000000000000000 16 73 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12722560406774351/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 73 16 (by norm_num) hpowers
    exact h
  have major_s0_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(820351075331079/5000000000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2))+(1081858256112193/10000000000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 2 0)) := by
    have hh := chart_majorant (a := (73/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (820351075331079/5000000000000000 : ℝ)) (beta := (1081858256112193/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow1,s0_corner1a]) (by linarith only [s0_pow1,s0_corner1b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![true, false, false]] hX 1 (by
        change ((-1 : ℝ)*pair X 1 2) ≤ (1 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order1.2.2])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(820351075331079/5000000000000000 : ℝ)*((-1 : ℝ)*pair X 1 2)+(1081858256112193/10000000000000000 : ℝ)*((-1 : ℝ)*pair X 1 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow2 : (1 : ℝ) ^ (73/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^73 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^73*1^16 ≤ 1^16*1^73 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 73 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 73 16 (by norm_num) hpowers
    exact h
  have s0_corner2a : (2 : ℝ) ≤ (5820351075331079/5000000000000000 : ℝ) ^ (73/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (5820351075331079/5000000000000000 : ℝ)^73 := by
      have hnat : (2 : ℕ)^16*5000000000000000^73 ≤ 5820351075331079^73*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 5820351075331079 5000000000000000 16 73 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5820351075331079/5000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 73 16 (by norm_num) hpowers
    exact h
  have s0_corner2b : (3 : ℝ) ≤ (12722560406774351/10000000000000000 : ℝ) ^ (73/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (12722560406774351/10000000000000000 : ℝ)^73 := by
      have hnat : (3 : ℕ)^16*10000000000000000^73 ≤ 12722560406774351^73*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 12722560406774351 10000000000000000 16 73 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12722560406774351/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 73 16 (by norm_num) hpowers
    exact h
  have major_s0_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(820351075331079/5000000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(1081858256112193/10000000000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (73/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (820351075331079/5000000000000000 : ℝ)) (beta := (1081858256112193/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow2,s0_corner2a]) (by linarith only [s0_pow2,s0_corner2b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![true, false, false]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (1 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order2.2.2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(820351075331079/5000000000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(1081858256112193/10000000000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s0_0 : ((-2965205337/10000000000 : ℝ)*X 0 0+(2965205337/10000000000 : ℝ)*X 0 1+(-6488996319/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c313078_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_1 : ((6488996319/10000000000 : ℝ)*X 1 0+(-2965205337/10000000000 : ℝ)*X 1 1+(-2965205337/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c313078_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_2 : ((2965205337/10000000000 : ℝ)*X 2 0+(6488996319/10000000000 : ℝ)*X 2 1+(2965205337/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c313078_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_6 : ((4227076403/10000000000 : ℝ)*X 0 0+(4227076403/10000000000 : ℝ)*X 0 1+(-4227076403/10000000000 : ℝ)*X 0 2+(4227076403/10000000000 : ℝ)*X 1 0+(4227076403/10000000000 : ℝ)*X 1 1+(-4227076403/10000000000 : ℝ)*X 1 2+(4227076403/10000000000 : ℝ)*X 2 0+(4227076403/10000000000 : ℝ)*X 2 1+(-4227076403/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c313078_s0_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have hsep : (-358461/50000 : ℝ) < ((-169487/100000 : ℝ)*P 0+(-169487/100000 : ℝ)*P 1+(-169487/100000 : ℝ)*P 2+(1 : ℝ)*T) := by
    have hcertificate_margin : (-358461/50000 : ℝ) < (-559928675136157104567/78125000000000000000 : ℝ) := by norm_num
    linear_combination (493/1000000000000 : ℝ)*(base33) + (76081058429/200000000000 : ℝ)*(base39) + (76081058439/200000000000 : ℝ)*(base49) + (239/1000000000000 : ℝ)*(base50) + (19020264613/50000000000 : ℝ)*(base59) + (1694869999507/1000000000000 : ℝ)*(major_s0_0) + (169487/100000 : ℝ)*(major_s0_1) + (169487/100000 : ℝ)*(major_s0_2) + (298628626281/125000000000 : ℝ)*(sp_s0_0) + (477805802309/200000000000 : ℝ)*(sp_s0_1) + (477805801951/200000000000 : ℝ)*(sp_s0_2) + (1 : ℝ)*(sp_s0_6) + (298628626281/125000000000 : ℝ)*(f.sum) + (215548236563/5000000000000000000000 : ℝ)*base63 + (213965078257/5000000000000000000000 : ℝ)*base65 + (178386913/2500000000000000000000 : ℝ)*base67 + (3147388354679/2000000000000000000000 : ℝ)*base68 + (214050817469278053/5000000000000000000000000000 : ℝ)*base71 + (1734585045311688851/10000000000000000000000000000 : ℝ)*base73 + (44722469/2000000000000000000000 : ℝ)*base74 + (252261330721947/5000000000000000000000000000 : ℝ)*base76 + (2606362248311149/10000000000000000000000000000 : ℝ)*base78 + (179/100000000000 : ℝ)*base83 + hcertificate_margin
  linarith only [hsep,f.failure]

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem collision_support_c313079_s0_1 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (3993172231/5000000000 : ℝ)*x 0 + (-1523370593/10000000000 : ℝ)*x 1 + (-236334163/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3993172231/5000000000 : ℝ)^37 ≤ (75060173803709/100000000000000 : ℝ)^29 := by
    have hnat : (3993172231 : ℕ)^37*100000000000000^29 ≤ 75060173803709^29*5000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3993172231 5000000000 75060173803709 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1523370593/10000000000 : ℝ)^37 ≤ (4532550225803/50000000000000 : ℝ)^29 := by
    have hnat : (1523370593 : ℕ)^37*50000000000000^29 ≤ 4532550225803^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1523370593 10000000000 4532550225803 50000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (236334163/1000000000 : ℝ)^37 ≤ (3968681432207/25000000000000 : ℝ)^29 := by
    have hnat : (236334163 : ℕ)^37*25000000000000^29 ≤ 3968681432207^29*1000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      236334163 1000000000 3968681432207 25000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3993172231/5000000000 : ℝ), (-1523370593/10000000000 : ℝ), (-236334163/1000000000 : ℝ)] ![(75060173803709/100000000000000 : ℝ), (4532550225803/50000000000000 : ℝ), (3968681432207/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3993172231/5000000000 : ℝ)|^37 ≤ (75060173803709/100000000000000 : ℝ)^29
        have hw : |(3993172231/5000000000 : ℝ)|=(3993172231/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1523370593/10000000000 : ℝ)|^37 ≤ (4532550225803/50000000000000 : ℝ)^29
        have hw : |(-1523370593/10000000000 : ℝ)|=(1523370593/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-236334163/1000000000 : ℝ)|^37 ≤ (3968681432207/25000000000000 : ℝ)^29
        have hw : |(-236334163/1000000000 : ℝ)|=(236334163/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c313079_s0_2 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (625633173/2000000000 : ℝ)*x 0 + (5940469829/10000000000 : ℝ)*x 1 + (3462651871/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (625633173/2000000000 : ℝ)^37 ≤ (11350875740341/50000000000000 : ℝ)^29 := by
    have hnat : (625633173 : ℕ)^37*50000000000000^29 ≤ 11350875740341^29*2000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      625633173 2000000000 11350875740341 50000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5940469829/10000000000 : ℝ)^37 ≤ (2572743770131/5000000000000 : ℝ)^29 := by
    have hnat : (5940469829 : ℕ)^37*5000000000000^29 ≤ 2572743770131^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5940469829 10000000000 2572743770131 5000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3462651871/10000000000 : ℝ)^37 ≤ (6460843275763/25000000000000 : ℝ)^29 := by
    have hnat : (3462651871 : ℕ)^37*25000000000000^29 ≤ 6460843275763^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3462651871 10000000000 6460843275763 25000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(625633173/2000000000 : ℝ), (5940469829/10000000000 : ℝ), (3462651871/10000000000 : ℝ)] ![(11350875740341/50000000000000 : ℝ), (2572743770131/5000000000000 : ℝ), (6460843275763/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(625633173/2000000000 : ℝ)|^37 ≤ (11350875740341/50000000000000 : ℝ)^29
        have hw : |(625633173/2000000000 : ℝ)|=(625633173/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5940469829/10000000000 : ℝ)|^37 ≤ (2572743770131/5000000000000 : ℝ)^29
        have hw : |(5940469829/10000000000 : ℝ)|=(5940469829/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3462651871/10000000000 : ℝ)|^37 ≤ (6460843275763/25000000000000 : ℝ)^29
        have hw : |(3462651871/10000000000 : ℝ)|=(3462651871/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c313079_s0_7 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-70486227/400000000 : ℝ)*x 0 + (1521312659/5000000000 : ℝ)*x 1 + (-7320659603/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (70486227/400000000 : ℝ)^37 ≤ (5457911513787/50000000000000 : ℝ)^29 := by
    have hnat : (70486227 : ℕ)^37*50000000000000^29 ≤ 5457911513787^29*400000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      70486227 400000000 5457911513787 50000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1521312659/5000000000 : ℝ)^37 ≤ (21912722043167/100000000000000 : ℝ)^29 := by
    have hnat : (1521312659 : ℕ)^37*100000000000000^29 ≤ 21912722043167^29*5000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1521312659 5000000000 21912722043167 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (7320659603/10000000000 : ℝ)^37 ≤ (8396431864013/12500000000000 : ℝ)^29 := by
    have hnat : (7320659603 : ℕ)^37*12500000000000^29 ≤ 8396431864013^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7320659603 10000000000 8396431864013 12500000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-70486227/400000000 : ℝ), (1521312659/5000000000 : ℝ), (-7320659603/10000000000 : ℝ)] ![(5457911513787/50000000000000 : ℝ), (21912722043167/100000000000000 : ℝ), (8396431864013/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-70486227/400000000 : ℝ)|^37 ≤ (5457911513787/50000000000000 : ℝ)^29
        have hw : |(-70486227/400000000 : ℝ)|=(70486227/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1521312659/5000000000 : ℝ)|^37 ≤ (21912722043167/100000000000000 : ℝ)^29
        have hw : |(1521312659/5000000000 : ℝ)|=(1521312659/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-7320659603/10000000000 : ℝ)|^37 ≤ (8396431864013/12500000000000 : ℝ)^29
        have hw : |(-7320659603/10000000000 : ℝ)|=(7320659603/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c313079_s0_8 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (8031611253/10000000000 : ℝ)*x 0 + (-366203673/10000000000 : ℝ)*x 1 + (-1576176837/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (8031611253/10000000000 : ℝ)^37 ≤ (75603403991597/100000000000000 : ℝ)^29 := by
    have hnat : (8031611253 : ℕ)^37*100000000000000^29 ≤ 75603403991597^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8031611253 10000000000 75603403991597 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (366203673/10000000000 : ℝ)^37 ≤ (91915400647/6250000000000 : ℝ)^29 := by
    have hnat : (366203673 : ℕ)^37*6250000000000^29 ≤ 91915400647^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      366203673 10000000000 91915400647 6250000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1576176837/5000000000 : ℝ)^37 ≤ (716435924353/3125000000000 : ℝ)^29 := by
    have hnat : (1576176837 : ℕ)^37*3125000000000^29 ≤ 716435924353^29*5000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1576176837 5000000000 716435924353 3125000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(8031611253/10000000000 : ℝ), (-366203673/10000000000 : ℝ), (-1576176837/5000000000 : ℝ)] ![(75603403991597/100000000000000 : ℝ), (91915400647/6250000000000 : ℝ), (716435924353/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(8031611253/10000000000 : ℝ)|^37 ≤ (75603403991597/100000000000000 : ℝ)^29
        have hw : |(8031611253/10000000000 : ℝ)|=(8031611253/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-366203673/10000000000 : ℝ)|^37 ≤ (91915400647/6250000000000 : ℝ)^29
        have hw : |(-366203673/10000000000 : ℝ)|=(366203673/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1576176837/5000000000 : ℝ)|^37 ≤ (716435924353/3125000000000 : ℝ)^29
        have hw : |(-1576176837/5000000000 : ℝ)|=(1576176837/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c313079_s0_9 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (782848381/5000000000 : ℝ)*x 0 + (478473063/625000000 : ℝ)*x 1 + (2776292497/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (782848381/5000000000 : ℝ)^37 ≤ (4693837441567/50000000000000 : ℝ)^29 := by
    have hnat : (782848381 : ℕ)^37*50000000000000^29 ≤ 4693837441567^29*5000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      782848381 5000000000 4693837441567 50000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (478473063/625000000 : ℝ)^37 ≤ (71116645299757/100000000000000 : ℝ)^29 := by
    have hnat : (478473063 : ℕ)^37*100000000000000^29 ≤ 71116645299757^29*625000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      478473063 625000000 71116645299757 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2776292497/10000000000 : ℝ)^37 ≤ (19495679802411/100000000000000 : ℝ)^29 := by
    have hnat : (2776292497 : ℕ)^37*100000000000000^29 ≤ 19495679802411^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2776292497 10000000000 19495679802411 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(782848381/5000000000 : ℝ), (478473063/625000000 : ℝ), (2776292497/10000000000 : ℝ)] ![(4693837441567/50000000000000 : ℝ), (71116645299757/100000000000000 : ℝ), (19495679802411/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(782848381/5000000000 : ℝ)|^37 ≤ (4693837441567/50000000000000 : ℝ)^29
        have hw : |(782848381/5000000000 : ℝ)|=(782848381/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(478473063/625000000 : ℝ)|^37 ≤ (71116645299757/100000000000000 : ℝ)^29
        have hw : |(478473063/625000000 : ℝ)|=(478473063/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2776292497/10000000000 : ℝ)|^37 ≤ (19495679802411/100000000000000 : ℝ)^29
        have hw : |(2776292497/10000000000 : ℝ)|=(2776292497/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c313079_s0_13 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (486102037/2000000000 : ℝ)*x 0 + (1864091579/2500000000 : ℝ)*x 1 + (-2235002827/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (486102037/2000000000 : ℝ)^37 ≤ (8226302509009/50000000000000 : ℝ)^29 := by
    have hnat : (486102037 : ℕ)^37*50000000000000^29 ≤ 8226302509009^29*2000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      486102037 2000000000 8226302509009 50000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1864091579/2500000000 : ℝ)^37 ≤ (68764190599141/100000000000000 : ℝ)^29 := by
    have hnat : (1864091579 : ℕ)^37*100000000000000^29 ≤ 68764190599141^29*2500000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1864091579 2500000000 68764190599141 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2235002827/10000000000 : ℝ)^37 ≤ (14783204366737/100000000000000 : ℝ)^29 := by
    have hnat : (2235002827 : ℕ)^37*100000000000000^29 ≤ 14783204366737^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2235002827 10000000000 14783204366737 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(486102037/2000000000 : ℝ), (1864091579/2500000000 : ℝ), (-2235002827/10000000000 : ℝ)] ![(8226302509009/50000000000000 : ℝ), (68764190599141/100000000000000 : ℝ), (14783204366737/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(486102037/2000000000 : ℝ)|^37 ≤ (8226302509009/50000000000000 : ℝ)^29
        have hw : |(486102037/2000000000 : ℝ)|=(486102037/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1864091579/2500000000 : ℝ)|^37 ≤ (68764190599141/100000000000000 : ℝ)^29
        have hw : |(1864091579/2500000000 : ℝ)|=(1864091579/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2235002827/10000000000 : ℝ)|^37 ≤ (14783204366737/100000000000000 : ℝ)^29
        have hw : |(-2235002827/10000000000 : ℝ)|=(2235002827/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c313079_s0_14 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-357693321/10000000000 : ℝ)*x 0 + (1798805807/5000000000 : ℝ)*x 1 + (-1920656099/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (357693321/10000000000 : ℝ)^37 ≤ (713590961127/50000000000000 : ℝ)^29 := by
    have hnat : (357693321 : ℕ)^37*50000000000000^29 ≤ 713590961127^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      357693321 10000000000 713590961127 50000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1798805807/5000000000 : ℝ)^37 ≤ (6783837948387/25000000000000 : ℝ)^29 := by
    have hnat : (1798805807 : ℕ)^37*25000000000000^29 ≤ 6783837948387^29*5000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1798805807 5000000000 6783837948387 25000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1920656099/2500000000 : ℝ)^37 ≤ (3571873313507/5000000000000 : ℝ)^29 := by
    have hnat : (1920656099 : ℕ)^37*5000000000000^29 ≤ 3571873313507^29*2500000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1920656099 2500000000 3571873313507 5000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-357693321/10000000000 : ℝ), (1798805807/5000000000 : ℝ), (-1920656099/2500000000 : ℝ)] ![(713590961127/50000000000000 : ℝ), (6783837948387/25000000000000 : ℝ), (3571873313507/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-357693321/10000000000 : ℝ)|^37 ≤ (713590961127/50000000000000 : ℝ)^29
        have hw : |(-357693321/10000000000 : ℝ)|=(357693321/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1798805807/5000000000 : ℝ)|^37 ≤ (6783837948387/25000000000000 : ℝ)^29
        have hw : |(1798805807/5000000000 : ℝ)|=(1798805807/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1920656099/2500000000 : ℝ)|^37 ≤ (3571873313507/5000000000000 : ℝ)^29
        have hw : |(-1920656099/2500000000 : ℝ)|=(1920656099/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c313079_s0_15 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (565150139/625000000 : ℝ)*x 0 + (-1357622093/10000000000 : ℝ)*x 1 + (-837619321/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (565150139/625000000 : ℝ)^37 ≤ (87947639171281/100000000000000 : ℝ)^29 := by
    have hnat : (565150139 : ℕ)^37*100000000000000^29 ≤ 87947639171281^29*625000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      565150139 625000000 87947639171281 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1357622093/10000000000 : ℝ)^37 ≤ (7826101731361/100000000000000 : ℝ)^29 := by
    have hnat : (1357622093 : ℕ)^37*100000000000000^29 ≤ 7826101731361^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1357622093 10000000000 7826101731361 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (837619321/10000000000 : ℝ)^37 ≤ (4226259083633/100000000000000 : ℝ)^29 := by
    have hnat : (837619321 : ℕ)^37*100000000000000^29 ≤ 4226259083633^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      837619321 10000000000 4226259083633 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(565150139/625000000 : ℝ), (-1357622093/10000000000 : ℝ), (-837619321/10000000000 : ℝ)] ![(87947639171281/100000000000000 : ℝ), (7826101731361/100000000000000 : ℝ), (4226259083633/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(565150139/625000000 : ℝ)|^37 ≤ (87947639171281/100000000000000 : ℝ)^29
        have hw : |(565150139/625000000 : ℝ)|=(565150139/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1357622093/10000000000 : ℝ)|^37 ≤ (7826101731361/100000000000000 : ℝ)^29
        have hw : |(-1357622093/10000000000 : ℝ)|=(1357622093/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-837619321/10000000000 : ℝ)|^37 ≤ (4226259083633/100000000000000 : ℝ)^29
        have hw : |(-837619321/10000000000 : ℝ)|=(837619321/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c313079_s0_16 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (3696372503/10000000000 : ℝ)*x 0 + (733567483/1250000000 : ℝ)*x 1 + (2970193653/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3696372503/10000000000 : ℝ)^37 ≤ (14044667245859/50000000000000 : ℝ)^29 := by
    have hnat : (3696372503 : ℕ)^37*50000000000000^29 ≤ 14044667245859^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3696372503 10000000000 14044667245859 50000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (733567483/1250000000 : ℝ)^37 ≤ (10132258887959/20000000000000 : ℝ)^29 := by
    have hnat : (733567483 : ℕ)^37*20000000000000^29 ≤ 10132258887959^29*1250000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      733567483 1250000000 10132258887959 20000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2970193653/10000000000 : ℝ)^37 ≤ (21249371064079/100000000000000 : ℝ)^29 := by
    have hnat : (2970193653 : ℕ)^37*100000000000000^29 ≤ 21249371064079^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2970193653 10000000000 21249371064079 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3696372503/10000000000 : ℝ), (733567483/1250000000 : ℝ), (2970193653/10000000000 : ℝ)] ![(14044667245859/50000000000000 : ℝ), (10132258887959/20000000000000 : ℝ), (21249371064079/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3696372503/10000000000 : ℝ)|^37 ≤ (14044667245859/50000000000000 : ℝ)^29
        have hw : |(3696372503/10000000000 : ℝ)|=(3696372503/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(733567483/1250000000 : ℝ)|^37 ≤ (10132258887959/20000000000000 : ℝ)^29
        have hw : |(733567483/1250000000 : ℝ)|=(733567483/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2970193653/10000000000 : ℝ)|^37 ≤ (21249371064079/100000000000000 : ℝ)^29
        have hw : |(2970193653/10000000000 : ℝ)|=(2970193653/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c313079_s0_20 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (1300123669/5000000000 : ℝ)*x 0 + (3378988611/10000000000 : ℝ)*x 1 + (-321912073/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1300123669/5000000000 : ℝ)^37 ≤ (17932440328127/100000000000000 : ℝ)^29 := by
    have hnat : (1300123669 : ℕ)^37*100000000000000^29 ≤ 17932440328127^29*5000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1300123669 5000000000 17932440328127 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3378988611/10000000000 : ℝ)^37 ≤ (3131171625899/12500000000000 : ℝ)^29 := by
    have hnat : (3378988611 : ℕ)^37*12500000000000^29 ≤ 3131171625899^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3378988611 10000000000 3131171625899 12500000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (321912073/500000000 : ℝ)^37 ≤ (11403637328439/20000000000000 : ℝ)^29 := by
    have hnat : (321912073 : ℕ)^37*20000000000000^29 ≤ 11403637328439^29*500000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      321912073 500000000 11403637328439 20000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1300123669/5000000000 : ℝ), (3378988611/10000000000 : ℝ), (-321912073/500000000 : ℝ)] ![(17932440328127/100000000000000 : ℝ), (3131171625899/12500000000000 : ℝ), (11403637328439/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1300123669/5000000000 : ℝ)|^37 ≤ (17932440328127/100000000000000 : ℝ)^29
        have hw : |(1300123669/5000000000 : ℝ)|=(1300123669/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3378988611/10000000000 : ℝ)|^37 ≤ (3131171625899/12500000000000 : ℝ)^29
        have hw : |(3378988611/10000000000 : ℝ)|=(3378988611/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-321912073/500000000 : ℝ)|^37 ≤ (11403637328439/20000000000000 : ℝ)^29
        have hw : |(-321912073/500000000 : ℝ)|=(321912073/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c313079_s0_21 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-92086659/2000000000 : ℝ)*x 0 + (277235617/500000000 : ℝ)*x 1 + (-2945474129/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (92086659/2000000000 : ℝ)^37 ≤ (1969632159723/100000000000000 : ℝ)^29 := by
    have hnat : (92086659 : ℕ)^37*100000000000000^29 ≤ 1969632159723^29*2000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      92086659 2000000000 1969632159723 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (277235617/500000000 : ℝ)^37 ≤ (942442693937/2000000000000 : ℝ)^29 := by
    have hnat : (277235617 : ℕ)^37*2000000000000^29 ≤ 942442693937^29*500000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      277235617 500000000 942442693937 2000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2945474129/5000000000 : ℝ)^37 ≤ (10181646626283/20000000000000 : ℝ)^29 := by
    have hnat : (2945474129 : ℕ)^37*20000000000000^29 ≤ 10181646626283^29*5000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2945474129 5000000000 10181646626283 20000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-92086659/2000000000 : ℝ), (277235617/500000000 : ℝ), (-2945474129/5000000000 : ℝ)] ![(1969632159723/100000000000000 : ℝ), (942442693937/2000000000000 : ℝ), (10181646626283/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-92086659/2000000000 : ℝ)|^37 ≤ (1969632159723/100000000000000 : ℝ)^29
        have hw : |(-92086659/2000000000 : ℝ)|=(92086659/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(277235617/500000000 : ℝ)|^37 ≤ (942442693937/2000000000000 : ℝ)^29
        have hw : |(277235617/500000000 : ℝ)|=(277235617/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2945474129/5000000000 : ℝ)|^37 ≤ (10181646626283/20000000000000 : ℝ)^29
        have hw : |(-2945474129/5000000000 : ℝ)|=(2945474129/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c313079_s0_22 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (4751012187/5000000000 : ℝ)*x 0 + (-383933961/10000000000 : ℝ)*x 1 + (-28672413/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4751012187/5000000000 : ℝ)^37 ≤ (93690693717099/100000000000000 : ℝ)^29 := by
    have hnat : (4751012187 : ℕ)^37*100000000000000^29 ≤ 93690693717099^29*5000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4751012187 5000000000 93690693717099 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (383933961/10000000000 : ℝ)^37 ≤ (781045997007/50000000000000 : ℝ)^29 := by
    have hnat : (383933961 : ℕ)^37*50000000000000^29 ≤ 781045997007^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      383933961 10000000000 781045997007 50000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (28672413/312500000 : ℝ)^37 ≤ (4747214275101/100000000000000 : ℝ)^29 := by
    have hnat : (28672413 : ℕ)^37*100000000000000^29 ≤ 4747214275101^29*312500000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      28672413 312500000 4747214275101 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4751012187/5000000000 : ℝ), (-383933961/10000000000 : ℝ), (-28672413/312500000 : ℝ)] ![(93690693717099/100000000000000 : ℝ), (781045997007/50000000000000 : ℝ), (4747214275101/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4751012187/5000000000 : ℝ)|^37 ≤ (93690693717099/100000000000000 : ℝ)^29
        have hw : |(4751012187/5000000000 : ℝ)|=(4751012187/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-383933961/10000000000 : ℝ)|^37 ≤ (781045997007/50000000000000 : ℝ)^29
        have hw : |(-383933961/10000000000 : ℝ)|=(383933961/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-28672413/312500000 : ℝ)|^37 ≤ (4747214275101/100000000000000 : ℝ)^29
        have hw : |(-28672413/312500000 : ℝ)|=(28672413/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c313079_s0_23 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (1294212759/5000000000 : ℝ)*x 0 + (594106007/1000000000 : ℝ)*x 1 + (3964053521/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1294212759/5000000000 : ℝ)^37 ≤ (17828486598703/100000000000000 : ℝ)^29 := by
    have hnat : (1294212759 : ℕ)^37*100000000000000^29 ≤ 17828486598703^29*5000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1294212759 5000000000 17828486598703 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (594106007/1000000000 : ℝ)^37 ≤ (51461398363711/100000000000000 : ℝ)^29 := by
    have hnat : (594106007 : ℕ)^37*100000000000000^29 ≤ 51461398363711^29*1000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      594106007 1000000000 51461398363711 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3964053521/10000000000 : ℝ)^37 ≤ (7677528757591/25000000000000 : ℝ)^29 := by
    have hnat : (3964053521 : ℕ)^37*25000000000000^29 ≤ 7677528757591^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3964053521 10000000000 7677528757591 25000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1294212759/5000000000 : ℝ), (594106007/1000000000 : ℝ), (3964053521/10000000000 : ℝ)] ![(17828486598703/100000000000000 : ℝ), (51461398363711/100000000000000 : ℝ), (7677528757591/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1294212759/5000000000 : ℝ)|^37 ≤ (17828486598703/100000000000000 : ℝ)^29
        have hw : |(1294212759/5000000000 : ℝ)|=(1294212759/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(594106007/1000000000 : ℝ)|^37 ≤ (51461398363711/100000000000000 : ℝ)^29
        have hw : |(594106007/1000000000 : ℝ)|=(594106007/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3964053521/10000000000 : ℝ)|^37 ≤ (7677528757591/25000000000000 : ℝ)^29
        have hw : |(3964053521/10000000000 : ℝ)|=(3964053521/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c313079_s0_27 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (1952026277/5000000000 : ℝ)*x 0 + (2765944021/5000000000 : ℝ)*x 1 + (-1574702047/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1952026277/5000000000 : ℝ)^37 ≤ (30118290561183/100000000000000 : ℝ)^29 := by
    have hnat : (1952026277 : ℕ)^37*100000000000000^29 ≤ 30118290561183^29*5000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1952026277 5000000000 30118290561183 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2765944021/5000000000 : ℝ)^37 ≤ (46983125153667/100000000000000 : ℝ)^29 := by
    have hnat : (2765944021 : ℕ)^37*100000000000000^29 ≤ 46983125153667^29*5000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2765944021 5000000000 46983125153667 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1574702047/5000000000 : ℝ)^37 ≤ (457971685557/2000000000000 : ℝ)^29 := by
    have hnat : (1574702047 : ℕ)^37*2000000000000^29 ≤ 457971685557^29*5000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1574702047 5000000000 457971685557 2000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1952026277/5000000000 : ℝ), (2765944021/5000000000 : ℝ), (-1574702047/5000000000 : ℝ)] ![(30118290561183/100000000000000 : ℝ), (46983125153667/100000000000000 : ℝ), (457971685557/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1952026277/5000000000 : ℝ)|^37 ≤ (30118290561183/100000000000000 : ℝ)^29
        have hw : |(1952026277/5000000000 : ℝ)|=(1952026277/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2765944021/5000000000 : ℝ)|^37 ≤ (46983125153667/100000000000000 : ℝ)^29
        have hw : |(2765944021/5000000000 : ℝ)|=(2765944021/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1574702047/5000000000 : ℝ)|^37 ≤ (457971685557/2000000000000 : ℝ)^29
        have hw : |(-1574702047/5000000000 : ℝ)|=(1574702047/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c313079_s1_0 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-2613627761/10000000000 : ℝ)*x 0 + (437882053/1000000000 : ℝ)*x 1 + (-5541030207/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2613627761/10000000000 : ℝ)^37 ≤ (18050256812959/100000000000000 : ℝ)^29 := by
    have hnat : (2613627761 : ℕ)^37*100000000000000^29 ≤ 18050256812959^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2613627761 10000000000 18050256812959 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (437882053/1000000000 : ℝ)^37 ≤ (544805159411/1562500000000 : ℝ)^29 := by
    have hnat : (437882053 : ℕ)^37*1562500000000^29 ≤ 544805159411^29*1000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      437882053 1000000000 544805159411 1562500000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5541030207/10000000000 : ℝ)^37 ≤ (9416442593507/20000000000000 : ℝ)^29 := by
    have hnat : (5541030207 : ℕ)^37*20000000000000^29 ≤ 9416442593507^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5541030207 10000000000 9416442593507 20000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2613627761/10000000000 : ℝ), (437882053/1000000000 : ℝ), (-5541030207/10000000000 : ℝ)] ![(18050256812959/100000000000000 : ℝ), (544805159411/1562500000000 : ℝ), (9416442593507/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2613627761/10000000000 : ℝ)|^37 ≤ (18050256812959/100000000000000 : ℝ)^29
        have hw : |(-2613627761/10000000000 : ℝ)|=(2613627761/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(437882053/1000000000 : ℝ)|^37 ≤ (544805159411/1562500000000 : ℝ)^29
        have hw : |(437882053/1000000000 : ℝ)|=(437882053/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-5541030207/10000000000 : ℝ)|^37 ≤ (9416442593507/20000000000000 : ℝ)^29
        have hw : |(-5541030207/10000000000 : ℝ)|=(5541030207/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c313079_s1_1 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (399514791/625000000 : ℝ)*x 0 + (-1369928629/5000000000 : ℝ)*x 1 + (-3302829101/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (399514791/625000000 : ℝ)^37 ≤ (56498879779983/100000000000000 : ℝ)^29 := by
    have hnat : (399514791 : ℕ)^37*100000000000000^29 ≤ 56498879779983^29*625000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      399514791 625000000 56498879779983 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1369928629/5000000000 : ℝ)^37 ≤ (1198114764951/6250000000000 : ℝ)^29 := by
    have hnat : (1369928629 : ℕ)^37*6250000000000^29 ≤ 1198114764951^29*5000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1369928629 5000000000 1198114764951 6250000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3302829101/10000000000 : ℝ)^37 ≤ (608282099111/2500000000000 : ℝ)^29 := by
    have hnat : (3302829101 : ℕ)^37*2500000000000^29 ≤ 608282099111^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3302829101 10000000000 608282099111 2500000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(399514791/625000000 : ℝ), (-1369928629/5000000000 : ℝ), (-3302829101/10000000000 : ℝ)] ![(56498879779983/100000000000000 : ℝ), (1198114764951/6250000000000 : ℝ), (608282099111/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(399514791/625000000 : ℝ)|^37 ≤ (56498879779983/100000000000000 : ℝ)^29
        have hw : |(399514791/625000000 : ℝ)|=(399514791/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1369928629/5000000000 : ℝ)|^37 ≤ (1198114764951/6250000000000 : ℝ)^29
        have hw : |(-1369928629/5000000000 : ℝ)|=(1369928629/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3302829101/10000000000 : ℝ)|^37 ≤ (608282099111/2500000000000 : ℝ)^29
        have hw : |(-3302829101/10000000000 : ℝ)|=(3302829101/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c313079_s1_2 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (58404429/156250000 : ℝ)*x 0 + (5142371591/10000000000 : ℝ)*x 1 + (58743387/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (58404429/156250000 : ℝ)^37 ≤ (5698484993147/20000000000000 : ℝ)^29 := by
    have hnat : (58404429 : ℕ)^37*20000000000000^29 ≤ 5698484993147^29*156250000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      58404429 156250000 5698484993147 20000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5142371591/10000000000 : ℝ)^37 ≤ (21402002650269/50000000000000 : ℝ)^29 := by
    have hnat : (5142371591 : ℕ)^37*50000000000000^29 ≤ 21402002650269^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5142371591 10000000000 21402002650269 50000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (58743387/156250000 : ℝ)^37 ≤ (28703569709413/100000000000000 : ℝ)^29 := by
    have hnat : (58743387 : ℕ)^37*100000000000000^29 ≤ 28703569709413^29*156250000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      58743387 156250000 28703569709413 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(58404429/156250000 : ℝ), (5142371591/10000000000 : ℝ), (58743387/156250000 : ℝ)] ![(5698484993147/20000000000000 : ℝ), (21402002650269/50000000000000 : ℝ), (28703569709413/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(58404429/156250000 : ℝ)|^37 ≤ (5698484993147/20000000000000 : ℝ)^29
        have hw : |(58404429/156250000 : ℝ)|=(58404429/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5142371591/10000000000 : ℝ)|^37 ≤ (21402002650269/50000000000000 : ℝ)^29
        have hw : |(5142371591/10000000000 : ℝ)|=(5142371591/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(58743387/156250000 : ℝ)|^37 ≤ (28703569709413/100000000000000 : ℝ)^29
        have hw : |(58743387/156250000 : ℝ)|=(58743387/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c313079_s1_6 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (372800001/1000000000 : ℝ)*x 0 + (4870731523/10000000000 : ℝ)*x 1 + (-162406249/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (372800001/1000000000 : ℝ)^37 ≤ (2839633959807/10000000000000 : ℝ)^29 := by
    have hnat : (372800001 : ℕ)^37*10000000000000^29 ≤ 2839633959807^29*1000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      372800001 1000000000 2839633959807 10000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4870731523/10000000000 : ℝ)^37 ≤ (7988095985661/20000000000000 : ℝ)^29 := by
    have hnat : (4870731523 : ℕ)^37*20000000000000^29 ≤ 7988095985661^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4870731523 10000000000 7988095985661 20000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (162406249/400000000 : ℝ)^37 ≤ (3166318045633/10000000000000 : ℝ)^29 := by
    have hnat : (162406249 : ℕ)^37*10000000000000^29 ≤ 3166318045633^29*400000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      162406249 400000000 3166318045633 10000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(372800001/1000000000 : ℝ), (4870731523/10000000000 : ℝ), (-162406249/400000000 : ℝ)] ![(2839633959807/10000000000000 : ℝ), (7988095985661/20000000000000 : ℝ), (3166318045633/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(372800001/1000000000 : ℝ)|^37 ≤ (2839633959807/10000000000000 : ℝ)^29
        have hw : |(372800001/1000000000 : ℝ)|=(372800001/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4870731523/10000000000 : ℝ)|^37 ≤ (7988095985661/20000000000000 : ℝ)^29
        have hw : |(4870731523/10000000000 : ℝ)|=(4870731523/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-162406249/400000000 : ℝ)|^37 ≤ (3166318045633/10000000000000 : ℝ)^29
        have hw : |(-162406249/400000000 : ℝ)|=(162406249/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c313079 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (169487/100000 : ℝ) (176973/100000 : ℝ) (78599/100000 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![true, true, false]]) : False := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (78599/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (78599/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (78599/100000 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (78599/100000 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 0+X 2 0)) ∧ ((-1 : ℝ)*(X 0 0+X 2 0)) ≤ ((-1 : ℝ)*(X 0 2+X 2 2)) ∧ ((-1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 0) ∧ ((-1 : ℝ)*pair X 1 0) ≤ ((-1 : ℝ)*pair X 1 2) ∧ ((-1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (78599/100000 : ℝ)*P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (78599/100000 : ℝ)*P 2 ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base12 : ((-1 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 2).1]
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
  have s0_pow0 : (1 : ℝ) ^ (73/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^73 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^73*1^16 ≤ 1^16*1^73 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 73 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 73 16 (by norm_num) hpowers
    exact h
  have s0_corner0a : (2 : ℝ) ≤ (5820351075331079/5000000000000000 : ℝ) ^ (73/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (5820351075331079/5000000000000000 : ℝ)^73 := by
      have hnat : (2 : ℕ)^16*5000000000000000^73 ≤ 5820351075331079^73*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 5820351075331079 5000000000000000 16 73 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5820351075331079/5000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 73 16 (by norm_num) hpowers
    exact h
  have s0_corner0b : (3 : ℝ) ≤ (12722560406774351/10000000000000000 : ℝ) ^ (73/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (12722560406774351/10000000000000000 : ℝ)^73 := by
      have hnat : (3 : ℕ)^16*10000000000000000^73 ≤ 12722560406774351^73*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 12722560406774351 10000000000000000 16 73 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12722560406774351/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 73 16 (by norm_num) hpowers
    exact h
  have major_s0_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(820351075331079/5000000000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(1081858256112193/10000000000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (73/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (820351075331079/5000000000000000 : ℝ)) (beta := (1081858256112193/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow0,s0_corner0a]) (by linarith only [s0_pow0,s0_corner0b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![true, true, false]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (1 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order0.2.2])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(820351075331079/5000000000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(1081858256112193/10000000000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow1 : (1 : ℝ) ^ (73/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^73 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^73*1^16 ≤ 1^16*1^73 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 73 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 73 16 (by norm_num) hpowers
    exact h
  have s0_corner1a : (2 : ℝ) ≤ (5820351075331079/5000000000000000 : ℝ) ^ (73/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (5820351075331079/5000000000000000 : ℝ)^73 := by
      have hnat : (2 : ℕ)^16*5000000000000000^73 ≤ 5820351075331079^73*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 5820351075331079 5000000000000000 16 73 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5820351075331079/5000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 73 16 (by norm_num) hpowers
    exact h
  have s0_corner1b : (3 : ℝ) ≤ (12722560406774351/10000000000000000 : ℝ) ^ (73/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (12722560406774351/10000000000000000 : ℝ)^73 := by
      have hnat : (3 : ℕ)^16*10000000000000000^73 ≤ 12722560406774351^73*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 12722560406774351 10000000000000000 16 73 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12722560406774351/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 73 16 (by norm_num) hpowers
    exact h
  have major_s0_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(820351075331079/5000000000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2))+(1081858256112193/10000000000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 2 0)) := by
    have hh := chart_majorant (a := (73/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (820351075331079/5000000000000000 : ℝ)) (beta := (1081858256112193/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow1,s0_corner1a]) (by linarith only [s0_pow1,s0_corner1b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![true, true, false]] hX 1 (by
        change ((-1 : ℝ)*pair X 1 2) ≤ (1 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order1.2.2])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(820351075331079/5000000000000000 : ℝ)*((-1 : ℝ)*pair X 1 2)+(1081858256112193/10000000000000000 : ℝ)*((-1 : ℝ)*pair X 1 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow2 : (1 : ℝ) ^ (73/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^73 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^73*1^16 ≤ 1^16*1^73 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 73 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 73 16 (by norm_num) hpowers
    exact h
  have s0_corner2a : (2 : ℝ) ≤ (5820351075331079/5000000000000000 : ℝ) ^ (73/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (5820351075331079/5000000000000000 : ℝ)^73 := by
      have hnat : (2 : ℕ)^16*5000000000000000^73 ≤ 5820351075331079^73*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 5820351075331079 5000000000000000 16 73 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5820351075331079/5000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 73 16 (by norm_num) hpowers
    exact h
  have s0_corner2b : (3 : ℝ) ≤ (12722560406774351/10000000000000000 : ℝ) ^ (73/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (12722560406774351/10000000000000000 : ℝ)^73 := by
      have hnat : (3 : ℕ)^16*10000000000000000^73 ≤ 12722560406774351^73*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 12722560406774351 10000000000000000 16 73 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12722560406774351/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 73 16 (by norm_num) hpowers
    exact h
  have major_s0_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(820351075331079/5000000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(1081858256112193/10000000000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (73/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (820351075331079/5000000000000000 : ℝ)) (beta := (1081858256112193/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow2,s0_corner2a]) (by linarith only [s0_pow2,s0_corner2b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![true, true, false]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (1 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order2.2.2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(820351075331079/5000000000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(1081858256112193/10000000000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s0_1 : ((3993172231/5000000000 : ℝ)*X 1 0+(-1523370593/10000000000 : ℝ)*X 1 1+(-236334163/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c313079_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_2 : ((625633173/2000000000 : ℝ)*X 2 0+(5940469829/10000000000 : ℝ)*X 2 1+(3462651871/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c313079_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_7 : ((-70486227/400000000 : ℝ)*X 0 0+(1521312659/5000000000 : ℝ)*X 0 1+(-7320659603/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c313079_s0_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_8 : ((8031611253/10000000000 : ℝ)*X 1 0+(-366203673/10000000000 : ℝ)*X 1 1+(-1576176837/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c313079_s0_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_9 : ((782848381/5000000000 : ℝ)*X 2 0+(478473063/625000000 : ℝ)*X 2 1+(2776292497/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c313079_s0_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_13 : ((486102037/2000000000 : ℝ)*X 0 0+(1864091579/2500000000 : ℝ)*X 0 1+(-2235002827/10000000000 : ℝ)*X 0 2+(486102037/2000000000 : ℝ)*X 1 0+(1864091579/2500000000 : ℝ)*X 1 1+(-2235002827/10000000000 : ℝ)*X 1 2+(486102037/2000000000 : ℝ)*X 2 0+(1864091579/2500000000 : ℝ)*X 2 1+(-2235002827/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c313079_s0_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_14 : ((-357693321/10000000000 : ℝ)*X 0 0+(1798805807/5000000000 : ℝ)*X 0 1+(-1920656099/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c313079_s0_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_15 : ((565150139/625000000 : ℝ)*X 1 0+(-1357622093/10000000000 : ℝ)*X 1 1+(-837619321/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c313079_s0_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_16 : ((3696372503/10000000000 : ℝ)*X 2 0+(733567483/1250000000 : ℝ)*X 2 1+(2970193653/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c313079_s0_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_20 : ((1300123669/5000000000 : ℝ)*X 0 0+(3378988611/10000000000 : ℝ)*X 0 1+(-321912073/500000000 : ℝ)*X 0 2+(1300123669/5000000000 : ℝ)*X 1 0+(3378988611/10000000000 : ℝ)*X 1 1+(-321912073/500000000 : ℝ)*X 1 2+(1300123669/5000000000 : ℝ)*X 2 0+(3378988611/10000000000 : ℝ)*X 2 1+(-321912073/500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c313079_s0_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_21 : ((-92086659/2000000000 : ℝ)*X 0 0+(277235617/500000000 : ℝ)*X 0 1+(-2945474129/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c313079_s0_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_22 : ((4751012187/5000000000 : ℝ)*X 1 0+(-383933961/10000000000 : ℝ)*X 1 1+(-28672413/312500000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c313079_s0_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_23 : ((1294212759/5000000000 : ℝ)*X 2 0+(594106007/1000000000 : ℝ)*X 2 1+(3964053521/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c313079_s0_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_27 : ((1952026277/5000000000 : ℝ)*X 0 0+(2765944021/5000000000 : ℝ)*X 0 1+(-1574702047/5000000000 : ℝ)*X 0 2+(1952026277/5000000000 : ℝ)*X 1 0+(2765944021/5000000000 : ℝ)*X 1 1+(-1574702047/5000000000 : ℝ)*X 1 2+(1952026277/5000000000 : ℝ)*X 2 0+(2765944021/5000000000 : ℝ)*X 2 1+(-1574702047/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c313079_s0_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s0_0 : (0 : ℝ) ≤ ((35877/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(35877/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (46071306889508077644777/5000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (143847/125000000000 : ℝ)*(base18) + (443959484277/500000000000 : ℝ)*(base39) + (281588997529/250000000000 : ℝ)*(base49) + (1182929/250000000000 : ℝ)*(base53) + (168343805669/250000000000 : ℝ)*(base60) + (1407303143719/500000000000 : ℝ)*(major_s0_0) + (1407303143719/500000000000 : ℝ)*(major_s0_1) + (2814601555721/1000000000000 : ℝ)*(major_s0_2) + (27457891/1000000000000 : ℝ)*(sp_s0_1) + (496063910259/125000000000 : ℝ)*(sp_s0_7) + (3968514113803/1000000000000 : ℝ)*(sp_s0_8) + (1984273727093/500000000000 : ℝ)*(sp_s0_9) + (332132409853/200000000000 : ℝ)*(sp_s0_13) + (15720199/500000000000 : ℝ)*(sp_s0_14) + (332132409853/200000000000 : ℝ)*(f.failure) + (1984273727093/500000000000 : ℝ)*(f.sum) + (120775130098399/625000000000000000000000000 : ℝ)*base63 + (2007635909006153/10000000000000000000000000000 : ℝ)*base65 + (1263224350407199/2500000000000000000000000000 : ℝ)*base67 + (861349128552959/5000000000000000000000000000 : ℝ)*base69 + (1360376736377357/10000000000000000000000000000 : ℝ)*base71 + (1795124020765767/5000000000000000000000000000 : ℝ)*base73 + (2996839454234233/5000000000000000000000000000 : ℝ)*base75 + (1009659137342801/2500000000000000000000000000 : ℝ)*base77 + (282492072983967/1000000000000000000000000000 : ℝ)*base78 + (4589/20000000000000000 : ℝ)*base86 + (4589/20000000000000000 : ℝ)*base88 + (15411/20000000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s0_1 : (0 : ℝ) ≤ ((22949/50000 : ℝ)*X 0 1+(1 : ℝ)*X 0 2+(22949/50000 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (286667635541433533643/62500000000000000000000000 : ℝ) := by norm_num
    linear_combination (1317057946597/1000000000000 : ℝ)*(base39) + (1652819/1000000000000 : ℝ)*(base40) + (90797881987/125000000000 : ℝ)*(base49) + (883889019797/1000000000000 : ℝ)*(base60) + (167205279783/50000000000 : ℝ)*(major_s0_0) + (167205279783/50000000000 : ℝ)*(major_s0_1) + (167205279783/50000000000 : ℝ)*(major_s0_2) + (13857329/1000000000000 : ℝ)*(sp_s0_1) + (12926337/1000000000000 : ℝ)*(sp_s0_7) + (4715121753537/1000000000000 : ℝ)*(sp_s0_14) + (4715088742373/1000000000000 : ℝ)*(sp_s0_15) + (37721077439/8000000000 : ℝ)*(sp_s0_16) + (1973074982541/1000000000000 : ℝ)*(sp_s0_20) + (16040087/500000000000 : ℝ)*(sp_s0_22) + (1973074982541/1000000000000 : ℝ)*(f.failure) + (37721077439/8000000000 : ℝ)*(f.sum) + (84277469511519/100000000000000000000000000 : ℝ)*base63 + (85459430944119/500000000000000000000000000 : ℝ)*base65 + (243260982200857/250000000000000000000000000 : ℝ)*base66 + (121961111824143/250000000000000000000000000 : ℝ)*base68 + (82516424304167/500000000000000000000000000 : ℝ)*base70 + (217193574955881/500000000000000000000000000 : ℝ)*base72 + (297839448155881/500000000000000000000000000 : ℝ)*base75 + (8501611500857/250000000000000000000000000 : ℝ)*base77 + (56344174721519/100000000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base80 + (1/1000000000000 : ℝ)*base83 + (73533/100000000000000000 : ℝ)*base86 + (73533/100000000000000000 : ℝ)*base88 + (73533/100000000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s0_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-909/2500 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-909/2500 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (8919676058413610637297/1250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (264127058899/250000000000 : ℝ)*(base39) + (182556939337/250000000000 : ℝ)*(base49) + (458533/250000000000 : ℝ)*(base50) + (2462787898607/1000000000000 : ℝ)*(major_s0_0) + (2462787898607/1000000000000 : ℝ)*(major_s0_1) + (2462787898607/1000000000000 : ℝ)*(major_s0_2) + (5434273/62500000000 : ℝ)*(sp_s0_2) + (348649/1000000000000 : ℝ)*(sp_s0_9) + (6998901/1000000000000 : ℝ)*(sp_s0_13) + (14385201/1000000000000 : ℝ)*(sp_s0_15) + (868122440279/250000000000 : ℝ)*(sp_s0_21) + (1736237687957/500000000000 : ℝ)*(sp_s0_22) + (1736201232049/500000000000 : ℝ)*(sp_s0_23) + (1453076658611/1000000000000 : ℝ)*(sp_s0_27) + (181635457189/125000000000 : ℝ)*(f.failure) + (868122440279/250000000000 : ℝ)*(f.sum) + (847602071279751/2000000000000000000000000000 : ℝ)*base63 + (1528607717584849/10000000000000000000000000000 : ℝ)*base64 + (630315963406953/5000000000000000000000000000 : ℝ)*base66 + (3930525188406953/5000000000000000000000000000 : ℝ)*base69 + (2433760814770943/10000000000000000000000000000 : ℝ)*base70 + (513137393584849/10000000000000000000000000000 : ℝ)*base72 + (7846153098584849/10000000000000000000000000000 : ℝ)*base75 + (2284369956906953/5000000000000000000000000000 : ℝ)*base77 + (658614421320249/2000000000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base82 + (1/1000000000000 : ℝ)*base84 + (4543/12500000000000000 : ℝ)*base87 + (4543/12500000000000000 : ℝ)*base89 + (4543/12500000000000000 : ℝ)*base91 + hcertificate_margin
  have s1_pow0 : (35877/100000 : ℝ) ^ (73/16 : ℝ) ≤ (930783230645441789/100000000000000000000 : ℝ) := by
    have hpowers : (35877/100000 : ℝ)^73 ≤ (930783230645441789/100000000000000000000 : ℝ)^16 := by
      have hnat : (35877 : ℕ)^73*100000000000000000000^16 ≤ 930783230645441789^16*100000^73 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        35877 100000 930783230645441789 100000000000000000000 73 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (35877/100000 : ℝ)) (X := (930783230645441789/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 73 16 (by norm_num) hpowers
    exact h
  have s1_corner0a : (100930783230645441789/100000000000000000000 : ℝ) ≤ (10020327001521449/10000000000000000 : ℝ) ^ (73/16 : ℝ) := by
    have hpowers : (100930783230645441789/100000000000000000000 : ℝ)^16 ≤ (10020327001521449/10000000000000000 : ℝ)^73 := by
      have hnat : (100930783230645441789 : ℕ)^16*10000000000000000^73 ≤ 10020327001521449^73*100000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100930783230645441789 100000000000000000000 10020327001521449 10000000000000000 16 73 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10020327001521449/10000000000000000 : ℝ)) (X := (100930783230645441789/100000000000000000000 : ℝ)) (by norm_num) 73 16 (by norm_num) hpowers
    exact h
  have s1_corner0b : (50930783230645441789/50000000000000000000 : ℝ) ≤ (1004050815652361/1000000000000000 : ℝ) ^ (73/16 : ℝ) := by
    have hpowers : (50930783230645441789/50000000000000000000 : ℝ)^16 ≤ (1004050815652361/1000000000000000 : ℝ)^73 := by
      have hnat : (50930783230645441789 : ℕ)^16*1000000000000000^73 ≤ 1004050815652361^73*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50930783230645441789 50000000000000000000 1004050815652361 1000000000000000 16 73 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1004050815652361/1000000000000000 : ℝ)) (X := (50930783230645441789/50000000000000000000 : ℝ)) (by norm_num) 73 16 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(20327001521449/3587700000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(6727051667387/1195900000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (73/16 : ℝ)) (rho := (35877/100000 : ℝ)) (alpha := (20327001521449/3587700000000000 : ℝ)) (beta := (6727051667387/1195900000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![true, true, false]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (35877/100000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(20327001521449/3587700000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(6727051667387/1195900000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (22949/50000 : ℝ) ^ (73/16 : ℝ) ≤ (286374297859053197/10000000000000000000 : ℝ) := by
    have hpowers : (22949/50000 : ℝ)^73 ≤ (286374297859053197/10000000000000000000 : ℝ)^16 := by
      have hnat : (22949 : ℕ)^73*10000000000000000000^16 ≤ 286374297859053197^16*50000^73 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        22949 50000 286374297859053197 10000000000000000000 73 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (22949/50000 : ℝ)) (X := (286374297859053197/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 73 16 (by norm_num) hpowers
    exact h
  have s1_corner1a : (10286374297859053197/10000000000000000000 : ℝ) ≤ (10062076908654199/10000000000000000 : ℝ) ^ (73/16 : ℝ) := by
    have hpowers : (10286374297859053197/10000000000000000000 : ℝ)^16 ≤ (10062076908654199/10000000000000000 : ℝ)^73 := by
      have hnat : (10286374297859053197 : ℕ)^16*10000000000000000^73 ≤ 10062076908654199^73*10000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10286374297859053197 10000000000000000000 10062076908654199 10000000000000000 16 73 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10062076908654199/10000000000000000 : ℝ)) (X := (10286374297859053197/10000000000000000000 : ℝ)) (by norm_num) 73 16 (by norm_num) hpowers
    exact h
  have s1_corner1b : (5286374297859053197/5000000000000000000 : ℝ) ≤ (5061409350449593/5000000000000000 : ℝ) ^ (73/16 : ℝ) := by
    have hpowers : (5286374297859053197/5000000000000000000 : ℝ)^16 ≤ (5061409350449593/5000000000000000 : ℝ)^73 := by
      have hnat : (5286374297859053197 : ℕ)^16*5000000000000000^73 ≤ 5061409350449593^73*5000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5286374297859053197 5000000000000000000 5061409350449593 5000000000000000 16 73 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5061409350449593/5000000000000000 : ℝ)) (X := (5286374297859053197/5000000000000000000 : ℝ)) (by norm_num) 73 16 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(62076908654199/4589800000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2))+(60741792244987/4589800000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 2 0)) := by
    have hh := chart_majorant (a := (73/16 : ℝ)) (rho := (22949/50000 : ℝ)) (alpha := (62076908654199/4589800000000000 : ℝ)) (beta := (60741792244987/4589800000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![true, true, false]] hX 1 (by
        change ((-1 : ℝ)*pair X 1 2) ≤ (22949/50000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(62076908654199/4589800000000000 : ℝ)*((-1 : ℝ)*pair X 1 2)+(60741792244987/4589800000000000 : ℝ)*((-1 : ℝ)*pair X 1 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (909/2500 : ℝ) ^ (73/16 : ℝ) ≤ (494670978696763449/50000000000000000000 : ℝ) := by
    have hpowers : (909/2500 : ℝ)^73 ≤ (494670978696763449/50000000000000000000 : ℝ)^16 := by
      have hnat : (909 : ℕ)^73*50000000000000000000^16 ≤ 494670978696763449^16*2500^73 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        909 2500 494670978696763449 50000000000000000000 73 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (909/2500 : ℝ)) (X := (494670978696763449/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 73 16 (by norm_num) hpowers
    exact h
  have s1_corner2a : (50494670978696763449/50000000000000000000 : ℝ) ≤ (5010800470283743/5000000000000000 : ℝ) ^ (73/16 : ℝ) := by
    have hpowers : (50494670978696763449/50000000000000000000 : ℝ)^16 ≤ (5010800470283743/5000000000000000 : ℝ)^73 := by
      have hnat : (50494670978696763449 : ℕ)^16*5000000000000000^73 ≤ 5010800470283743^73*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50494670978696763449 50000000000000000000 5010800470283743 5000000000000000 16 73 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5010800470283743/5000000000000000 : ℝ)) (X := (50494670978696763449/50000000000000000000 : ℝ)) (by norm_num) 73 16 (by norm_num) hpowers
    exact h
  have s1_corner2b : (25494670978696763449/25000000000000000000 : ℝ) ≤ (2008607455062367/2000000000000000 : ℝ) ^ (73/16 : ℝ) := by
    have hpowers : (25494670978696763449/25000000000000000000 : ℝ)^16 ≤ (2008607455062367/2000000000000000 : ℝ)^73 := by
      have hnat : (25494670978696763449 : ℕ)^16*2000000000000000^73 ≤ 2008607455062367^73*25000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25494670978696763449 25000000000000000000 2008607455062367 2000000000000000 16 73 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2008607455062367/2000000000000000 : ℝ)) (X := (25494670978696763449/25000000000000000000 : ℝ)) (by norm_num) 73 16 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(10800470283743/1818000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(7145444914783/1212000000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (73/16 : ℝ)) (rho := (909/2500 : ℝ)) (alpha := (10800470283743/1818000000000000 : ℝ)) (beta := (7145444914783/1212000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![true, true, false]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (909/2500 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(10800470283743/1818000000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(7145444914783/1212000000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-2613627761/10000000000 : ℝ)*X 0 0+(437882053/1000000000 : ℝ)*X 0 1+(-5541030207/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c313079_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_1 : ((399514791/625000000 : ℝ)*X 1 0+(-1369928629/5000000000 : ℝ)*X 1 1+(-3302829101/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c313079_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((58404429/156250000 : ℝ)*X 2 0+(5142371591/10000000000 : ℝ)*X 2 1+(58743387/156250000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c313079_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_6 : ((372800001/1000000000 : ℝ)*X 0 0+(4870731523/10000000000 : ℝ)*X 0 1+(-162406249/400000000 : ℝ)*X 0 2+(372800001/1000000000 : ℝ)*X 1 0+(4870731523/10000000000 : ℝ)*X 1 1+(-162406249/400000000 : ℝ)*X 1 2+(372800001/1000000000 : ℝ)*X 2 0+(4870731523/10000000000 : ℝ)*X 2 1+(-162406249/400000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c313079_s1_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have hsep : (-358461/50000 : ℝ) < ((-169487/100000 : ℝ)*P 0+(-169487/100000 : ℝ)*P 1+(-169487/100000 : ℝ)*P 2+(1 : ℝ)*T) := by
    have hcertificate_margin : (-358461/50000 : ℝ) < (-2952991233424325252690413610309851/415787342865000000000000000000000 : ℝ) := by norm_num
    linear_combination (37063/1000000000000 : ℝ)*(base12) + (20541/500000000000 : ℝ)*(base23) + (284531/250000000000 : ℝ)*(base25) + (497412428159/1000000000000 : ℝ)*(base39) + (414738193021/1000000000000 : ℝ)*(base49) + (181151921909/1000000000000 : ℝ)*(base60) + (688019/1000000000000 : ℝ)*(ratio_s0_0) + (4261/200000000000 : ℝ)*(ratio_s0_2) + (169487/100000 : ℝ)*(major_s1_0) + (169487/100000 : ℝ)*(major_s1_1) + (169487/100000 : ℝ)*(major_s1_2) + (2367389033411/1000000000000 : ℝ)*(sp_s1_0) + (1183694535237/500000000000 : ℝ)*(sp_s1_1) + (591846972817/250000000000 : ℝ)*(sp_s1_2) + (1 : ℝ)*(sp_s1_6) + (1183694535237/500000000000 : ℝ)*(f.sum) + (42703977962706211/208606410000000000000000000000 : ℝ)*base63 + (154798850749/303000000000000000000000 : ℝ)*base64 + (36149362278927/229490000000000000000000000 : ℝ)*base66 + (291058902869/568125000000000000000000 : ℝ)*base69 + (597965371095043/3019647500000000000000000000 : ℝ)*base70 + (31223067065417/59795000000000000000000000 : ℝ)*base72 + (1629279053303/3585781250000000000000000 : ℝ)*base74 + (37341934405181/89692500000000000000000000 : ℝ)*base77 + (36622059370445437/85764715937500000000000000000 : ℝ)*base78 + hcertificate_margin
  linarith only [hsep,f.failure]

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
namespace HlawkaSchatten.DiagonalCutoff4
theorem coarse_distinct_p013_b031 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ))
    (c : Fin 88) (hlo : 78 ≤ c.val) (hhi : c.val < 81)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (169487/100000 : ℝ) (176973/100000 : ℝ) (78599/100000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  have hc : c=78 ∨ c=79 ∨ c=80 := by omega
  rcases hc with rfl|rfl|rfl
  · exact collision_c313078 p hpa (by linarith only [hpb]) X hX
  · exact collision_c313079 p hpa (by linarith only [hpb]) X hX
  · exact collision_c313080 p hpa (by linarith only [hpb]) X hX

end HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ))
    (c : Fin 88) (hlo : 78 ≤ c.val) (hhi : c.val < 81)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (169487/100000 : ℝ) (176973/100000 : ℝ) (78599/100000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  exact HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p013_b031 p hpa hpb c hlo hhi hn63 hn87 X hX

#print axioms solution
