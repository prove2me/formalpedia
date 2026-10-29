-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p013_b034
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:32:47.581338+00:00
-- url     : https://prove2.me/submissions/6dc16d00-5105-4212-be10-02393e6eb4b1

import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c313086_s0
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c313086_s1
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c313086_s2
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
theorem HlawkaSchatten.DiagonalCutoff4.collision_c313086 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (169487/100000 : ℝ) (176973/100000 : ℝ) (78599/100000 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, false, true]]) : False := by
  have h0 := collision_c313086_s0 p hpa hpb X hX
  have h1 := collision_c313086_s1 p hpa hpb X hX h0
  exact collision_c313086_s2 p hpa hpb X hX h1

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
theorem collision_support_c313085_s0_1 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (5579033109/10000000000 : ℝ)*x 0 + (1366793171/5000000000 : ℝ)*x 1 + (2116429981/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5579033109/10000000000 : ℝ)^37 ≤ (4749459221879/10000000000000 : ℝ)^29 := by
    have hnat : (5579033109 : ℕ)^37*10000000000000^29 ≤ 4749459221879^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5579033109 10000000000 4749459221879 10000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1366793171/5000000000 : ℝ)^37 ≤ (19113874916147/100000000000000 : ℝ)^29 := by
    have hnat : (1366793171 : ℕ)^37*100000000000000^29 ≤ 19113874916147^29*5000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1366793171 5000000000 19113874916147 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2116429981/5000000000 : ℝ)^37 ≤ (33391532859893/100000000000000 : ℝ)^29 := by
    have hnat : (2116429981 : ℕ)^37*100000000000000^29 ≤ 33391532859893^29*5000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2116429981 5000000000 33391532859893 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5579033109/10000000000 : ℝ), (1366793171/5000000000 : ℝ), (2116429981/5000000000 : ℝ)] ![(4749459221879/10000000000000 : ℝ), (19113874916147/100000000000000 : ℝ), (33391532859893/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5579033109/10000000000 : ℝ)|^37 ≤ (4749459221879/10000000000000 : ℝ)^29
        have hw : |(5579033109/10000000000 : ℝ)|=(5579033109/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1366793171/5000000000 : ℝ)|^37 ≤ (19113874916147/100000000000000 : ℝ)^29
        have hw : |(1366793171/5000000000 : ℝ)|=(1366793171/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2116429981/5000000000 : ℝ)|^37 ≤ (33391532859893/100000000000000 : ℝ)^29
        have hw : |(2116429981/5000000000 : ℝ)|=(2116429981/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c313085_s0_2 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (3896446319/10000000000 : ℝ)*x 0 + (-1610555841/5000000000 : ℝ)*x 1 + (-2738570743/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3896446319/10000000000 : ℝ)^37 ≤ (30043444086393/100000000000000 : ℝ)^29 := by
    have hnat : (3896446319 : ℕ)^37*100000000000000^29 ≤ 30043444086393^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3896446319 10000000000 30043444086393 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1610555841/5000000000 : ℝ)^37 ≤ (23565857120729/100000000000000 : ℝ)^29 := by
    have hnat : (1610555841 : ℕ)^37*100000000000000^29 ≤ 23565857120729^29*5000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1610555841 5000000000 23565857120729 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2738570743/5000000000 : ℝ)^37 ≤ (2899418673213/6250000000000 : ℝ)^29 := by
    have hnat : (2738570743 : ℕ)^37*6250000000000^29 ≤ 2899418673213^29*5000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2738570743 5000000000 2899418673213 6250000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3896446319/10000000000 : ℝ), (-1610555841/5000000000 : ℝ), (-2738570743/5000000000 : ℝ)] ![(30043444086393/100000000000000 : ℝ), (23565857120729/100000000000000 : ℝ), (2899418673213/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3896446319/10000000000 : ℝ)|^37 ≤ (30043444086393/100000000000000 : ℝ)^29
        have hw : |(3896446319/10000000000 : ℝ)|=(3896446319/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1610555841/5000000000 : ℝ)|^37 ≤ (23565857120729/100000000000000 : ℝ)^29
        have hw : |(-1610555841/5000000000 : ℝ)|=(1610555841/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2738570743/5000000000 : ℝ)|^37 ≤ (2899418673213/6250000000000 : ℝ)^29
        have hw : |(-2738570743/5000000000 : ℝ)|=(2738570743/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c313085_s0_6 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (6750577451/10000000000 : ℝ)*x 0 + (-539389867/2500000000 : ℝ)*x 1 + (53204513/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6750577451/10000000000 : ℝ)^37 ≤ (12114139051299/20000000000000 : ℝ)^29 := by
    have hnat : (6750577451 : ℕ)^37*20000000000000^29 ≤ 12114139051299^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6750577451 10000000000 12114139051299 20000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (539389867/2500000000 : ℝ)^37 ≤ (3533201259507/25000000000000 : ℝ)^29 := by
    have hnat : (539389867 : ℕ)^37*25000000000000^29 ≤ 3533201259507^29*2500000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      539389867 2500000000 3533201259507 25000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (53204513/156250000 : ℝ)^37 ≤ (3162062461417/12500000000000 : ℝ)^29 := by
    have hnat : (53204513 : ℕ)^37*12500000000000^29 ≤ 3162062461417^29*156250000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      53204513 156250000 3162062461417 12500000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6750577451/10000000000 : ℝ), (-539389867/2500000000 : ℝ), (53204513/156250000 : ℝ)] ![(12114139051299/20000000000000 : ℝ), (3533201259507/25000000000000 : ℝ), (3162062461417/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6750577451/10000000000 : ℝ)|^37 ≤ (12114139051299/20000000000000 : ℝ)^29
        have hw : |(6750577451/10000000000 : ℝ)|=(6750577451/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-539389867/2500000000 : ℝ)|^37 ≤ (3533201259507/25000000000000 : ℝ)^29
        have hw : |(-539389867/2500000000 : ℝ)|=(539389867/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(53204513/156250000 : ℝ)|^37 ≤ (3162062461417/12500000000000 : ℝ)^29
        have hw : |(53204513/156250000 : ℝ)|=(53204513/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c313085_s0_7 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-847758273/5000000000 : ℝ)*x 0 + (-122033149/156250000 : ℝ)*x 1 + (2453865293/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (847758273/5000000000 : ℝ)^37 ≤ (10391917645387/100000000000000 : ℝ)^29 := by
    have hnat : (847758273 : ℕ)^37*100000000000000^29 ≤ 10391917645387^29*5000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      847758273 5000000000 10391917645387 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (122033149/156250000 : ℝ)^37 ≤ (4559593920589/6250000000000 : ℝ)^29 := by
    have hnat : (122033149 : ℕ)^37*6250000000000^29 ≤ 4559593920589^29*156250000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      122033149 156250000 4559593920589 6250000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2453865293/10000000000 : ℝ)^37 ≤ (16654579608669/100000000000000 : ℝ)^29 := by
    have hnat : (2453865293 : ℕ)^37*100000000000000^29 ≤ 16654579608669^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2453865293 10000000000 16654579608669 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-847758273/5000000000 : ℝ), (-122033149/156250000 : ℝ), (2453865293/10000000000 : ℝ)] ![(10391917645387/100000000000000 : ℝ), (4559593920589/6250000000000 : ℝ), (16654579608669/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-847758273/5000000000 : ℝ)|^37 ≤ (10391917645387/100000000000000 : ℝ)^29
        have hw : |(-847758273/5000000000 : ℝ)|=(847758273/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-122033149/156250000 : ℝ)|^37 ≤ (4559593920589/6250000000000 : ℝ)^29
        have hw : |(-122033149/156250000 : ℝ)|=(122033149/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2453865293/10000000000 : ℝ)|^37 ≤ (16654579608669/100000000000000 : ℝ)^29
        have hw : |(2453865293/10000000000 : ℝ)|=(2453865293/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c313085_s0_8 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (5665525443/10000000000 : ℝ)*x 0 + (2534483939/10000000000 : ℝ)*x 1 + (4313782919/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5665525443/10000000000 : ℝ)^37 ≤ (9687205646867/20000000000000 : ℝ)^29 := by
    have hnat : (5665525443 : ℕ)^37*20000000000000^29 ≤ 9687205646867^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5665525443 10000000000 9687205646867 20000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2534483939/10000000000 : ℝ)^37 ≤ (8677912841973/50000000000000 : ℝ)^29 := by
    have hnat : (2534483939 : ℕ)^37*50000000000000^29 ≤ 8677912841973^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2534483939 10000000000 8677912841973 50000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4313782919/10000000000 : ℝ)^37 ≤ (34208146063649/100000000000000 : ℝ)^29 := by
    have hnat : (4313782919 : ℕ)^37*100000000000000^29 ≤ 34208146063649^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4313782919 10000000000 34208146063649 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5665525443/10000000000 : ℝ), (2534483939/10000000000 : ℝ), (4313782919/10000000000 : ℝ)] ![(9687205646867/20000000000000 : ℝ), (8677912841973/50000000000000 : ℝ), (34208146063649/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5665525443/10000000000 : ℝ)|^37 ≤ (9687205646867/20000000000000 : ℝ)^29
        have hw : |(5665525443/10000000000 : ℝ)|=(5665525443/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2534483939/10000000000 : ℝ)|^37 ≤ (8677912841973/50000000000000 : ℝ)^29
        have hw : |(2534483939/10000000000 : ℝ)|=(2534483939/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4313782919/10000000000 : ℝ)|^37 ≤ (34208146063649/100000000000000 : ℝ)^29
        have hw : |(4313782919/10000000000 : ℝ)|=(4313782919/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c313085_s0_9 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (4076638037/10000000000 : ℝ)*x 0 + (-1408905799/5000000000 : ℝ)*x 1 + (-5653445943/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4076638037/10000000000 : ℝ)^37 ≤ (795681584041/2500000000000 : ℝ)^29 := by
    have hnat : (4076638037 : ℕ)^37*2500000000000^29 ≤ 795681584041^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4076638037 10000000000 795681584041 2500000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1408905799/5000000000 : ℝ)^37 ≤ (9934214423653/50000000000000 : ℝ)^29 := by
    have hnat : (1408905799 : ℕ)^37*50000000000000^29 ≤ 9934214423653^29*5000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1408905799 5000000000 9934214423653 50000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5653445943/10000000000 : ℝ)^37 ≤ (48304307782951/100000000000000 : ℝ)^29 := by
    have hnat : (5653445943 : ℕ)^37*100000000000000^29 ≤ 48304307782951^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5653445943 10000000000 48304307782951 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4076638037/10000000000 : ℝ), (-1408905799/5000000000 : ℝ), (-5653445943/10000000000 : ℝ)] ![(795681584041/2500000000000 : ℝ), (9934214423653/50000000000000 : ℝ), (48304307782951/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4076638037/10000000000 : ℝ)|^37 ≤ (795681584041/2500000000000 : ℝ)^29
        have hw : |(4076638037/10000000000 : ℝ)|=(4076638037/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1408905799/5000000000 : ℝ)|^37 ≤ (9934214423653/50000000000000 : ℝ)^29
        have hw : |(-1408905799/5000000000 : ℝ)|=(1408905799/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-5653445943/10000000000 : ℝ)|^37 ≤ (48304307782951/100000000000000 : ℝ)^29
        have hw : |(-5653445943/10000000000 : ℝ)|=(5653445943/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c313085_s0_13 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (7486161521/10000000000 : ℝ)*x 0 + (-285205179/2000000000 : ℝ)*x 1 + (1556011379/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (7486161521/10000000000 : ℝ)^37 ≤ (69114962078937/100000000000000 : ℝ)^29 := by
    have hnat : (7486161521 : ℕ)^37*100000000000000^29 ≤ 69114962078937^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7486161521 10000000000 69114962078937 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (285205179/2000000000 : ℝ)^37 ≤ (416632604849/5000000000000 : ℝ)^29 := by
    have hnat : (285205179 : ℕ)^37*5000000000000^29 ≤ 416632604849^29*2000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      285205179 2000000000 416632604849 5000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1556011379/5000000000 : ℝ)^37 ≤ (22552385802211/100000000000000 : ℝ)^29 := by
    have hnat : (1556011379 : ℕ)^37*100000000000000^29 ≤ 22552385802211^29*5000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1556011379 5000000000 22552385802211 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(7486161521/10000000000 : ℝ), (-285205179/2000000000 : ℝ), (1556011379/5000000000 : ℝ)] ![(69114962078937/100000000000000 : ℝ), (416632604849/5000000000000 : ℝ), (22552385802211/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(7486161521/10000000000 : ℝ)|^37 ≤ (69114962078937/100000000000000 : ℝ)^29
        have hw : |(7486161521/10000000000 : ℝ)|=(7486161521/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-285205179/2000000000 : ℝ)|^37 ≤ (416632604849/5000000000000 : ℝ)^29
        have hw : |(-285205179/2000000000 : ℝ)|=(285205179/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1556011379/5000000000 : ℝ)|^37 ≤ (22552385802211/100000000000000 : ℝ)^29
        have hw : |(1556011379/5000000000 : ℝ)|=(1556011379/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c313085_s0_14 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-1990672751/10000000000 : ℝ)*x 0 + (-7236076783/10000000000 : ℝ)*x 1 + (2949856881/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1990672751/10000000000 : ℝ)^37 ≤ (49817342987/390625000000 : ℝ)^29 := by
    have hnat : (1990672751 : ℕ)^37*390625000000^29 ≤ 49817342987^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1990672751 10000000000 49817342987 390625000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (7236076783/10000000000 : ℝ)^37 ≤ (66182843047587/100000000000000 : ℝ)^29 := by
    have hnat : (7236076783 : ℕ)^37*100000000000000^29 ≤ 66182843047587^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7236076783 10000000000 66182843047587 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2949856881/10000000000 : ℝ)^37 ≤ (1053195856823/5000000000000 : ℝ)^29 := by
    have hnat : (2949856881 : ℕ)^37*5000000000000^29 ≤ 1053195856823^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2949856881 10000000000 1053195856823 5000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1990672751/10000000000 : ℝ), (-7236076783/10000000000 : ℝ), (2949856881/10000000000 : ℝ)] ![(49817342987/390625000000 : ℝ), (66182843047587/100000000000000 : ℝ), (1053195856823/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1990672751/10000000000 : ℝ)|^37 ≤ (49817342987/390625000000 : ℝ)^29
        have hw : |(-1990672751/10000000000 : ℝ)|=(1990672751/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-7236076783/10000000000 : ℝ)|^37 ≤ (66182843047587/100000000000000 : ℝ)^29
        have hw : |(-7236076783/10000000000 : ℝ)|=(7236076783/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2949856881/10000000000 : ℝ)|^37 ≤ (1053195856823/5000000000000 : ℝ)^29
        have hw : |(2949856881/10000000000 : ℝ)|=(2949856881/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c313085_s0_15 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (2505463029/5000000000 : ℝ)*x 0 + (2981293173/10000000000 : ℝ)*x 1 + (4610309959/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2505463029/5000000000 : ℝ)^37 ≤ (10353251405001/25000000000000 : ℝ)^29 := by
    have hnat : (2505463029 : ℕ)^37*25000000000000^29 ≤ 10353251405001^29*5000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2505463029 5000000000 10353251405001 25000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2981293173/10000000000 : ℝ)^37 ≤ (21350737186629/100000000000000 : ℝ)^29 := by
    have hnat : (2981293173 : ℕ)^37*100000000000000^29 ≤ 21350737186629^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2981293173 10000000000 21350737186629 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4610309959/10000000000 : ℝ)^37 ≤ (37236257181641/100000000000000 : ℝ)^29 := by
    have hnat : (4610309959 : ℕ)^37*100000000000000^29 ≤ 37236257181641^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4610309959 10000000000 37236257181641 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2505463029/5000000000 : ℝ), (2981293173/10000000000 : ℝ), (4610309959/10000000000 : ℝ)] ![(10353251405001/25000000000000 : ℝ), (21350737186629/100000000000000 : ℝ), (37236257181641/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2505463029/5000000000 : ℝ)|^37 ≤ (10353251405001/25000000000000 : ℝ)^29
        have hw : |(2505463029/5000000000 : ℝ)|=(2505463029/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2981293173/10000000000 : ℝ)|^37 ≤ (21350737186629/100000000000000 : ℝ)^29
        have hw : |(2981293173/10000000000 : ℝ)|=(2981293173/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4610309959/10000000000 : ℝ)|^37 ≤ (37236257181641/100000000000000 : ℝ)^29
        have hw : |(4610309959/10000000000 : ℝ)|=(4610309959/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c313085_s0_16 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (1968986847/5000000000 : ℝ)*x 0 + (-799405309/2500000000 : ℝ)*x 1 + (-545954419/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1968986847/5000000000 : ℝ)^37 ≤ (30452568647789/100000000000000 : ℝ)^29 := by
    have hnat : (1968986847 : ℕ)^37*100000000000000^29 ≤ 30452568647789^29*5000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1968986847 5000000000 30452568647789 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (799405309/2500000000 : ℝ)^37 ≤ (23346811485057/100000000000000 : ℝ)^29 := by
    have hnat : (799405309 : ℕ)^37*100000000000000^29 ≤ 23346811485057^29*2500000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      799405309 2500000000 23346811485057 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (545954419/1000000000 : ℝ)^37 ≤ (23100309922873/50000000000000 : ℝ)^29 := by
    have hnat : (545954419 : ℕ)^37*50000000000000^29 ≤ 23100309922873^29*1000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      545954419 1000000000 23100309922873 50000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1968986847/5000000000 : ℝ), (-799405309/2500000000 : ℝ), (-545954419/1000000000 : ℝ)] ![(30452568647789/100000000000000 : ℝ), (23346811485057/100000000000000 : ℝ), (23100309922873/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1968986847/5000000000 : ℝ)|^37 ≤ (30452568647789/100000000000000 : ℝ)^29
        have hw : |(1968986847/5000000000 : ℝ)|=(1968986847/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-799405309/2500000000 : ℝ)|^37 ≤ (23346811485057/100000000000000 : ℝ)^29
        have hw : |(-799405309/2500000000 : ℝ)|=(799405309/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-545954419/1000000000 : ℝ)|^37 ≤ (23100309922873/50000000000000 : ℝ)^29
        have hw : |(-545954419/1000000000 : ℝ)|=(545954419/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c313085_s0_20 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (488640129/625000000 : ℝ)*x 0 + (-134951617/1000000000 : ℝ)*x 1 + (685337761/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (488640129/625000000 : ℝ)^37 ≤ (73050294540081/100000000000000 : ℝ)^29 := by
    have hnat : (488640129 : ℕ)^37*100000000000000^29 ≤ 73050294540081^29*625000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      488640129 625000000 73050294540081 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (134951617/1000000000 : ℝ)^37 ≤ (7766533532573/100000000000000 : ℝ)^29 := by
    have hnat : (134951617 : ℕ)^37*100000000000000^29 ≤ 7766533532573^29*1000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      134951617 1000000000 7766533532573 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (685337761/2500000000 : ℝ)^37 ≤ (9591585960599/50000000000000 : ℝ)^29 := by
    have hnat : (685337761 : ℕ)^37*50000000000000^29 ≤ 9591585960599^29*2500000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      685337761 2500000000 9591585960599 50000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(488640129/625000000 : ℝ), (-134951617/1000000000 : ℝ), (685337761/2500000000 : ℝ)] ![(73050294540081/100000000000000 : ℝ), (7766533532573/100000000000000 : ℝ), (9591585960599/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(488640129/625000000 : ℝ)|^37 ≤ (73050294540081/100000000000000 : ℝ)^29
        have hw : |(488640129/625000000 : ℝ)|=(488640129/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-134951617/1000000000 : ℝ)|^37 ≤ (7766533532573/100000000000000 : ℝ)^29
        have hw : |(-134951617/1000000000 : ℝ)|=(134951617/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(685337761/2500000000 : ℝ)|^37 ≤ (9591585960599/50000000000000 : ℝ)^29
        have hw : |(685337761/2500000000 : ℝ)|=(685337761/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c313085_s0_21 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-340474421/2000000000 : ℝ)*x 0 + (-301499143/400000000 : ℝ)*x 1 + (2814032233/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (340474421/2000000000 : ℝ)^37 ≤ (2089111365989/20000000000000 : ℝ)^29 := by
    have hnat : (340474421 : ℕ)^37*20000000000000^29 ≤ 2089111365989^29*2000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      340474421 2000000000 2089111365989 20000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (301499143/400000000 : ℝ)^37 ≤ (69720007642713/100000000000000 : ℝ)^29 := by
    have hnat : (301499143 : ℕ)^37*100000000000000^29 ≤ 69720007642713^29*400000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      301499143 400000000 69720007642713 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2814032233/10000000000 : ℝ)^37 ≤ (4958608878381/25000000000000 : ℝ)^29 := by
    have hnat : (2814032233 : ℕ)^37*25000000000000^29 ≤ 4958608878381^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2814032233 10000000000 4958608878381 25000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-340474421/2000000000 : ℝ), (-301499143/400000000 : ℝ), (2814032233/10000000000 : ℝ)] ![(2089111365989/20000000000000 : ℝ), (69720007642713/100000000000000 : ℝ), (4958608878381/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-340474421/2000000000 : ℝ)|^37 ≤ (2089111365989/20000000000000 : ℝ)^29
        have hw : |(-340474421/2000000000 : ℝ)|=(340474421/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-301499143/400000000 : ℝ)|^37 ≤ (69720007642713/100000000000000 : ℝ)^29
        have hw : |(-301499143/400000000 : ℝ)|=(301499143/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2814032233/10000000000 : ℝ)|^37 ≤ (4958608878381/25000000000000 : ℝ)^29
        have hw : |(2814032233/10000000000 : ℝ)|=(2814032233/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c313085_s0_22 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (5888818401/10000000000 : ℝ)*x 0 + (163474157/625000000 : ℝ)*x 1 + (3998169917/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5888818401/10000000000 : ℝ)^37 ≤ (50884751118221/100000000000000 : ℝ)^29 := by
    have hnat : (5888818401 : ℕ)^37*100000000000000^29 ≤ 50884751118221^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5888818401 10000000000 50884751118221 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (163474157/625000000 : ℝ)^37 ≤ (1806751787411/10000000000000 : ℝ)^29 := by
    have hnat : (163474157 : ℕ)^37*10000000000000^29 ≤ 1806751787411^29*625000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      163474157 625000000 1806751787411 10000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3998169917/10000000000 : ℝ)^37 ≤ (3104773100229/10000000000000 : ℝ)^29 := by
    have hnat : (3998169917 : ℕ)^37*10000000000000^29 ≤ 3104773100229^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3998169917 10000000000 3104773100229 10000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5888818401/10000000000 : ℝ), (163474157/625000000 : ℝ), (3998169917/10000000000 : ℝ)] ![(50884751118221/100000000000000 : ℝ), (1806751787411/10000000000000 : ℝ), (3104773100229/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5888818401/10000000000 : ℝ)|^37 ≤ (50884751118221/100000000000000 : ℝ)^29
        have hw : |(5888818401/10000000000 : ℝ)|=(5888818401/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(163474157/625000000 : ℝ)|^37 ≤ (1806751787411/10000000000000 : ℝ)^29
        have hw : |(163474157/625000000 : ℝ)|=(163474157/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3998169917/10000000000 : ℝ)|^37 ≤ (3104773100229/10000000000000 : ℝ)^29
        have hw : |(3998169917/10000000000 : ℝ)|=(3998169917/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c313085_s0_23 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (1816393739/5000000000 : ℝ)*x 0 + (-822883009/2500000000 : ℝ)*x 1 + (-226123981/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1816393739/5000000000 : ℝ)^37 ≤ (686857895547/2500000000000 : ℝ)^29 := by
    have hnat : (1816393739 : ℕ)^37*2500000000000^29 ≤ 686857895547^29*5000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1816393739 5000000000 686857895547 2500000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (822883009/2500000000 : ℝ)^37 ≤ (12112576370783/50000000000000 : ℝ)^29 := by
    have hnat : (822883009 : ℕ)^37*50000000000000^29 ≤ 12112576370783^29*2500000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      822883009 2500000000 12112576370783 50000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (226123981/400000000 : ℝ)^37 ≤ (48300531425249/100000000000000 : ℝ)^29 := by
    have hnat : (226123981 : ℕ)^37*100000000000000^29 ≤ 48300531425249^29*400000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      226123981 400000000 48300531425249 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1816393739/5000000000 : ℝ), (-822883009/2500000000 : ℝ), (-226123981/400000000 : ℝ)] ![(686857895547/2500000000000 : ℝ), (12112576370783/50000000000000 : ℝ), (48300531425249/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1816393739/5000000000 : ℝ)|^37 ≤ (686857895547/2500000000000 : ℝ)^29
        have hw : |(1816393739/5000000000 : ℝ)|=(1816393739/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-822883009/2500000000 : ℝ)|^37 ≤ (12112576370783/50000000000000 : ℝ)^29
        have hw : |(-822883009/2500000000 : ℝ)|=(822883009/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-226123981/400000000 : ℝ)|^37 ≤ (48300531425249/100000000000000 : ℝ)^29
        have hw : |(-226123981/400000000 : ℝ)|=(226123981/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c313085_s0_27 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (1951895521/2500000000 : ℝ)*x 0 + (-249008963/2000000000 : ℝ)*x 1 + (710019947/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1951895521/2500000000 : ℝ)^37 ≤ (14584647937051/20000000000000 : ℝ)^29 := by
    have hnat : (1951895521 : ℕ)^37*20000000000000^29 ≤ 14584647937051^29*2500000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1951895521 2500000000 14584647937051 20000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (249008963/2000000000 : ℝ)^37 ≤ (1401557234059/20000000000000 : ℝ)^29 := by
    have hnat : (249008963 : ℕ)^37*20000000000000^29 ≤ 1401557234059^29*2000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      249008963 2000000000 1401557234059 20000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (710019947/2500000000 : ℝ)^37 ≤ (2006897413003/10000000000000 : ℝ)^29 := by
    have hnat : (710019947 : ℕ)^37*10000000000000^29 ≤ 2006897413003^29*2500000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      710019947 2500000000 2006897413003 10000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1951895521/2500000000 : ℝ), (-249008963/2000000000 : ℝ), (710019947/2500000000 : ℝ)] ![(14584647937051/20000000000000 : ℝ), (1401557234059/20000000000000 : ℝ), (2006897413003/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1951895521/2500000000 : ℝ)|^37 ≤ (14584647937051/20000000000000 : ℝ)^29
        have hw : |(1951895521/2500000000 : ℝ)|=(1951895521/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-249008963/2000000000 : ℝ)|^37 ≤ (1401557234059/20000000000000 : ℝ)^29
        have hw : |(-249008963/2000000000 : ℝ)|=(249008963/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(710019947/2500000000 : ℝ)|^37 ≤ (2006897413003/10000000000000 : ℝ)^29
        have hw : |(710019947/2500000000 : ℝ)|=(710019947/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c313085_s1_0 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-322979401/1000000000 : ℝ)*x 0 + (-2719722119/5000000000 : ℝ)*x 1 + (3929537027/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (322979401/1000000000 : ℝ)^37 ≤ (23646930579531/100000000000000 : ℝ)^29 := by
    have hnat : (322979401 : ℕ)^37*100000000000000^29 ≤ 23646930579531^29*1000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      322979401 1000000000 23646930579531 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2719722119/5000000000 : ℝ)^37 ≤ (45983714941291/100000000000000 : ℝ)^29 := by
    have hnat : (2719722119 : ℕ)^37*100000000000000^29 ≤ 45983714941291^29*5000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2719722119 5000000000 45983714941291 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3929537027/10000000000 : ℝ)^37 ≤ (6073870893719/20000000000000 : ℝ)^29 := by
    have hnat : (3929537027 : ℕ)^37*20000000000000^29 ≤ 6073870893719^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3929537027 10000000000 6073870893719 20000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-322979401/1000000000 : ℝ), (-2719722119/5000000000 : ℝ), (3929537027/10000000000 : ℝ)] ![(23646930579531/100000000000000 : ℝ), (45983714941291/100000000000000 : ℝ), (6073870893719/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-322979401/1000000000 : ℝ)|^37 ≤ (23646930579531/100000000000000 : ℝ)^29
        have hw : |(-322979401/1000000000 : ℝ)|=(322979401/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2719722119/5000000000 : ℝ)|^37 ≤ (45983714941291/100000000000000 : ℝ)^29
        have hw : |(-2719722119/5000000000 : ℝ)|=(2719722119/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3929537027/10000000000 : ℝ)|^37 ≤ (6073870893719/20000000000000 : ℝ)^29
        have hw : |(3929537027/10000000000 : ℝ)|=(3929537027/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c313085_s1_1 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (2608052639/5000000000 : ℝ)*x 0 + (3313312191/10000000000 : ℝ)*x 1 + (4092118223/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2608052639/5000000000 : ℝ)^37 ≤ (43588600679461/100000000000000 : ℝ)^29 := by
    have hnat : (2608052639 : ℕ)^37*100000000000000^29 ≤ 43588600679461^29*5000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2608052639 5000000000 43588600679461 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3313312191/10000000000 : ℝ)^37 ≤ (2442985785727/10000000000000 : ℝ)^29 := by
    have hnat : (3313312191 : ℕ)^37*10000000000000^29 ≤ 2442985785727^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3313312191 10000000000 2442985785727 10000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4092118223/10000000000 : ℝ)^37 ≤ (15990770724591/50000000000000 : ℝ)^29 := by
    have hnat : (4092118223 : ℕ)^37*50000000000000^29 ≤ 15990770724591^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4092118223 10000000000 15990770724591 50000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2608052639/5000000000 : ℝ), (3313312191/10000000000 : ℝ), (4092118223/10000000000 : ℝ)] ![(43588600679461/100000000000000 : ℝ), (2442985785727/10000000000000 : ℝ), (15990770724591/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2608052639/5000000000 : ℝ)|^37 ≤ (43588600679461/100000000000000 : ℝ)^29
        have hw : |(2608052639/5000000000 : ℝ)|=(2608052639/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3313312191/10000000000 : ℝ)|^37 ≤ (2442985785727/10000000000000 : ℝ)^29
        have hw : |(3313312191/10000000000 : ℝ)|=(3313312191/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4092118223/10000000000 : ℝ)|^37 ≤ (15990770724591/50000000000000 : ℝ)^29
        have hw : |(4092118223/10000000000 : ℝ)|=(4092118223/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c313085_s1_2 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (198143821/500000000 : ℝ)*x 0 + (-775882557/2000000000 : ℝ)*x 1 + (-4821443589/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (198143821/500000000 : ℝ)^37 ≤ (7674620173611/25000000000000 : ℝ)^29 := by
    have hnat : (198143821 : ℕ)^37*25000000000000^29 ≤ 7674620173611^29*500000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      198143821 500000000 7674620173611 25000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (775882557/2000000000 : ℝ)^37 ≤ (29875977840847/100000000000000 : ℝ)^29 := by
    have hnat : (775882557 : ℕ)^37*100000000000000^29 ≤ 29875977840847^29*2000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      775882557 2000000000 29875977840847 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4821443589/10000000000 : ℝ)^37 ≤ (19712770723659/50000000000000 : ℝ)^29 := by
    have hnat : (4821443589 : ℕ)^37*50000000000000^29 ≤ 19712770723659^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4821443589 10000000000 19712770723659 50000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(198143821/500000000 : ℝ), (-775882557/2000000000 : ℝ), (-4821443589/10000000000 : ℝ)] ![(7674620173611/25000000000000 : ℝ), (29875977840847/100000000000000 : ℝ), (19712770723659/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(198143821/500000000 : ℝ)|^37 ≤ (7674620173611/25000000000000 : ℝ)^29
        have hw : |(198143821/500000000 : ℝ)|=(198143821/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-775882557/2000000000 : ℝ)|^37 ≤ (29875977840847/100000000000000 : ℝ)^29
        have hw : |(-775882557/2000000000 : ℝ)|=(775882557/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-4821443589/10000000000 : ℝ)|^37 ≤ (19712770723659/50000000000000 : ℝ)^29
        have hw : |(-4821443589/10000000000 : ℝ)|=(4821443589/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c313085_s1_6 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (189464513/400000000 : ℝ)*x 0 + (-4211635191/10000000000 : ℝ)*x 1 + (743189741/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (189464513/400000000 : ℝ)^37 ≤ (3854266908361/10000000000000 : ℝ)^29 := by
    have hnat : (189464513 : ℕ)^37*10000000000000^29 ≤ 3854266908361^29*400000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      189464513 400000000 3854266908361 10000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4211635191/10000000000 : ℝ)^37 ≤ (16589028601889/50000000000000 : ℝ)^29 := by
    have hnat : (4211635191 : ℕ)^37*50000000000000^29 ≤ 16589028601889^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4211635191 10000000000 16589028601889 50000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (743189741/2000000000 : ℝ)^37 ≤ (14139636847213/50000000000000 : ℝ)^29 := by
    have hnat : (743189741 : ℕ)^37*50000000000000^29 ≤ 14139636847213^29*2000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      743189741 2000000000 14139636847213 50000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(189464513/400000000 : ℝ), (-4211635191/10000000000 : ℝ), (743189741/2000000000 : ℝ)] ![(3854266908361/10000000000000 : ℝ), (16589028601889/50000000000000 : ℝ), (14139636847213/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(189464513/400000000 : ℝ)|^37 ≤ (3854266908361/10000000000000 : ℝ)^29
        have hw : |(189464513/400000000 : ℝ)|=(189464513/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-4211635191/10000000000 : ℝ)|^37 ≤ (16589028601889/50000000000000 : ℝ)^29
        have hw : |(-4211635191/10000000000 : ℝ)|=(4211635191/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(743189741/2000000000 : ℝ)|^37 ≤ (14139636847213/50000000000000 : ℝ)^29
        have hw : |(743189741/2000000000 : ℝ)|=(743189741/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c313085 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (169487/100000 : ℝ) (176973/100000 : ℝ) (78599/100000 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![true, false, false], ![true, false, true]]) : False := by
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
  have main1 : (78599/100000 : ℝ)*P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (78599/100000 : ℝ)*P 1 ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((-1 : ℝ)*(X 0 2+X 2 2)) ∧ ((-1 : ℝ)*(X 0 2+X 2 2)) ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((-1 : ℝ)*pair X 1 2) ∧ ((-1 : ℝ)*pair X 1 2) ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (78599/100000 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (78599/100000 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((-1 : ℝ)*(X 0 1+X 1 1)) ∧ ((-1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((-1 : ℝ)*pair X 2 1) ∧ ((-1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base3 : ((1 : ℝ)*N 1+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 1]
  have base21 : ((1 : ℝ)*X 2 0+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 0).2]
  have base22 : ((-1 : ℝ)*X 2 1+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 1).1]
  have base33 : ((-1 : ℝ)*N 1+(-1 : ℝ)*N 2+(1 : ℝ)*P 0) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 0,f.sum]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base43 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 2+(1 : ℝ)*P 1) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 1,f.sum]
  have base49 : ((-1 : ℝ)*X 0 0+(-1 : ℝ)*X 2 0) ≤ (0 : ℝ) := by
    linarith only [order1.1]
  have base50 : ((1 : ℝ)*X 0 0+(1 : ℝ)*X 0 2+(1 : ℝ)*X 2 0+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
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
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![true, false, false], ![true, false, true]] hX 0 (by
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
  have major_s0_1 : P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1))+(820351075331079/5000000000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2))+(1081858256112193/10000000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0)) := by
    have hh := chart_majorant (a := (73/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (820351075331079/5000000000000000 : ℝ)) (beta := (1081858256112193/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow1,s0_corner1a]) (by linarith only [s0_pow1,s0_corner1b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![true, false, false], ![true, false, true]] hX 1 (by
        change ((-1 : ℝ)*pair X 1 2) ≤ (1 : ℝ)*((-1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order1.2.2])
    change lpNorm p (pair X 1) ≤ ((-1 : ℝ)*pair X 1 1)+(820351075331079/5000000000000000 : ℝ)*((-1 : ℝ)*pair X 1 2)+(1081858256112193/10000000000000000 : ℝ)*((1 : ℝ)*pair X 1 0) at hh
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
  have major_s0_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(820351075331079/5000000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(1081858256112193/10000000000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (73/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (820351075331079/5000000000000000 : ℝ)) (beta := (1081858256112193/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow2,s0_corner2a]) (by linarith only [s0_pow2,s0_corner2b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![true, false, false], ![true, false, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (1 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order2.2.2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(820351075331079/5000000000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(1081858256112193/10000000000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s0_1 : ((5579033109/10000000000 : ℝ)*X 1 0+(1366793171/5000000000 : ℝ)*X 1 1+(2116429981/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c313085_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_2 : ((3896446319/10000000000 : ℝ)*X 2 0+(-1610555841/5000000000 : ℝ)*X 2 1+(-2738570743/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c313085_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_6 : ((6750577451/10000000000 : ℝ)*X 0 0+(-539389867/2500000000 : ℝ)*X 0 1+(53204513/156250000 : ℝ)*X 0 2+(6750577451/10000000000 : ℝ)*X 1 0+(-539389867/2500000000 : ℝ)*X 1 1+(53204513/156250000 : ℝ)*X 1 2+(6750577451/10000000000 : ℝ)*X 2 0+(-539389867/2500000000 : ℝ)*X 2 1+(53204513/156250000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c313085_s0_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_7 : ((-847758273/5000000000 : ℝ)*X 0 0+(-122033149/156250000 : ℝ)*X 0 1+(2453865293/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c313085_s0_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_8 : ((5665525443/10000000000 : ℝ)*X 1 0+(2534483939/10000000000 : ℝ)*X 1 1+(4313782919/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c313085_s0_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_9 : ((4076638037/10000000000 : ℝ)*X 2 0+(-1408905799/5000000000 : ℝ)*X 2 1+(-5653445943/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c313085_s0_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_13 : ((7486161521/10000000000 : ℝ)*X 0 0+(-285205179/2000000000 : ℝ)*X 0 1+(1556011379/5000000000 : ℝ)*X 0 2+(7486161521/10000000000 : ℝ)*X 1 0+(-285205179/2000000000 : ℝ)*X 1 1+(1556011379/5000000000 : ℝ)*X 1 2+(7486161521/10000000000 : ℝ)*X 2 0+(-285205179/2000000000 : ℝ)*X 2 1+(1556011379/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c313085_s0_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_14 : ((-1990672751/10000000000 : ℝ)*X 0 0+(-7236076783/10000000000 : ℝ)*X 0 1+(2949856881/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c313085_s0_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_15 : ((2505463029/5000000000 : ℝ)*X 1 0+(2981293173/10000000000 : ℝ)*X 1 1+(4610309959/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c313085_s0_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_16 : ((1968986847/5000000000 : ℝ)*X 2 0+(-799405309/2500000000 : ℝ)*X 2 1+(-545954419/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c313085_s0_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_20 : ((488640129/625000000 : ℝ)*X 0 0+(-134951617/1000000000 : ℝ)*X 0 1+(685337761/2500000000 : ℝ)*X 0 2+(488640129/625000000 : ℝ)*X 1 0+(-134951617/1000000000 : ℝ)*X 1 1+(685337761/2500000000 : ℝ)*X 1 2+(488640129/625000000 : ℝ)*X 2 0+(-134951617/1000000000 : ℝ)*X 2 1+(685337761/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c313085_s0_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_21 : ((-340474421/2000000000 : ℝ)*X 0 0+(-301499143/400000000 : ℝ)*X 0 1+(2814032233/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c313085_s0_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_22 : ((5888818401/10000000000 : ℝ)*X 1 0+(163474157/625000000 : ℝ)*X 1 1+(3998169917/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c313085_s0_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_23 : ((1816393739/5000000000 : ℝ)*X 2 0+(-822883009/2500000000 : ℝ)*X 2 1+(-226123981/400000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c313085_s0_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_27 : ((1951895521/2500000000 : ℝ)*X 0 0+(-249008963/2000000000 : ℝ)*X 0 1+(710019947/2500000000 : ℝ)*X 0 2+(1951895521/2500000000 : ℝ)*X 1 0+(-249008963/2000000000 : ℝ)*X 1 1+(710019947/2500000000 : ℝ)*X 1 2+(1951895521/2500000000 : ℝ)*X 2 0+(-249008963/2000000000 : ℝ)*X 2 1+(710019947/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c313085_s0_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s0_0 : (0 : ℝ) ≤ ((2447/20000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(2447/20000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (10535969299128132264741/2500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (3000493390233/1000000000000 : ℝ)*(base3) + (87090348643/62500000000 : ℝ)*(base40) + (164517794489/62500000000 : ℝ)*(base50) + (5544860325079/1000000000000 : ℝ)*(major_s0_0) + (5544860325079/1000000000000 : ℝ)*(major_s0_1) + (5544860325079/1000000000000 : ℝ)*(major_s0_2) + (18053367/1000000000000 : ℝ)*(sp_s0_6) + (7818123143927/1000000000000 : ℝ)*(sp_s0_7) + (10818642126017/1000000000000 : ℝ)*(sp_s0_8) + (781813230061/100000000000 : ℝ)*(sp_s0_9) + (135521749357/500000000000 : ℝ)*(sp_s0_13) + (1945907/125000000000 : ℝ)*(sp_s0_15) + (41159113/1000000000000 : ℝ)*(sp_s0_21) + (3200243/100000000000 : ℝ)*(sp_s0_23) + (3271554942313/1000000000000 : ℝ)*(f.failure) + (24431763447/3125000000 : ℝ)*(f.sum) + (8496592844751271/10000000000000000000000000000 : ℝ)*base62 + (1502626957411753/10000000000000000000000000000 : ℝ)*base65 + (2911994239830241/5000000000000000000000000000 : ℝ)*base66 + (1712237953169759/5000000000000000000000000000 : ℝ)*base68 + (52193968614447/2000000000000000000000000000 : ℝ)*base71 + (39879992588247/10000000000000000000000000000 : ℝ)*base73 + (8503968945411753/10000000000000000000000000000 : ℝ)*base74 + (146753485169759/5000000000000000000000000000 : ℝ)*base76 + (860797176814447/2000000000000000000000000000 : ℝ)*base78 + (96569/100000000000000000 : ℝ)*base86 + (96569/100000000000000000 : ℝ)*base88 + (96569/100000000000000000 : ℝ)*base90 + (1/1000000000000 : ℝ)*base93 + hcertificate_margin
  have ratio_s0_1 : (0 : ℝ) ≤ ((-1671/20000 : ℝ)*X 0 1+(1 : ℝ)*X 0 2+(-1671/20000 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (89042584704651212978241/5000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (83588988363/1000000000000 : ℝ)*(base3) + (919416478723/500000000000 : ℝ)*(base40) + (638771545993/1000000000000 : ℝ)*(base50) + (10207578231/500000000000 : ℝ)*(base59) + (6256692381579/1000000000000 : ℝ)*(major_s0_0) + (6256692381579/1000000000000 : ℝ)*(major_s0_1) + (6256692381579/1000000000000 : ℝ)*(major_s0_2) + (807549/2000000000 : ℝ)*(sp_s0_2) + (45477859/125000000000 : ℝ)*(sp_s0_9) + (4410915878771/500000000000 : ℝ)*(sp_s0_14) + (1781084149181/200000000000 : ℝ)*(sp_s0_15) + (8821064160169/1000000000000 : ℝ)*(sp_s0_16) + (1803883100387/500000000000 : ℝ)*(sp_s0_20) + (191880301/1000000000000 : ℝ)*(sp_s0_27) + (1845773534719/500000000000 : ℝ)*(f.failure) + (4410915878771/500000000000 : ℝ)*(f.sum) + (112983335919771/10000000000000000000000000000 : ℝ)*base62 + (4090997690507253/10000000000000000000000000000 : ℝ)*base65 + (1050459798793741/5000000000000000000000000000 : ℝ)*base66 + (36484229206259/5000000000000000000000000000 : ℝ)*base68 + (280010518218947/2000000000000000000000000000 : ℝ)*base71 + (166622451492747/10000000000000000000000000000 : ℝ)*base73 + (1702827720492747/10000000000000000000000000000 : ℝ)*base75 + (936229456706259/5000000000000000000000000000 : ℝ)*base76 + (899347019818947/2000000000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base84 + (30847/50000000000000000 : ℝ)*base86 + (30847/50000000000000000 : ℝ)*base88 + (30847/50000000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s0_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(7283/25000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(7283/25000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (4854844242044346329703/1250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (672988596239/250000000000 : ℝ)*(base3) + (3900733888389/1000000000000 : ℝ)*(base40) + (3718732361947/1000000000000 : ℝ)*(base50) + (86233/200000000000 : ℝ)*(base59) + (11950203271607/1000000000000 : ℝ)*(major_s0_0) + (11950203271607/1000000000000 : ℝ)*(major_s0_1) + (11950203271607/1000000000000 : ℝ)*(major_s0_2) + (967107/200000000000 : ℝ)*(sp_s0_1) + (73101199/1000000000000 : ℝ)*(sp_s0_2) + (42891159/250000000000 : ℝ)*(sp_s0_20) + (16849597061757/1000000000000 : ℝ)*(sp_s0_21) + (9770773305589/500000000000 : ℝ)*(sp_s0_22) + (8424761980279/500000000000 : ℝ)*(sp_s0_23) + (2179341118617/500000000000 : ℝ)*(sp_s0_27) + (7050808186827/1000000000000 : ℝ)*(f.failure) + (16849597061757/1000000000000 : ℝ)*(f.sum) + (6526970139152057/10000000000000000000000000000 : ℝ)*base63 + (640669061595849/10000000000000000000000000000 : ℝ)*base65 + (616163636126047/5000000000000000000000000000 : ℝ)*base67 + (205986958873953/5000000000000000000000000000 : ℝ)*base69 + (1810925669731249/2000000000000000000000000000 : ℝ)*base70 + (2384104771404151/10000000000000000000000000000 : ℝ)*base73 + (2059999478404151/10000000000000000000000000000 : ℝ)*base75 + (420049196626047/5000000000000000000000000000 : ℝ)*base76 + (2152442072131249/2000000000000000000000000000 : ℝ)*base79 + (47749/100000000000000000 : ℝ)*base87 + (47749/100000000000000000 : ℝ)*base89 + (47749/100000000000000000 : ℝ)*base91 + (1/1000000000000 : ℝ)*base92 + hcertificate_margin
  have s1_pow0 : (2447/20000 : ℝ) ^ (73/16 : ℝ) ≤ (6873740460213887/100000000000000000000 : ℝ) := by
    have hpowers : (2447/20000 : ℝ)^73 ≤ (6873740460213887/100000000000000000000 : ℝ)^16 := by
      have hnat : (2447 : ℕ)^73*100000000000000000000^16 ≤ 6873740460213887^16*20000^73 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2447 20000 6873740460213887 100000000000000000000 73 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2447/20000 : ℝ)) (X := (6873740460213887/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 73 16 (by norm_num) hpowers
    exact h
  have s1_corner0a : (100006873740460213887/100000000000000000000 : ℝ) ≤ (5000075326641153/5000000000000000 : ℝ) ^ (73/16 : ℝ) := by
    have hpowers : (100006873740460213887/100000000000000000000 : ℝ)^16 ≤ (5000075326641153/5000000000000000 : ℝ)^73 := by
      have hnat : (100006873740460213887 : ℕ)^16*5000000000000000^73 ≤ 5000075326641153^73*100000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100006873740460213887 100000000000000000000 5000075326641153 5000000000000000 16 73 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000075326641153/5000000000000000 : ℝ)) (X := (100006873740460213887/100000000000000000000 : ℝ)) (by norm_num) 73 16 (by norm_num) hpowers
    exact h
  have s1_corner0b : (50006873740460213887/50000000000000000000 : ℝ) ≤ (1000030129847957/1000000000000000 : ℝ) ^ (73/16 : ℝ) := by
    have hpowers : (50006873740460213887/50000000000000000000 : ℝ)^16 ≤ (1000030129847957/1000000000000000 : ℝ)^73 := by
      have hnat : (50006873740460213887 : ℕ)^16*1000000000000000^73 ≤ 1000030129847957^73*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50006873740460213887 50000000000000000000 1000030129847957 1000000000000000 16 73 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000030129847957/1000000000000000 : ℝ)) (X := (50006873740460213887/50000000000000000000 : ℝ)) (by norm_num) 73 16 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(75326641153/611750000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(9415324829/76468750000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (73/16 : ℝ)) (rho := (2447/20000 : ℝ)) (alpha := (75326641153/611750000000000 : ℝ)) (beta := (9415324829/76468750000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![true, false, false], ![true, false, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (2447/20000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(75326641153/611750000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(9415324829/76468750000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (1671/20000 : ℝ) ^ (73/16 : ℝ) ≤ (241218544756349/20000000000000000000 : ℝ) := by
    have hpowers : (1671/20000 : ℝ)^73 ≤ (241218544756349/20000000000000000000 : ℝ)^16 := by
      have hnat : (1671 : ℕ)^73*20000000000000000000^16 ≤ 241218544756349^16*20000^73 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1671 20000 241218544756349 20000000000000000000 73 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1671/20000 : ℝ)) (X := (241218544756349/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 73 16 (by norm_num) hpowers
    exact h
  have s1_corner1a : (20000241218544756349/20000000000000000000 : ℝ) ≤ (10000026434784541/10000000000000000 : ℝ) ^ (73/16 : ℝ) := by
    have hpowers : (20000241218544756349/20000000000000000000 : ℝ)^16 ≤ (10000026434784541/10000000000000000 : ℝ)^73 := by
      have hnat : (20000241218544756349 : ℕ)^16*10000000000000000^73 ≤ 10000026434784541^73*20000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20000241218544756349 20000000000000000000 10000026434784541 10000000000000000 16 73 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000026434784541/10000000000000000 : ℝ)) (X := (20000241218544756349/20000000000000000000 : ℝ)) (by norm_num) 73 16 (by norm_num) hpowers
    exact h
  have s1_corner1b : (10000241218544756349/10000000000000000000 : ℝ) ≤ (5000026434660069/5000000000000000 : ℝ) ^ (73/16 : ℝ) := by
    have hpowers : (10000241218544756349/10000000000000000000 : ℝ)^16 ≤ (5000026434660069/5000000000000000 : ℝ)^73 := by
      have hnat : (10000241218544756349 : ℕ)^16*5000000000000000^73 ≤ 5000026434660069^73*10000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10000241218544756349 10000000000000000000 5000026434660069 5000000000000000 16 73 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000026434660069/5000000000000000 : ℝ)) (X := (10000241218544756349/10000000000000000000 : ℝ)) (by norm_num) 73 16 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1))+(8811594847/278500000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2))+(26434535597/835500000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0)) := by
    have hh := chart_majorant (a := (73/16 : ℝ)) (rho := (1671/20000 : ℝ)) (alpha := (8811594847/278500000000000 : ℝ)) (beta := (26434535597/835500000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![true, false, false], ![true, false, true]] hX 1 (by
        change ((-1 : ℝ)*pair X 1 2) ≤ (1671/20000 : ℝ)*((-1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((-1 : ℝ)*pair X 1 1)+(8811594847/278500000000000 : ℝ)*((-1 : ℝ)*pair X 1 2)+(26434535597/835500000000000 : ℝ)*((1 : ℝ)*pair X 1 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (7283/25000 : ℝ) ^ (73/16 : ℝ) ≤ (359906342056155493/100000000000000000000 : ℝ) := by
    have hpowers : (7283/25000 : ℝ)^73 ≤ (359906342056155493/100000000000000000000 : ℝ)^16 := by
      have hnat : (7283 : ℕ)^73*100000000000000000000^16 ≤ 359906342056155493^16*25000^73 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7283 25000 359906342056155493 100000000000000000000 73 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7283/25000 : ℝ)) (X := (359906342056155493/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 73 16 (by norm_num) hpowers
    exact h
  have s1_corner2a : (100359906342056155493/100000000000000000000 : ℝ) ≤ (2001575459552459/2000000000000000 : ℝ) ^ (73/16 : ℝ) := by
    have hpowers : (100359906342056155493/100000000000000000000 : ℝ)^16 ≤ (2001575459552459/2000000000000000 : ℝ)^73 := by
      have hnat : (100359906342056155493 : ℕ)^16*2000000000000000^73 ≤ 2001575459552459^73*100000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100359906342056155493 100000000000000000000 2001575459552459 2000000000000000 16 73 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2001575459552459/2000000000000000 : ℝ)) (X := (100359906342056155493/100000000000000000000 : ℝ)) (by norm_num) 73 16 (by norm_num) hpowers
    exact h
  have s1_corner2b : (50359906342056155493/50000000000000000000 : ℝ) ≤ (2503933142174921/2500000000000000 : ℝ) ^ (73/16 : ℝ) := by
    have hpowers : (50359906342056155493/50000000000000000000 : ℝ)^16 ≤ (2503933142174921/2500000000000000 : ℝ)^73 := by
      have hnat : (50359906342056155493 : ℕ)^16*2500000000000000^73 ≤ 2503933142174921^73*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50359906342056155493 50000000000000000000 2503933142174921 2500000000000000 16 73 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2503933142174921/2500000000000000 : ℝ)) (X := (50359906342056155493/50000000000000000000 : ℝ)) (by norm_num) 73 16 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(1575459552459/582640000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(7855270937389/2913200000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (73/16 : ℝ)) (rho := (7283/25000 : ℝ)) (alpha := (1575459552459/582640000000000 : ℝ)) (beta := (7855270937389/2913200000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![true, false, false], ![true, false, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (7283/25000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(1575459552459/582640000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(7855270937389/2913200000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-322979401/1000000000 : ℝ)*X 0 0+(-2719722119/5000000000 : ℝ)*X 0 1+(3929537027/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c313085_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_1 : ((2608052639/5000000000 : ℝ)*X 1 0+(3313312191/10000000000 : ℝ)*X 1 1+(4092118223/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c313085_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((198143821/500000000 : ℝ)*X 2 0+(-775882557/2000000000 : ℝ)*X 2 1+(-4821443589/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c313085_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_6 : ((189464513/400000000 : ℝ)*X 0 0+(-4211635191/10000000000 : ℝ)*X 0 1+(743189741/2000000000 : ℝ)*X 0 2+(189464513/400000000 : ℝ)*X 1 0+(-4211635191/10000000000 : ℝ)*X 1 1+(743189741/2000000000 : ℝ)*X 1 2+(189464513/400000000 : ℝ)*X 2 0+(-4211635191/10000000000 : ℝ)*X 2 1+(743189741/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c313085_s1_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have hsep : (-358461/50000 : ℝ) < ((-169487/100000 : ℝ)*P 0+(-169487/100000 : ℝ)*P 1+(-169487/100000 : ℝ)*P 2+(1 : ℝ)*T) := by
    have hcertificate_margin : (-358461/50000 : ℝ) < (-17495688735071337795209032182809837/2481644014250000000000000000000000 : ℝ) := by norm_num
    linear_combination (11913/500000000000 : ℝ)*(base21) + (27623/500000000000 : ℝ)*(base22) + (33197/1000000000000 : ℝ)*(base33) + (361830633511/1000000000000 : ℝ)*(base40) + (12223/1000000000000 : ℝ)*(base43) + (54896988413/500000000000 : ℝ)*(base49) + (399775112643/1000000000000 : ℝ)*(base50) + (3917/1000000000000 : ℝ)*(base60) + (1694869966803/1000000000000 : ℝ)*(major_s1_0) + (1694869987777/1000000000000 : ℝ)*(major_s1_1) + (169487/100000 : ℝ)*(major_s1_2) + (1175006604733/500000000000 : ℝ)*(sp_s1_0) + (587503297123/250000000000 : ℝ)*(sp_s1_1) + (2350013097197/1000000000000 : ℝ)*(sp_s1_2) + (1 : ℝ)*(sp_s1_6) + (2350013221689/1000000000000 : ℝ)*(f.sum) + (2937941628730348927/6084946500000000000000000000000 : ℝ)*base63 + (1333977952741/18207500000000000000000000 : ℝ)*base65 + (103123186156181/278500000000000000000000000 : ℝ)*base67 + (6732516702299/9103750000000000000000000 : ℝ)*base69 + (3931310192844375797/4455375250000000000000000000000 : ℝ)*base71 + (68079295040701/152937500000000000000000000 : ℝ)*base72 + (616710630870869/835500000000000000000000000 : ℝ)*base75 + (202667271063367/305875000000000000000000000 : ℝ)*base77 + (2598573602236299/681489500000000000000000000000 : ℝ)*base78 + hcertificate_margin
  linarith only [hsep,f.failure]

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
namespace HlawkaSchatten.DiagonalCutoff4
theorem coarse_distinct_p013_b034 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ))
    (c : Fin 88) (hlo : 85 ≤ c.val) (hhi : c.val < 88)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (169487/100000 : ℝ) (176973/100000 : ℝ) (78599/100000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  have hc : c=85 ∨ c=86 ∨ c=87 := by omega
  rcases hc with rfl|rfl|rfl
  · exact collision_c313085 p hpa (by linarith only [hpb]) X hX
  · exact collision_c313086 p hpa (by linarith only [hpb]) X hX
  · exact (hn87 rfl).elim

end HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ))
    (c : Fin 88) (hlo : 85 ≤ c.val) (hhi : c.val < 88)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (169487/100000 : ℝ) (176973/100000 : ℝ) (78599/100000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  exact HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p013_b034 p hpa hpb c hlo hhi hn63 hn87 X hX

#print axioms solution
