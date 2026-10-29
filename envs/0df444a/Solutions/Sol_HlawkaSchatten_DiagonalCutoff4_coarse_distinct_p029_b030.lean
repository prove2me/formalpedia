-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p029_b030
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T02:27:24.249228+00:00
-- url     : https://prove2.me/submissions/798d2309-a308-4907-96e2-911564d0372f

import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c329061_s0
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c329061_s1
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c329061_s2
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
theorem HlawkaSchatten.DiagonalCutoff4.collision_c329061 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (55589/25000 : ℝ) (160257/100000 : ℝ) (10347/12500 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, true]]) : False := by
  have h0 := collision_c329061_s0 p hpa hpb X hX
  have h1 := collision_c329061_s1 p hpa hpb X hX h0
  exact collision_c329061_s2 p hpa hpb X hX h1

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
theorem collision_support_c329060_s0_0 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-1223416953/10000000000 : ℝ)*x 0 + (447949197/1000000000 : ℝ)*x 1 + (-5984515867/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1223416953/10000000000 : ℝ)^95 ≤ (319771273447/4000000000000 : ℝ)^79 := by
    have hnat : (1223416953 : ℕ)^95*4000000000000^79 ≤ 319771273447^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1223416953 10000000000 319771273447 4000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (447949197/1000000000 : ℝ)^95 ≤ (380707602701/1000000000000 : ℝ)^79 := by
    have hnat : (447949197 : ℕ)^95*1000000000000^79 ≤ 380707602701^79*1000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      447949197 1000000000 380707602701 1000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5984515867/10000000000 : ℝ)^95 ≤ (26967478936201/50000000000000 : ℝ)^79 := by
    have hnat : (5984515867 : ℕ)^95*50000000000000^79 ≤ 26967478936201^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5984515867 10000000000 26967478936201 50000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (95/16 : ℝ)) 95 79 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1223416953/10000000000 : ℝ), (447949197/1000000000 : ℝ), (-5984515867/10000000000 : ℝ)] ![(319771273447/4000000000000 : ℝ), (380707602701/1000000000000 : ℝ), (26967478936201/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1223416953/10000000000 : ℝ)|^95 ≤ (319771273447/4000000000000 : ℝ)^79
        have hw : |(-1223416953/10000000000 : ℝ)|=(1223416953/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(447949197/1000000000 : ℝ)|^95 ≤ (380707602701/1000000000000 : ℝ)^79
        have hw : |(447949197/1000000000 : ℝ)|=(447949197/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-5984515867/10000000000 : ℝ)|^95 ≤ (26967478936201/50000000000000 : ℝ)^79
        have hw : |(-5984515867/10000000000 : ℝ)|=(5984515867/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c329060_s0_1 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4479491579/10000000000 : ℝ)*x 0 + (-611708617/5000000000 : ℝ)*x 1 + (-5984516033/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4479491579/10000000000 : ℝ)^95 ≤ (19035378137001/50000000000000 : ℝ)^79 := by
    have hnat : (4479491579 : ℕ)^95*50000000000000^79 ≤ 19035378137001^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4479491579 10000000000 19035378137001 50000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (611708617/5000000000 : ℝ)^95 ≤ (399714202211/5000000000000 : ℝ)^79 := by
    have hnat : (611708617 : ℕ)^95*5000000000000^79 ≤ 399714202211^79*5000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      611708617 5000000000 399714202211 5000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5984516033/10000000000 : ℝ)^95 ≤ (53934959671463/100000000000000 : ℝ)^79 := by
    have hnat : (5984516033 : ℕ)^95*100000000000000^79 ≤ 53934959671463^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5984516033 10000000000 53934959671463 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (95/16 : ℝ)) 95 79 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4479491579/10000000000 : ℝ), (-611708617/5000000000 : ℝ), (-5984516033/10000000000 : ℝ)] ![(19035378137001/50000000000000 : ℝ), (399714202211/5000000000000 : ℝ), (53934959671463/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4479491579/10000000000 : ℝ)|^95 ≤ (19035378137001/50000000000000 : ℝ)^79
        have hw : |(4479491579/10000000000 : ℝ)|=(4479491579/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-611708617/5000000000 : ℝ)|^95 ≤ (399714202211/5000000000000 : ℝ)^79
        have hw : |(-611708617/5000000000 : ℝ)|=(611708617/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-5984516033/10000000000 : ℝ)|^95 ≤ (53934959671463/100000000000000 : ℝ)^79
        have hw : |(-5984516033/10000000000 : ℝ)|=(5984516033/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c329060_s0_7 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-223928881/1250000000 : ℝ)*x 0 + (1437628991/10000000000 : ℝ)*x 1 + (-8102794037/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (223928881/1250000000 : ℝ)^95 ≤ (12645892439791/100000000000000 : ℝ)^79 := by
    have hnat : (223928881 : ℕ)^95*100000000000000^79 ≤ 12645892439791^79*1250000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      223928881 1250000000 12645892439791 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1437628991/10000000000 : ℝ)^95 ≤ (97060750893/1000000000000 : ℝ)^79 := by
    have hnat : (1437628991 : ℕ)^95*1000000000000^79 ≤ 97060750893^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1437628991 10000000000 97060750893 1000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (8102794037/10000000000 : ℝ)^95 ≤ (38824016225951/50000000000000 : ℝ)^79 := by
    have hnat : (8102794037 : ℕ)^95*50000000000000^79 ≤ 38824016225951^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8102794037 10000000000 38824016225951 50000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (95/16 : ℝ)) 95 79 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-223928881/1250000000 : ℝ), (1437628991/10000000000 : ℝ), (-8102794037/10000000000 : ℝ)] ![(12645892439791/100000000000000 : ℝ), (97060750893/1000000000000 : ℝ), (38824016225951/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-223928881/1250000000 : ℝ)|^95 ≤ (12645892439791/100000000000000 : ℝ)^79
        have hw : |(-223928881/1250000000 : ℝ)|=(223928881/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1437628991/10000000000 : ℝ)|^95 ≤ (97060750893/1000000000000 : ℝ)^79
        have hw : |(1437628991/10000000000 : ℝ)|=(1437628991/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-8102794037/10000000000 : ℝ)|^95 ≤ (38824016225951/50000000000000 : ℝ)^79
        have hw : |(-8102794037/10000000000 : ℝ)|=(8102794037/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c329060_s0_8 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1243918529/5000000000 : ℝ)*x 0 + (-627579159/10000000000 : ℝ)*x 1 + (-810279597/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1243918529/5000000000 : ℝ)^95 ≤ (18769675070579/100000000000000 : ℝ)^79 := by
    have hnat : (1243918529 : ℕ)^95*100000000000000^79 ≤ 18769675070579^79*5000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1243918529 5000000000 18769675070579 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (627579159/10000000000 : ℝ)^95 ≤ (89556754579/2500000000000 : ℝ)^79 := by
    have hnat : (627579159 : ℕ)^95*2500000000000^79 ≤ 89556754579^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      627579159 10000000000 89556754579 2500000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (810279597/1000000000 : ℝ)^95 ≤ (77648054727227/100000000000000 : ℝ)^79 := by
    have hnat : (810279597 : ℕ)^95*100000000000000^79 ≤ 77648054727227^79*1000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      810279597 1000000000 77648054727227 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (95/16 : ℝ)) 95 79 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1243918529/5000000000 : ℝ), (-627579159/10000000000 : ℝ), (-810279597/1000000000 : ℝ)] ![(18769675070579/100000000000000 : ℝ), (89556754579/2500000000000 : ℝ), (77648054727227/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1243918529/5000000000 : ℝ)|^95 ≤ (18769675070579/100000000000000 : ℝ)^79
        have hw : |(1243918529/5000000000 : ℝ)|=(1243918529/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-627579159/10000000000 : ℝ)|^95 ≤ (89556754579/2500000000000 : ℝ)^79
        have hw : |(-627579159/10000000000 : ℝ)|=(627579159/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-810279597/1000000000 : ℝ)|^95 ≤ (77648054727227/100000000000000 : ℝ)^79
        have hw : |(-810279597/1000000000 : ℝ)|=(810279597/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c329060_s0_9 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1102957599/5000000000 : ℝ)*x 0 + (790330931/1000000000 : ℝ)*x 1 + (1275186981/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1102957599/5000000000 : ℝ)^95 ≤ (1624219704621/10000000000000 : ℝ)^79 := by
    have hnat : (1102957599 : ℕ)^95*10000000000000^79 ≤ 1624219704621^79*5000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1102957599 5000000000 1624219704621 10000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (790330931/1000000000 : ℝ)^95 ≤ (37677499077549/50000000000000 : ℝ)^79 := by
    have hnat : (790330931 : ℕ)^95*50000000000000^79 ≤ 37677499077549^79*1000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      790330931 1000000000 37677499077549 50000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1275186981/10000000000 : ℝ)^95 ≤ (131293824813/1562500000000 : ℝ)^79 := by
    have hnat : (1275186981 : ℕ)^95*1562500000000^79 ≤ 131293824813^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1275186981 10000000000 131293824813 1562500000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (95/16 : ℝ)) 95 79 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1102957599/5000000000 : ℝ), (790330931/1000000000 : ℝ), (1275186981/10000000000 : ℝ)] ![(1624219704621/10000000000000 : ℝ), (37677499077549/50000000000000 : ℝ), (131293824813/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1102957599/5000000000 : ℝ)|^95 ≤ (1624219704621/10000000000000 : ℝ)^79
        have hw : |(1102957599/5000000000 : ℝ)|=(1102957599/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(790330931/1000000000 : ℝ)|^95 ≤ (37677499077549/50000000000000 : ℝ)^79
        have hw : |(790330931/1000000000 : ℝ)|=(790330931/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1275186981/10000000000 : ℝ)|^95 ≤ (131293824813/1562500000000 : ℝ)^79
        have hw : |(1275186981/10000000000 : ℝ)|=(1275186981/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c329060_s0_13 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ)) (x : Fin 3 → ℝ) :
    (168209117/400000000 : ℝ)*x 0 + (3481645679/5000000000 : ℝ)*x 1 + (-383647/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (168209117/400000000 : ℝ)^95 ≤ (4410674706291/12500000000000 : ℝ)^79 := by
    have hnat : (168209117 : ℕ)^95*12500000000000^79 ≤ 4410674706291^79*400000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      168209117 400000000 4410674706291 12500000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3481645679/5000000000 : ℝ)^95 ≤ (16177803335281/25000000000000 : ℝ)^79 := by
    have hnat : (3481645679 : ℕ)^95*25000000000000^79 ≤ 16177803335281^79*5000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3481645679 5000000000 16177803335281 25000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (383647/2000000000 : ℝ)^95 ≤ (847250447/25000000000000 : ℝ)^79 := by
    have hnat : (383647 : ℕ)^95*25000000000000^79 ≤ 847250447^79*2000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      383647 2000000000 847250447 25000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (95/16 : ℝ)) 95 79 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(168209117/400000000 : ℝ), (3481645679/5000000000 : ℝ), (-383647/2000000000 : ℝ)] ![(4410674706291/12500000000000 : ℝ), (16177803335281/25000000000000 : ℝ), (847250447/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(168209117/400000000 : ℝ)|^95 ≤ (4410674706291/12500000000000 : ℝ)^79
        have hw : |(168209117/400000000 : ℝ)|=(168209117/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3481645679/5000000000 : ℝ)|^95 ≤ (16177803335281/25000000000000 : ℝ)^79
        have hw : |(3481645679/5000000000 : ℝ)|=(3481645679/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-383647/2000000000 : ℝ)|^95 ≤ (847250447/25000000000000 : ℝ)^79
        have hw : |(-383647/2000000000 : ℝ)|=(383647/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c329060_s0_14 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-862151791/10000000000 : ℝ)*x 0 + (2136714497/10000000000 : ℝ)*x 1 + (-257198799/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (862151791/10000000000 : ℝ)^95 ≤ (2624072085341/50000000000000 : ℝ)^79 := by
    have hnat : (862151791 : ℕ)^95*50000000000000^79 ≤ 2624072085341^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      862151791 10000000000 2624072085341 50000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2136714497/10000000000 : ℝ)^95 ≤ (3126287738251/20000000000000 : ℝ)^79 := by
    have hnat : (2136714497 : ℕ)^95*20000000000000^79 ≤ 3126287738251^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2136714497 10000000000 3126287738251 20000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (257198799/312500000 : ℝ)^95 ≤ (15824083425299/20000000000000 : ℝ)^79 := by
    have hnat : (257198799 : ℕ)^95*20000000000000^79 ≤ 15824083425299^79*312500000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      257198799 312500000 15824083425299 20000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (95/16 : ℝ)) 95 79 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-862151791/10000000000 : ℝ), (2136714497/10000000000 : ℝ), (-257198799/312500000 : ℝ)] ![(2624072085341/50000000000000 : ℝ), (3126287738251/20000000000000 : ℝ), (15824083425299/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-862151791/10000000000 : ℝ)|^95 ≤ (2624072085341/50000000000000 : ℝ)^79
        have hw : |(-862151791/10000000000 : ℝ)|=(862151791/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2136714497/10000000000 : ℝ)|^95 ≤ (3126287738251/20000000000000 : ℝ)^79
        have hw : |(2136714497/10000000000 : ℝ)|=(2136714497/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-257198799/312500000 : ℝ)|^95 ≤ (15824083425299/20000000000000 : ℝ)^79
        have hw : |(-257198799/312500000 : ℝ)|=(257198799/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c329060_s0_15 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ)) (x : Fin 3 → ℝ) :
    (962160429/10000000000 : ℝ)*x 0 + (-513051991/2500000000 : ℝ)*x 1 + (-4115180617/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (962160429/10000000000 : ℝ)^95 ≤ (2994283638857/50000000000000 : ℝ)^79 := by
    have hnat : (962160429 : ℕ)^95*50000000000000^79 ≤ 2994283638857^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      962160429 10000000000 2994283638857 50000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (513051991/2500000000 : ℝ)^95 ≤ (7445509720909/50000000000000 : ℝ)^79 := by
    have hnat : (513051991 : ℕ)^95*50000000000000^79 ≤ 7445509720909^79*2500000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      513051991 2500000000 7445509720909 50000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4115180617/5000000000 : ℝ)^95 ≤ (79120413265381/100000000000000 : ℝ)^79 := by
    have hnat : (4115180617 : ℕ)^95*100000000000000^79 ≤ 79120413265381^79*5000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4115180617 5000000000 79120413265381 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (95/16 : ℝ)) 95 79 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(962160429/10000000000 : ℝ), (-513051991/2500000000 : ℝ), (-4115180617/5000000000 : ℝ)] ![(2994283638857/50000000000000 : ℝ), (7445509720909/50000000000000 : ℝ), (79120413265381/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(962160429/10000000000 : ℝ)|^95 ≤ (2994283638857/50000000000000 : ℝ)^79
        have hw : |(962160429/10000000000 : ℝ)|=(962160429/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-513051991/2500000000 : ℝ)|^95 ≤ (7445509720909/50000000000000 : ℝ)^79
        have hw : |(-513051991/2500000000 : ℝ)|=(513051991/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-4115180617/5000000000 : ℝ)|^95 ≤ (79120413265381/100000000000000 : ℝ)^79
        have hw : |(-4115180617/5000000000 : ℝ)|=(4115180617/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c329060_s0_16 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ)) (x : Fin 3 → ℝ) :
    (6590500467/10000000000 : ℝ)*x 0 + (226695421/625000000 : ℝ)*x 1 + (1460905391/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6590500467/10000000000 : ℝ)^95 ≤ (60568056698721/100000000000000 : ℝ)^79 := by
    have hnat : (6590500467 : ℕ)^95*100000000000000^79 ≤ 60568056698721^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6590500467 10000000000 60568056698721 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (226695421/625000000 : ℝ)^95 ≤ (29536582593127/100000000000000 : ℝ)^79 := by
    have hnat : (226695421 : ℕ)^95*100000000000000^79 ≤ 29536582593127^79*625000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      226695421 625000000 29536582593127 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1460905391/10000000000 : ℝ)^95 ≤ (1236920086883/12500000000000 : ℝ)^79 := by
    have hnat : (1460905391 : ℕ)^95*12500000000000^79 ≤ 1236920086883^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1460905391 10000000000 1236920086883 12500000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (95/16 : ℝ)) 95 79 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6590500467/10000000000 : ℝ), (226695421/625000000 : ℝ), (1460905391/10000000000 : ℝ)] ![(60568056698721/100000000000000 : ℝ), (29536582593127/100000000000000 : ℝ), (1236920086883/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6590500467/10000000000 : ℝ)|^95 ≤ (60568056698721/100000000000000 : ℝ)^79
        have hw : |(6590500467/10000000000 : ℝ)|=(6590500467/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(226695421/625000000 : ℝ)|^95 ≤ (29536582593127/100000000000000 : ℝ)^79
        have hw : |(226695421/625000000 : ℝ)|=(226695421/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1460905391/10000000000 : ℝ)|^95 ≤ (1236920086883/12500000000000 : ℝ)^79
        have hw : |(1460905391/10000000000 : ℝ)|=(1460905391/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c329060_s0_20 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ)) (x : Fin 3 → ℝ) :
    (8401139807/10000000000 : ℝ)*x 0 + (625499889/2500000000 : ℝ)*x 1 + (-345049/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (8401139807/10000000000 : ℝ)^95 ≤ (81098777129653/100000000000000 : ℝ)^79 := by
    have hnat : (8401139807 : ℕ)^95*100000000000000^79 ≤ 81098777129653^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8401139807 10000000000 81098777129653 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (625499889/2500000000 : ℝ)^95 ≤ (18898239583159/100000000000000 : ℝ)^79 := by
    have hnat : (625499889 : ℕ)^95*100000000000000^79 ≤ 18898239583159^79*2500000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      625499889 2500000000 18898239583159 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (345049/2000000000 : ℝ)^95 ≤ (29832797/1000000000000 : ℝ)^79 := by
    have hnat : (345049 : ℕ)^95*1000000000000^79 ≤ 29832797^79*2000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      345049 2000000000 29832797 1000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (95/16 : ℝ)) 95 79 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(8401139807/10000000000 : ℝ), (625499889/2500000000 : ℝ), (-345049/2000000000 : ℝ)] ![(81098777129653/100000000000000 : ℝ), (18898239583159/100000000000000 : ℝ), (29832797/1000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(8401139807/10000000000 : ℝ)|^95 ≤ (81098777129653/100000000000000 : ℝ)^79
        have hw : |(8401139807/10000000000 : ℝ)|=(8401139807/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(625499889/2500000000 : ℝ)|^95 ≤ (18898239583159/100000000000000 : ℝ)^79
        have hw : |(625499889/2500000000 : ℝ)|=(625499889/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-345049/2000000000 : ℝ)|^95 ≤ (29832797/1000000000000 : ℝ)^79
        have hw : |(-345049/2000000000 : ℝ)|=(345049/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c329060_s0_21 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-420302371/10000000000 : ℝ)*x 0 + (9994877/16000000 : ℝ)*x 1 + (-238205429/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (420302371/10000000000 : ℝ)^95 ≤ (2212022572331/100000000000000 : ℝ)^79 := by
    have hnat : (420302371 : ℕ)^95*100000000000000^79 ≤ 2212022572331^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      420302371 10000000000 2212022572331 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (9994877/16000000 : ℝ)^95 ≤ (28394985222657/50000000000000 : ℝ)^79 := by
    have hnat : (9994877 : ℕ)^95*50000000000000^79 ≤ 28394985222657^79*16000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      9994877 16000000 28394985222657 50000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (238205429/500000000 : ℝ)^95 ≤ (40998006968097/100000000000000 : ℝ)^79 := by
    have hnat : (238205429 : ℕ)^95*100000000000000^79 ≤ 40998006968097^79*500000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      238205429 500000000 40998006968097 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (95/16 : ℝ)) 95 79 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-420302371/10000000000 : ℝ), (9994877/16000000 : ℝ), (-238205429/500000000 : ℝ)] ![(2212022572331/100000000000000 : ℝ), (28394985222657/50000000000000 : ℝ), (40998006968097/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-420302371/10000000000 : ℝ)|^95 ≤ (2212022572331/100000000000000 : ℝ)^79
        have hw : |(-420302371/10000000000 : ℝ)|=(420302371/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(9994877/16000000 : ℝ)|^95 ≤ (28394985222657/50000000000000 : ℝ)^79
        have hw : |(9994877/16000000 : ℝ)|=(9994877/16000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-238205429/500000000 : ℝ)|^95 ≤ (40998006968097/100000000000000 : ℝ)^79
        have hw : |(-238205429/500000000 : ℝ)|=(238205429/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c329060_s0_22 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ)) (x : Fin 3 → ℝ) :
    (6675885213/10000000000 : ℝ)*x 0 + (-424694857/5000000000 : ℝ)*x 1 + (-4010734211/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6675885213/10000000000 : ℝ)^95 ≤ (30756460575301/50000000000000 : ℝ)^79 := by
    have hnat : (6675885213 : ℕ)^95*50000000000000^79 ≤ 30756460575301^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6675885213 10000000000 30756460575301 50000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (424694857/5000000000 : ℝ)^95 ≤ (5154864754347/100000000000000 : ℝ)^79 := by
    have hnat : (424694857 : ℕ)^95*100000000000000^79 ≤ 5154864754347^79*5000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      424694857 5000000000 5154864754347 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4010734211/10000000000 : ℝ)^95 ≤ (6666442816383/20000000000000 : ℝ)^79 := by
    have hnat : (4010734211 : ℕ)^95*20000000000000^79 ≤ 6666442816383^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4010734211 10000000000 6666442816383 20000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (95/16 : ℝ)) 95 79 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6675885213/10000000000 : ℝ), (-424694857/5000000000 : ℝ), (-4010734211/10000000000 : ℝ)] ![(30756460575301/50000000000000 : ℝ), (5154864754347/100000000000000 : ℝ), (6666442816383/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6675885213/10000000000 : ℝ)|^95 ≤ (30756460575301/50000000000000 : ℝ)^79
        have hw : |(6675885213/10000000000 : ℝ)|=(6675885213/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-424694857/5000000000 : ℝ)|^95 ≤ (5154864754347/100000000000000 : ℝ)^79
        have hw : |(-424694857/5000000000 : ℝ)|=(424694857/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-4010734211/10000000000 : ℝ)|^95 ≤ (6666442816383/20000000000000 : ℝ)^79
        have hw : |(-4010734211/10000000000 : ℝ)|=(4010734211/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c329060_s0_23 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1336282257/10000000000 : ℝ)*x 0 + (3968636223/5000000000 : ℝ)*x 1 + (131657399/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1336282257/10000000000 : ℝ)^95 ≤ (4444623014269/50000000000000 : ℝ)^79 := by
    have hnat : (1336282257 : ℕ)^95*50000000000000^79 ≤ 4444623014269^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1336282257 10000000000 4444623014269 50000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3968636223/5000000000 : ℝ)^95 ≤ (18936144419007/25000000000000 : ℝ)^79 := by
    have hnat : (3968636223 : ℕ)^95*25000000000000^79 ≤ 18936144419007^79*5000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3968636223 5000000000 18936144419007 25000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (131657399/625000000 : ℝ)^95 ≤ (3073235257907/20000000000000 : ℝ)^79 := by
    have hnat : (131657399 : ℕ)^95*20000000000000^79 ≤ 3073235257907^79*625000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      131657399 625000000 3073235257907 20000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (95/16 : ℝ)) 95 79 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1336282257/10000000000 : ℝ), (3968636223/5000000000 : ℝ), (131657399/625000000 : ℝ)] ![(4444623014269/50000000000000 : ℝ), (18936144419007/25000000000000 : ℝ), (3073235257907/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1336282257/10000000000 : ℝ)|^95 ≤ (4444623014269/50000000000000 : ℝ)^79
        have hw : |(1336282257/10000000000 : ℝ)|=(1336282257/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3968636223/5000000000 : ℝ)|^95 ≤ (18936144419007/25000000000000 : ℝ)^79
        have hw : |(3968636223/5000000000 : ℝ)|=(3968636223/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(131657399/625000000 : ℝ)|^95 ≤ (3073235257907/20000000000000 : ℝ)^79
        have hw : |(131657399/625000000 : ℝ)|=(131657399/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c329060_s0_27 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ)) (x : Fin 3 → ℝ) :
    (9181997571/10000000000 : ℝ)*x 0 + (285884647/2000000000 : ℝ)*x 1 + (-35672811/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (9181997571/10000000000 : ℝ)^95 ≤ (18049317060583/20000000000000 : ℝ)^79 := by
    have hnat : (9181997571 : ℕ)^95*20000000000000^79 ≤ 18049317060583^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      9181997571 10000000000 18049317060583 20000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (285884647/2000000000 : ℝ)^95 ≤ (60246828339/625000000000 : ℝ)^79 := by
    have hnat : (285884647 : ℕ)^95*625000000000^79 ≤ 60246828339^79*2000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      285884647 2000000000 60246828339 625000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (35672811/10000000000 : ℝ)^95 ≤ (113922153279/100000000000000 : ℝ)^79 := by
    have hnat : (35672811 : ℕ)^95*100000000000000^79 ≤ 113922153279^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      35672811 10000000000 113922153279 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (95/16 : ℝ)) 95 79 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(9181997571/10000000000 : ℝ), (285884647/2000000000 : ℝ), (-35672811/10000000000 : ℝ)] ![(18049317060583/20000000000000 : ℝ), (60246828339/625000000000 : ℝ), (113922153279/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(9181997571/10000000000 : ℝ)|^95 ≤ (18049317060583/20000000000000 : ℝ)^79
        have hw : |(9181997571/10000000000 : ℝ)|=(9181997571/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(285884647/2000000000 : ℝ)|^95 ≤ (60246828339/625000000000 : ℝ)^79
        have hw : |(285884647/2000000000 : ℝ)|=(285884647/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-35672811/10000000000 : ℝ)|^95 ≤ (113922153279/100000000000000 : ℝ)^79
        have hw : |(-35672811/10000000000 : ℝ)|=(35672811/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c329060_s1_0 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-469936377/2500000000 : ℝ)*x 0 + (3806318923/10000000000 : ℝ)*x 1 + (-6110270943/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (469936377/2500000000 : ℝ)^95 ≤ (13399270138913/100000000000000 : ℝ)^79 := by
    have hnat : (469936377 : ℕ)^95*100000000000000^79 ≤ 13399270138913^79*2500000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      469936377 2500000000 13399270138913 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3806318923/10000000000 : ℝ)^95 ≤ (31299989844453/100000000000000 : ℝ)^79 := by
    have hnat : (3806318923 : ℕ)^95*100000000000000^79 ≤ 31299989844453^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3806318923 10000000000 31299989844453 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6110270943/10000000000 : ℝ)^95 ≤ (27650370002161/50000000000000 : ℝ)^79 := by
    have hnat : (6110270943 : ℕ)^95*50000000000000^79 ≤ 27650370002161^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6110270943 10000000000 27650370002161 50000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (95/16 : ℝ)) 95 79 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-469936377/2500000000 : ℝ), (3806318923/10000000000 : ℝ), (-6110270943/10000000000 : ℝ)] ![(13399270138913/100000000000000 : ℝ), (31299989844453/100000000000000 : ℝ), (27650370002161/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-469936377/2500000000 : ℝ)|^95 ≤ (13399270138913/100000000000000 : ℝ)^79
        have hw : |(-469936377/2500000000 : ℝ)|=(469936377/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3806318923/10000000000 : ℝ)|^95 ≤ (31299989844453/100000000000000 : ℝ)^79
        have hw : |(3806318923/10000000000 : ℝ)|=(3806318923/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-6110270943/10000000000 : ℝ)|^95 ≤ (27650370002161/50000000000000 : ℝ)^79
        have hw : |(-6110270943/10000000000 : ℝ)|=(6110270943/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c329060_s1_1 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2254991197/5000000000 : ℝ)*x 0 + (-2582357157/10000000000 : ℝ)*x 1 + (-4859477551/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2254991197/5000000000 : ℝ)^95 ≤ (2398912052511/6250000000000 : ℝ)^79 := by
    have hnat : (2254991197 : ℕ)^95*6250000000000^79 ≤ 2398912052511^79*5000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2254991197 5000000000 2398912052511 6250000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2582357157/10000000000 : ℝ)^95 ≤ (19630483803079/100000000000000 : ℝ)^79 := by
    have hnat : (2582357157 : ℕ)^95*100000000000000^79 ≤ 19630483803079^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2582357157 10000000000 19630483803079 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4859477551/10000000000 : ℝ)^95 ≤ (20993461667641/50000000000000 : ℝ)^79 := by
    have hnat : (4859477551 : ℕ)^95*50000000000000^79 ≤ 20993461667641^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4859477551 10000000000 20993461667641 50000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (95/16 : ℝ)) 95 79 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2254991197/5000000000 : ℝ), (-2582357157/10000000000 : ℝ), (-4859477551/10000000000 : ℝ)] ![(2398912052511/6250000000000 : ℝ), (19630483803079/100000000000000 : ℝ), (20993461667641/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2254991197/5000000000 : ℝ)|^95 ≤ (2398912052511/6250000000000 : ℝ)^79
        have hw : |(2254991197/5000000000 : ℝ)|=(2254991197/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2582357157/10000000000 : ℝ)|^95 ≤ (19630483803079/100000000000000 : ℝ)^79
        have hw : |(-2582357157/10000000000 : ℝ)|=(2582357157/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-4859477551/10000000000 : ℝ)|^95 ≤ (20993461667641/50000000000000 : ℝ)^79
        have hw : |(-4859477551/10000000000 : ℝ)|=(4859477551/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c329060_s1_2 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ)) (x : Fin 3 → ℝ) :
    (571081099/1250000000 : ℝ)*x 0 + (1380325031/2500000000 : ℝ)*x 1 + (215285971/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (571081099/1250000000 : ℝ)^95 ≤ (19491893772527/50000000000000 : ℝ)^79 := by
    have hnat : (571081099 : ℕ)^95*50000000000000^79 ≤ 19491893772527^79*1250000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      571081099 1250000000 19491893772527 50000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1380325031/2500000000 : ℝ)^95 ≤ (48954944896689/100000000000000 : ℝ)^79 := by
    have hnat : (1380325031 : ℕ)^95*100000000000000^79 ≤ 48954944896689^79*2500000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1380325031 2500000000 48954944896689 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (215285971/1250000000 : ℝ)^95 ≤ (12061267540981/100000000000000 : ℝ)^79 := by
    have hnat : (215285971 : ℕ)^95*100000000000000^79 ≤ 12061267540981^79*1250000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      215285971 1250000000 12061267540981 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (95/16 : ℝ)) 95 79 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(571081099/1250000000 : ℝ), (1380325031/2500000000 : ℝ), (215285971/1250000000 : ℝ)] ![(19491893772527/50000000000000 : ℝ), (48954944896689/100000000000000 : ℝ), (12061267540981/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(571081099/1250000000 : ℝ)|^95 ≤ (19491893772527/50000000000000 : ℝ)^79
        have hw : |(571081099/1250000000 : ℝ)|=(571081099/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1380325031/2500000000 : ℝ)|^95 ≤ (48954944896689/100000000000000 : ℝ)^79
        have hw : |(1380325031/2500000000 : ℝ)|=(1380325031/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(215285971/1250000000 : ℝ)|^95 ≤ (12061267540981/100000000000000 : ℝ)^79
        have hw : |(215285971/1250000000 : ℝ)|=(215285971/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c329060_s1_6 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1728404369/2500000000 : ℝ)*x 0 + (730440531/2000000000 : ℝ)*x 1 + (-121481813/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1728404369/2500000000 : ℝ)^95 ≤ (64156491651759/100000000000000 : ℝ)^79 := by
    have hnat : (1728404369 : ℕ)^95*100000000000000^79 ≤ 64156491651759^79*2500000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1728404369 2500000000 64156491651759 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (730440531/2000000000 : ℝ)^95 ≤ (14891155190719/50000000000000 : ℝ)^79 := by
    have hnat : (730440531 : ℕ)^95*50000000000000^79 ≤ 14891155190719^79*2000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      730440531 2000000000 14891155190719 50000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (121481813/1250000000 : ℝ)^95 ≤ (303059897207/5000000000000 : ℝ)^79 := by
    have hnat : (121481813 : ℕ)^95*5000000000000^79 ≤ 303059897207^79*1250000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      121481813 1250000000 303059897207 5000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (95/16 : ℝ)) 95 79 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1728404369/2500000000 : ℝ), (730440531/2000000000 : ℝ), (-121481813/1250000000 : ℝ)] ![(64156491651759/100000000000000 : ℝ), (14891155190719/50000000000000 : ℝ), (303059897207/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1728404369/2500000000 : ℝ)|^95 ≤ (64156491651759/100000000000000 : ℝ)^79
        have hw : |(1728404369/2500000000 : ℝ)|=(1728404369/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(730440531/2000000000 : ℝ)|^95 ≤ (14891155190719/50000000000000 : ℝ)^79
        have hw : |(730440531/2000000000 : ℝ)|=(730440531/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-121481813/1250000000 : ℝ)|^95 ≤ (303059897207/5000000000000 : ℝ)^79
        have hw : |(-121481813/1250000000 : ℝ)|=(121481813/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c329060 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (55589/25000 : ℝ) (160257/100000 : ℝ) (10347/12500 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, false]]) : False := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (10347/12500 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (10347/12500 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (10347/12500 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (10347/12500 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (10347/12500 : ℝ)*P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (10347/12500 : ℝ)*P 2 ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((-1 : ℝ)*(X 0 1+X 1 1)) ∧ ((-1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((-1 : ℝ)*pair X 2 1) ∧ ((-1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base5 : ((1 : ℝ)*N 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 2]
  have base7 : ((1 : ℝ)*T) ≤ (160257/100000 : ℝ) := by
    linarith only [f.Tcap]
  have base11 : ((1 : ℝ)*X 0 1+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 1).2]
  have base12 : ((-1 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 2).1]
  have base25 : ((1 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 2).2]
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base43 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 2+(1 : ℝ)*P 1) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 1,f.sum]
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
  have s0_pow0 : (1 : ℝ) ^ (93/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^93 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^93*1^16 ≤ 1^16*1^93 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 93 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 93 16 (by norm_num) hpowers
    exact h
  have s0_corner0a : (2 : ℝ) ≤ (11266528166513657/10000000000000000 : ℝ) ^ (93/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (11266528166513657/10000000000000000 : ℝ)^93 := by
      have hnat : (2 : ℕ)^16*10000000000000000^93 ≤ 11266528166513657^93*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 11266528166513657 10000000000000000 16 93 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11266528166513657/10000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 93 16 (by norm_num) hpowers
    exact h
  have s0_corner0b : (3 : ℝ) ≤ (755032062721991/625000000000000 : ℝ) ^ (93/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (755032062721991/625000000000000 : ℝ)^93 := by
      have hnat : (3 : ℕ)^16*625000000000000^93 ≤ 755032062721991^93*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 755032062721991 625000000000000 16 93 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (755032062721991/625000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 93 16 (by norm_num) hpowers
    exact h
  have major_s0_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(1266528166513657/10000000000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(813984837038199/10000000000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (93/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (1266528166513657/10000000000000000 : ℝ)) (beta := (813984837038199/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow0,s0_corner0a]) (by linarith only [s0_pow0,s0_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, false]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (1 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order0.2.2])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(1266528166513657/10000000000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(813984837038199/10000000000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow1 : (1 : ℝ) ^ (93/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^93 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^93*1^16 ≤ 1^16*1^93 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 93 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 93 16 (by norm_num) hpowers
    exact h
  have s0_corner1a : (2 : ℝ) ≤ (11266528166513657/10000000000000000 : ℝ) ^ (93/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (11266528166513657/10000000000000000 : ℝ)^93 := by
      have hnat : (2 : ℕ)^16*10000000000000000^93 ≤ 11266528166513657^93*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 11266528166513657 10000000000000000 16 93 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11266528166513657/10000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 93 16 (by norm_num) hpowers
    exact h
  have s0_corner1b : (3 : ℝ) ≤ (755032062721991/625000000000000 : ℝ) ^ (93/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (755032062721991/625000000000000 : ℝ)^93 := by
      have hnat : (3 : ℕ)^16*625000000000000^93 ≤ 755032062721991^93*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 755032062721991 625000000000000 16 93 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (755032062721991/625000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 93 16 (by norm_num) hpowers
    exact h
  have major_s0_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(1266528166513657/10000000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(813984837038199/10000000000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (93/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (1266528166513657/10000000000000000 : ℝ)) (beta := (813984837038199/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow1,s0_corner1a]) (by linarith only [s0_pow1,s0_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, false]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (1 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order1.2.2])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(1266528166513657/10000000000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(813984837038199/10000000000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow2 : (1 : ℝ) ^ (93/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^93 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^93*1^16 ≤ 1^16*1^93 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 93 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 93 16 (by norm_num) hpowers
    exact h
  have s0_corner2a : (2 : ℝ) ≤ (11266528166513657/10000000000000000 : ℝ) ^ (93/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (11266528166513657/10000000000000000 : ℝ)^93 := by
      have hnat : (2 : ℕ)^16*10000000000000000^93 ≤ 11266528166513657^93*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 11266528166513657 10000000000000000 16 93 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11266528166513657/10000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 93 16 (by norm_num) hpowers
    exact h
  have s0_corner2b : (3 : ℝ) ≤ (755032062721991/625000000000000 : ℝ) ^ (93/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (755032062721991/625000000000000 : ℝ)^93 := by
      have hnat : (3 : ℕ)^16*625000000000000^93 ≤ 755032062721991^93*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 755032062721991 625000000000000 16 93 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (755032062721991/625000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 93 16 (by norm_num) hpowers
    exact h
  have major_s0_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(1266528166513657/10000000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(813984837038199/10000000000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (93/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (1266528166513657/10000000000000000 : ℝ)) (beta := (813984837038199/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow2,s0_corner2a]) (by linarith only [s0_pow2,s0_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, false]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (1 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order2.2.2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(1266528166513657/10000000000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(813984837038199/10000000000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s0_0 : ((-1223416953/10000000000 : ℝ)*X 0 0+(447949197/1000000000 : ℝ)*X 0 1+(-5984515867/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c329060_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_1 : ((4479491579/10000000000 : ℝ)*X 1 0+(-611708617/5000000000 : ℝ)*X 1 1+(-5984516033/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c329060_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_7 : ((-223928881/1250000000 : ℝ)*X 0 0+(1437628991/10000000000 : ℝ)*X 0 1+(-8102794037/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c329060_s0_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_8 : ((1243918529/5000000000 : ℝ)*X 1 0+(-627579159/10000000000 : ℝ)*X 1 1+(-810279597/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c329060_s0_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_9 : ((1102957599/5000000000 : ℝ)*X 2 0+(790330931/1000000000 : ℝ)*X 2 1+(1275186981/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c329060_s0_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_13 : ((168209117/400000000 : ℝ)*X 0 0+(3481645679/5000000000 : ℝ)*X 0 1+(-383647/2000000000 : ℝ)*X 0 2+(168209117/400000000 : ℝ)*X 1 0+(3481645679/5000000000 : ℝ)*X 1 1+(-383647/2000000000 : ℝ)*X 1 2+(168209117/400000000 : ℝ)*X 2 0+(3481645679/5000000000 : ℝ)*X 2 1+(-383647/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c329060_s0_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_14 : ((-862151791/10000000000 : ℝ)*X 0 0+(2136714497/10000000000 : ℝ)*X 0 1+(-257198799/312500000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c329060_s0_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_15 : ((962160429/10000000000 : ℝ)*X 1 0+(-513051991/2500000000 : ℝ)*X 1 1+(-4115180617/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c329060_s0_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_16 : ((6590500467/10000000000 : ℝ)*X 2 0+(226695421/625000000 : ℝ)*X 2 1+(1460905391/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c329060_s0_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_20 : ((8401139807/10000000000 : ℝ)*X 0 0+(625499889/2500000000 : ℝ)*X 0 1+(-345049/2000000000 : ℝ)*X 0 2+(8401139807/10000000000 : ℝ)*X 1 0+(625499889/2500000000 : ℝ)*X 1 1+(-345049/2000000000 : ℝ)*X 1 2+(8401139807/10000000000 : ℝ)*X 2 0+(625499889/2500000000 : ℝ)*X 2 1+(-345049/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c329060_s0_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_21 : ((-420302371/10000000000 : ℝ)*X 0 0+(9994877/16000000 : ℝ)*X 0 1+(-238205429/500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c329060_s0_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_22 : ((6675885213/10000000000 : ℝ)*X 1 0+(-424694857/5000000000 : ℝ)*X 1 1+(-4010734211/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c329060_s0_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_23 : ((1336282257/10000000000 : ℝ)*X 2 0+(3968636223/5000000000 : ℝ)*X 2 1+(131657399/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c329060_s0_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_27 : ((9181997571/10000000000 : ℝ)*X 0 0+(285884647/2000000000 : ℝ)*X 0 1+(-35672811/10000000000 : ℝ)*X 0 2+(9181997571/10000000000 : ℝ)*X 1 0+(285884647/2000000000 : ℝ)*X 1 1+(-35672811/10000000000 : ℝ)*X 1 2+(9181997571/10000000000 : ℝ)*X 2 0+(285884647/2000000000 : ℝ)*X 2 1+(-35672811/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c329060_s0_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s0_0 : (0 : ℝ) ≤ ((12149/20000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(12149/20000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (63609400759392279/10000000000000000000000 : ℝ) := by norm_num
    linear_combination (226596347341/1000000000000 : ℝ)*(base5) + (1220650173673/1000000000000 : ℝ)*(base7) + (659159/500000000000 : ℝ)*(base59) + (1564286431029/1000000000000 : ℝ)*(major_s0_0) + (1564286431029/1000000000000 : ℝ)*(major_s0_1) + (1564286431029/1000000000000 : ℝ)*(major_s0_2) + (4167/1953125000 : ℝ)*(sp_s0_0) + (2568609/1000000000000 : ℝ)*(sp_s0_1) + (1772983151973/1000000000000 : ℝ)*(sp_s0_7) + (1773002357761/1000000000000 : ℝ)*(sp_s0_8) + (999801294543/500000000000 : ℝ)*(sp_s0_9) + (848779605027/500000000000 : ℝ)*(sp_s0_13) + (5239067/250000000000 : ℝ)*(sp_s0_14) + (657687/500000000000 : ℝ)*(sp_s0_15) + (351752691861/500000000000 : ℝ)*(f.failure) + (354601248349/200000000000 : ℝ)*(f.sum) + (483972644063053/5000000000000000000000000000 : ℝ)*base63 + (1149627302876771/10000000000000000000000000000 : ℝ)*base64 + (3089820534876771/10000000000000000000000000000 : ℝ)*base67 + (942893972063053/10000000000000000000000000000 : ℝ)*base69 + (498955412906859/5000000000000000000000000000 : ℝ)*base70 + (5245737875123229/10000000000000000000000000000 : ℝ)*base72 + (1626348860936947/10000000000000000000000000000 : ℝ)*base74 + (2461565874936947/10000000000000000000000000000 : ℝ)*base76 + (324492686123229/5000000000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base82 + (1371/12500000000000000 : ℝ)*base86 + (1371/12500000000000000 : ℝ)*base88 + (1371/12500000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s0_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(60607/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(60607/100000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (48838510604033377057509/2500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (550371/1000000000000 : ℝ)*(base5) + (607088436019/500000000000 : ℝ)*(base7) + (549631/100000000000 : ℝ)*(base12) + (12463586539/200000000000 : ℝ)*(base60) + (1493034810131/1000000000000 : ℝ)*(major_s0_0) + (1493034810131/1000000000000 : ℝ)*(major_s0_1) + (1493034810131/1000000000000 : ℝ)*(major_s0_2) + (27473/250000000000 : ℝ)*(sp_s0_1) + (20635591/250000000000 : ℝ)*(sp_s0_7) + (208239060217/125000000000 : ℝ)*(sp_s0_14) + (833000205259/500000000000 : ℝ)*(sp_s0_15) + (833000535391/500000000000 : ℝ)*(sp_s0_16) + (471399386727/250000000000 : ℝ)*(sp_s0_20) + (40219527/1000000000000 : ℝ)*(sp_s0_27) + (671461444769/1000000000000 : ℝ)*(f.failure) + (166600052041/100000000000 : ℝ)*(f.sum) + (2292816700959067/5000000000000000000000000000 : ℝ)*base63 + (4228895431805931/10000000000000000000000000000 : ℝ)*base65 + (3463701267805931/10000000000000000000000000000 : ℝ)*base66 + (8248503850459067/10000000000000000000000000000 : ℝ)*base69 + (308486120632499/5000000000000000000000000000 : ℝ)*base71 + (3890149135805931/10000000000000000000000000000 : ℝ)*base72 + (5441040346459067/10000000000000000000000000000 : ℝ)*base75 + (3361120968459067/10000000000000000000000000000 : ℝ)*base77 + (57536093305931/5000000000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base85 + (11059/25000000000000000 : ℝ)*base86 + (11059/25000000000000000 : ℝ)*base88 + (11059/25000000000000000 : ℝ)*base90 + (1/1000000000000 : ℝ)*base92 + hcertificate_margin
  have ratio_s0_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-49993/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-49993/100000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (35680174597102048377/7812500000000000000000000 : ℝ) := by norm_num
    linear_combination (910255929387/1000000000000 : ℝ)*(base7) + (141089941249/1000000000000 : ℝ)*(base39) + (434839/125000000000 : ℝ)*(base43) + (744917/1000000000000 : ℝ)*(base50) + (380425899999/250000000000 : ℝ)*(major_s0_0) + (380425030321/250000000000 : ℝ)*(major_s0_1) + (380425899999/250000000000 : ℝ)*(major_s0_2) + (4650097/1000000000000 : ℝ)*(sp_s0_0) + (6816817/250000000000 : ℝ)*(sp_s0_9) + (1569287/1000000000000 : ℝ)*(sp_s0_20) + (1872793295397/1000000000000 : ℝ)*(sp_s0_21) + (1872801424207/1000000000000 : ℝ)*(sp_s0_22) + (936385339113/500000000000 : ℝ)*(sp_s0_23) + (797304499303/500000000000 : ℝ)*(sp_s0_27) + (342177319253/500000000000 : ℝ)*(f.failure) + (1872801424207/1000000000000 : ℝ)*(f.sum) + (7571695053939/15625000000000000000000000 : ℝ)*base63 + (804246208688199/2500000000000000000000000000 : ℝ)*base65 + (1364539804768121/2500000000000000000000000000 : ℝ)*base66 + (801262831713657/2500000000000000000000000000 : ℝ)*base68 + (10067093362271/1250000000000000000000000000 : ℝ)*base71 + (824728481561801/2500000000000000000000000000 : ℝ)*base73 + (1191533890343897/2500000000000000000000000000 : ℝ)*base75 + (1071080135286343/2500000000000000000000000000 : ℝ)*base77 + (1270969844463/3906250000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base80 + (1/1000000000000 : ℝ)*base84 + (5017/12500000000000000 : ℝ)*base87 + (5017/12500000000000000 : ℝ)*base89 + (5017/12500000000000000 : ℝ)*base91 + hcertificate_margin
  have s1_pow0 : (12149/20000 : ℝ) ^ (93/16 : ℝ) ≤ (2758195192384333133/50000000000000000000 : ℝ) := by
    have hpowers : (12149/20000 : ℝ)^93 ≤ (2758195192384333133/50000000000000000000 : ℝ)^16 := by
      have hnat : (12149 : ℕ)^93*50000000000000000000^16 ≤ 2758195192384333133^16*20000^93 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12149 20000 2758195192384333133 50000000000000000000 93 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (12149/20000 : ℝ)) (X := (2758195192384333133/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 93 16 (by norm_num) hpowers
    exact h
  have s1_corner0a : (52758195192384333133/50000000000000000000 : ℝ) ≤ (2018561687029663/2000000000000000 : ℝ) ^ (93/16 : ℝ) := by
    have hpowers : (52758195192384333133/50000000000000000000 : ℝ)^16 ≤ (2018561687029663/2000000000000000 : ℝ)^93 := by
      have hnat : (52758195192384333133 : ℕ)^16*2000000000000000^93 ≤ 2018561687029663^93*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        52758195192384333133 50000000000000000000 2018561687029663 2000000000000000 16 93 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2018561687029663/2000000000000000 : ℝ)) (X := (52758195192384333133/50000000000000000000 : ℝ)) (by norm_num) 93 16 (by norm_num) hpowers
    exact h
  have s1_corner0b : (27758195192384333133/25000000000000000000 : ℝ) ≤ (318177588416563/312500000000000 : ℝ) ^ (93/16 : ℝ) := by
    have hpowers : (27758195192384333133/25000000000000000000 : ℝ)^16 ≤ (318177588416563/312500000000000 : ℝ)^93 := by
      have hnat : (27758195192384333133 : ℕ)^16*312500000000000^93 ≤ 318177588416563^93*25000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        27758195192384333133 25000000000000000000 318177588416563 312500000000000 16 93 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (318177588416563/312500000000000 : ℝ)) (X := (27758195192384333133/25000000000000000000 : ℝ)) (by norm_num) 93 16 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(18561687029663/1214900000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(88874394181701/6074500000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (93/16 : ℝ)) (rho := (12149/20000 : ℝ)) (alpha := (18561687029663/1214900000000000 : ℝ)) (beta := (88874394181701/6074500000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, false]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (12149/20000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(18561687029663/1214900000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(88874394181701/6074500000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (60607/100000 : ℝ) ^ (93/16 : ℝ) ≤ (170123270392032139/3125000000000000000 : ℝ) := by
    have hpowers : (60607/100000 : ℝ)^93 ≤ (170123270392032139/3125000000000000000 : ℝ)^16 := by
      have hnat : (60607 : ℕ)^93*3125000000000000000^16 ≤ 170123270392032139^16*100000^93 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        60607 100000 170123270392032139 3125000000000000000 93 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (60607/100000 : ℝ)) (X := (170123270392032139/3125000000000000000 : ℝ)) (by norm_num) (by norm_num) 93 16 (by norm_num) hpowers
    exact h
  have s1_corner1a : (3295123270392032139/3125000000000000000 : ℝ) ≤ (10091615915842747/10000000000000000 : ℝ) ^ (93/16 : ℝ) := by
    have hpowers : (3295123270392032139/3125000000000000000 : ℝ)^16 ≤ (10091615915842747/10000000000000000 : ℝ)^93 := by
      have hnat : (3295123270392032139 : ℕ)^16*10000000000000000^93 ≤ 10091615915842747^93*3125000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3295123270392032139 3125000000000000000 10091615915842747 10000000000000000 16 93 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10091615915842747/10000000000000000 : ℝ)) (X := (3295123270392032139/3125000000000000000 : ℝ)) (by norm_num) 93 16 (by norm_num) hpowers
    exact h
  have s1_corner1b : (1732623270392032139/1562500000000000000 : ℝ) ≤ (2544848935272669/2500000000000000 : ℝ) ^ (93/16 : ℝ) := by
    have hpowers : (1732623270392032139/1562500000000000000 : ℝ)^16 ≤ (2544848935272669/2500000000000000 : ℝ)^93 := by
      have hnat : (1732623270392032139 : ℕ)^16*2500000000000000^93 ≤ 2544848935272669^93*1562500000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1732623270392032139 1562500000000000000 2544848935272669 2500000000000000 16 93 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2544848935272669/2500000000000000 : ℝ)) (X := (1732623270392032139/1562500000000000000 : ℝ)) (by norm_num) 93 16 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(91615915842747/6060700000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(87779825247929/6060700000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (93/16 : ℝ)) (rho := (60607/100000 : ℝ)) (alpha := (91615915842747/6060700000000000 : ℝ)) (beta := (87779825247929/6060700000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, false]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (60607/100000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(91615915842747/6060700000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(87779825247929/6060700000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (49993/100000 : ℝ) ^ (93/16 : ℝ) ≤ (444477444385962393/25000000000000000000 : ℝ) := by
    have hpowers : (49993/100000 : ℝ)^93 ≤ (444477444385962393/25000000000000000000 : ℝ)^16 := by
      have hnat : (49993 : ℕ)^93*25000000000000000000^16 ≤ 444477444385962393^16*100000^93 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        49993 100000 444477444385962393 25000000000000000000 93 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (49993/100000 : ℝ)) (X := (444477444385962393/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 93 16 (by norm_num) hpowers
    exact h
  have s1_corner2a : (25444477444385962393/25000000000000000000 : ℝ) ≤ (10030364973267061/10000000000000000 : ℝ) ^ (93/16 : ℝ) := by
    have hpowers : (25444477444385962393/25000000000000000000 : ℝ)^16 ≤ (10030364973267061/10000000000000000 : ℝ)^93 := by
      have hnat : (25444477444385962393 : ℕ)^16*10000000000000000^93 ≤ 10030364973267061^93*25000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25444477444385962393 25000000000000000000 10030364973267061 10000000000000000 16 93 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10030364973267061/10000000000000000 : ℝ)) (X := (25444477444385962393/25000000000000000000 : ℝ)) (by norm_num) 93 16 (by norm_num) hpowers
    exact h
  have s1_corner2b : (12944477444385962393/12500000000000000000 : ℝ) ≤ (5030146950910833/5000000000000000 : ℝ) ^ (93/16 : ℝ) := by
    have hpowers : (12944477444385962393/12500000000000000000 : ℝ)^16 ≤ (5030146950910833/5000000000000000 : ℝ)^93 := by
      have hnat : (12944477444385962393 : ℕ)^16*5000000000000000^93 ≤ 5030146950910833^93*12500000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12944477444385962393 12500000000000000000 5030146950910833 5000000000000000 16 93 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5030146950910833/5000000000000000 : ℝ)) (X := (12944477444385962393/12500000000000000000 : ℝ)) (by norm_num) 93 16 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(30364973267061/4999300000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(5985785710921/999860000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (93/16 : ℝ)) (rho := (49993/100000 : ℝ)) (alpha := (30364973267061/4999300000000000 : ℝ)) (beta := (5985785710921/999860000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, false]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (49993/100000 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(30364973267061/4999300000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(5985785710921/999860000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-469936377/2500000000 : ℝ)*X 0 0+(3806318923/10000000000 : ℝ)*X 0 1+(-6110270943/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c329060_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_1 : ((2254991197/5000000000 : ℝ)*X 1 0+(-2582357157/10000000000 : ℝ)*X 1 1+(-4859477551/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c329060_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((571081099/1250000000 : ℝ)*X 2 0+(1380325031/2500000000 : ℝ)*X 2 1+(215285971/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c329060_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_6 : ((1728404369/2500000000 : ℝ)*X 0 0+(730440531/2000000000 : ℝ)*X 0 1+(-121481813/1250000000 : ℝ)*X 0 2+(1728404369/2500000000 : ℝ)*X 1 0+(730440531/2000000000 : ℝ)*X 1 1+(-121481813/1250000000 : ℝ)*X 1 2+(1728404369/2500000000 : ℝ)*X 2 0+(730440531/2000000000 : ℝ)*X 2 1+(-121481813/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c329060_s1_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have hsep : (-129267/12500 : ℝ) < ((-55589/25000 : ℝ)*P 0+(-55589/25000 : ℝ)*P 1+(-55589/25000 : ℝ)*P 2+(1 : ℝ)*T) := by
    have hcertificate_margin : (-129267/12500 : ℝ) < (-9462049626796114284935600535909292161/920264198722475000000000000000000000 : ℝ) := by norm_num
    linear_combination (85279/250000000000 : ℝ)*(base11) + (487633/1000000000000 : ℝ)*(base12) + (877/40000000000 : ℝ)*(base25) + (53544532741/125000000000 : ℝ)*(base39) + (44901/500000000000 : ℝ)*(base40) + (36157/500000000000 : ℝ)*(base43) + (33780652101/62500000000 : ℝ)*(base59) + (55589/25000 : ℝ)*(major_s1_0) + (1111779963843/500000000000 : ℝ)*(major_s1_1) + (1111780016963/500000000000 : ℝ)*(major_s1_2) + (3427293656521/1000000000000 : ℝ)*(sp_s1_0) + (685458911517/200000000000 : ℝ)*(sp_s1_1) + (171364721471/50000000000 : ℝ)*(sp_s1_2) + (1 : ℝ)*(sp_s1_6) + (3427294523659/1000000000000 : ℝ)*(f.sum) + (5488188218017183853/75748143775000000000000000000000 : ℝ)*base62 + (68594262987371/249965000000000000000000000 : ℝ)*base64 + (165399207954281/378793750000000000000000000 : ℝ)*base66 + (516556592797107/2499650000000000000000000000 : ℝ)*base68 + (2000698059348413931/3036824785000000000000000000000 : ℝ)*base70 + (11348332019183/24298000000000000000000000 : ℝ)*base73 + (216945130754321/3030350000000000000000000000 : ℝ)*base75 + (837863511549/1518625000000000000000000 : ℝ)*base76 + (5796155835345445497/36815722150000000000000000000000 : ℝ)*base78 + (1357/40000000000 : ℝ)*base81 + (16963/500000000000 : ℝ)*base83 + (16963/500000000000 : ℝ)*base90 + hcertificate_margin
  linarith only [hsep,f.failure]

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
namespace HlawkaSchatten.DiagonalCutoff4
theorem coarse_distinct_p029_b030 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ))
    (c : Fin 88) (hlo : 60 ≤ c.val) (hhi : c.val < 62)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (55589/25000 : ℝ) (160257/100000 : ℝ) (10347/12500 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  have hc : c=60 ∨ c=61 := by omega
  rcases hc with rfl|rfl
  · exact collision_c329060 p hpa (by linarith only [hpb]) X hX
  · exact collision_c329061 p hpa (by linarith only [hpb]) X hX

end HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ))
    (c : Fin 88) (hlo : 60 ≤ c.val) (hhi : c.val < 62)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (55589/25000 : ℝ) (160257/100000 : ℝ) (10347/12500 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  exact HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p029_b030 p hpa hpb c hlo hhi hn63 hn87 X hX

#print axioms solution
