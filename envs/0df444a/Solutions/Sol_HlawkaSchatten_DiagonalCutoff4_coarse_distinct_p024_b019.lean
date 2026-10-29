-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p024_b019
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T01:56:10.35083+00:00
-- url     : https://prove2.me/submissions/600829e8-6277-419b-ad15-2f85adb00f87

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_FiniteCharts
import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
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
theorem collision_support_c324039_s0_0 (p : ℝ) (hpa : (21/4 : ℝ) ≤ p) (hpb : p ≤ (43/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-57532233/500000000 : ℝ)*x 0 + (-6192254501/10000000000 : ℝ)*x 1 + (2249544041/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (57532233/500000000 : ℝ)^43 ≤ (1754846886751/25000000000000 : ℝ)^35 := by
    have hnat : (57532233 : ℕ)^43*25000000000000^35 ≤ 1754846886751^35*500000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      57532233 500000000 1754846886751 25000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6192254501/10000000000 : ℝ)^43 ≤ (13874309825747/25000000000000 : ℝ)^35 := by
    have hnat : (6192254501 : ℕ)^43*25000000000000^35 ≤ 13874309825747^35*10000000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6192254501 10000000000 13874309825747 25000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2249544041/5000000000 : ℝ)^43 ≤ (37483373135577/100000000000000 : ℝ)^35 := by
    have hnat : (2249544041 : ℕ)^43*100000000000000^35 ≤ 37483373135577^35*5000000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2249544041 5000000000 37483373135577 100000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (43/8 : ℝ)) 43 35 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-57532233/500000000 : ℝ), (-6192254501/10000000000 : ℝ), (2249544041/5000000000 : ℝ)] ![(1754846886751/25000000000000 : ℝ), (13874309825747/25000000000000 : ℝ), (37483373135577/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-57532233/500000000 : ℝ)|^43 ≤ (1754846886751/25000000000000 : ℝ)^35
        have hw : |(-57532233/500000000 : ℝ)|=(57532233/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-6192254501/10000000000 : ℝ)|^43 ≤ (13874309825747/25000000000000 : ℝ)^35
        have hw : |(-6192254501/10000000000 : ℝ)|=(6192254501/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2249544041/5000000000 : ℝ)|^43 ≤ (37483373135577/100000000000000 : ℝ)^35
        have hw : |(2249544041/5000000000 : ℝ)|=(2249544041/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c324039_s0_1 (p : ℝ) (hpa : (21/4 : ℝ) ≤ p) (hpb : p ≤ (43/8 : ℝ)) (x : Fin 3 → ℝ) :
    (4703900879/10000000000 : ℝ)*x 0 + (3742487901/10000000000 : ℝ)*x 1 + (3805509077/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4703900879/10000000000 : ℝ)^43 ≤ (39590542768181/100000000000000 : ℝ)^35 := by
    have hnat : (4703900879 : ℕ)^43*100000000000000^35 ≤ 39590542768181^35*10000000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4703900879 10000000000 39590542768181 100000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3742487901/10000000000 : ℝ)^43 ≤ (14947448760117/50000000000000 : ℝ)^35 := by
    have hnat : (3742487901 : ℕ)^43*50000000000000^35 ≤ 14947448760117^35*10000000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3742487901 10000000000 14947448760117 50000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3805509077/10000000000 : ℝ)^43 ≤ (6102911939751/20000000000000 : ℝ)^35 := by
    have hnat : (3805509077 : ℕ)^43*20000000000000^35 ≤ 6102911939751^35*10000000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3805509077 10000000000 6102911939751 20000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (43/8 : ℝ)) 43 35 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4703900879/10000000000 : ℝ), (3742487901/10000000000 : ℝ), (3805509077/10000000000 : ℝ)] ![(39590542768181/100000000000000 : ℝ), (14947448760117/50000000000000 : ℝ), (6102911939751/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4703900879/10000000000 : ℝ)|^43 ≤ (39590542768181/100000000000000 : ℝ)^35
        have hw : |(4703900879/10000000000 : ℝ)|=(4703900879/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3742487901/10000000000 : ℝ)|^43 ≤ (14947448760117/50000000000000 : ℝ)^35
        have hw : |(3742487901/10000000000 : ℝ)|=(3742487901/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3805509077/10000000000 : ℝ)|^43 ≤ (6102911939751/20000000000000 : ℝ)^35
        have hw : |(3805509077/10000000000 : ℝ)|=(3805509077/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c324039_s0_2 (p : ℝ) (hpa : (21/4 : ℝ) ≤ p) (hpb : p ≤ (43/8 : ℝ)) (x : Fin 3 → ℝ) :
    (1175974999/2500000000 : ℝ)*x 0 + (-3698735101/10000000000 : ℝ)*x 1 + (-6014033/15625000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1175974999/2500000000 : ℝ)^43 ≤ (9897633409421/25000000000000 : ℝ)^35 := by
    have hnat : (1175974999 : ℕ)^43*25000000000000^35 ≤ 9897633409421^35*2500000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1175974999 2500000000 9897633409421 25000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3698735101/10000000000 : ℝ)^43 ≤ (1841630740351/6250000000000 : ℝ)^35 := by
    have hnat : (3698735101 : ℕ)^43*6250000000000^35 ≤ 1841630740351^35*10000000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3698735101 10000000000 1841630740351 6250000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6014033/15625000 : ℝ)^43 ≤ (15471687251487/50000000000000 : ℝ)^35 := by
    have hnat : (6014033 : ℕ)^43*50000000000000^35 ≤ 15471687251487^35*15625000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6014033 15625000 15471687251487 50000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (43/8 : ℝ)) 43 35 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1175974999/2500000000 : ℝ), (-3698735101/10000000000 : ℝ), (-6014033/15625000 : ℝ)] ![(9897633409421/25000000000000 : ℝ), (1841630740351/6250000000000 : ℝ), (15471687251487/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1175974999/2500000000 : ℝ)|^43 ≤ (9897633409421/25000000000000 : ℝ)^35
        have hw : |(1175974999/2500000000 : ℝ)|=(1175974999/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3698735101/10000000000 : ℝ)|^43 ≤ (1841630740351/6250000000000 : ℝ)^35
        have hw : |(-3698735101/10000000000 : ℝ)|=(3698735101/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-6014033/15625000 : ℝ)|^43 ≤ (15471687251487/50000000000000 : ℝ)^35
        have hw : |(-6014033/15625000 : ℝ)|=(6014033/15625000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c324039_s0_7 (p : ℝ) (hpa : (21/4 : ℝ) ≤ p) (hpb : p ≤ (43/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-235097687/10000000000 : ℝ)*x 0 + (-3951419171/5000000000 : ℝ)*x 1 + (1570919303/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (235097687/10000000000 : ℝ)^43 ≤ (997613382547/100000000000000 : ℝ)^35 := by
    have hnat : (235097687 : ℕ)^43*100000000000000^35 ≤ 997613382547^35*10000000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      235097687 10000000000 997613382547 100000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3951419171/5000000000 : ℝ)^43 ≤ (18722301883653/25000000000000 : ℝ)^35 := by
    have hnat : (3951419171 : ℕ)^43*25000000000000^35 ≤ 18722301883653^35*5000000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3951419171 5000000000 18722301883653 25000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1570919303/5000000000 : ℝ)^43 ≤ (12056589530509/50000000000000 : ℝ)^35 := by
    have hnat : (1570919303 : ℕ)^43*50000000000000^35 ≤ 12056589530509^35*5000000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1570919303 5000000000 12056589530509 50000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (43/8 : ℝ)) 43 35 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-235097687/10000000000 : ℝ), (-3951419171/5000000000 : ℝ), (1570919303/5000000000 : ℝ)] ![(997613382547/100000000000000 : ℝ), (18722301883653/25000000000000 : ℝ), (12056589530509/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-235097687/10000000000 : ℝ)|^43 ≤ (997613382547/100000000000000 : ℝ)^35
        have hw : |(-235097687/10000000000 : ℝ)|=(235097687/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3951419171/5000000000 : ℝ)|^43 ≤ (18722301883653/25000000000000 : ℝ)^35
        have hw : |(-3951419171/5000000000 : ℝ)|=(3951419171/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1570919303/5000000000 : ℝ)|^43 ≤ (12056589530509/50000000000000 : ℝ)^35
        have hw : |(1570919303/5000000000 : ℝ)|=(1570919303/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c324039_s0_8 (p : ℝ) (hpa : (21/4 : ℝ) ≤ p) (hpb : p ≤ (43/8 : ℝ)) (x : Fin 3 → ℝ) :
    (3053113727/10000000000 : ℝ)*x 0 + (2188582101/5000000000 : ℝ)*x 1 + (4789875971/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3053113727/10000000000 : ℝ)^43 ≤ (2327930171749/10000000000000 : ℝ)^35 := by
    have hnat : (3053113727 : ℕ)^43*10000000000000^35 ≤ 2327930171749^35*10000000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3053113727 10000000000 2327930171749 10000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2188582101/5000000000 : ℝ)^43 ≤ (7247859550879/20000000000000 : ℝ)^35 := by
    have hnat : (2188582101 : ℕ)^43*20000000000000^35 ≤ 7247859550879^35*5000000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2188582101 5000000000 7247859550879 20000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4789875971/10000000000 : ℝ)^43 ≤ (20240700258631/50000000000000 : ℝ)^35 := by
    have hnat : (4789875971 : ℕ)^43*50000000000000^35 ≤ 20240700258631^35*10000000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4789875971 10000000000 20240700258631 50000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (43/8 : ℝ)) 43 35 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3053113727/10000000000 : ℝ), (2188582101/5000000000 : ℝ), (4789875971/10000000000 : ℝ)] ![(2327930171749/10000000000000 : ℝ), (7247859550879/20000000000000 : ℝ), (20240700258631/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3053113727/10000000000 : ℝ)|^43 ≤ (2327930171749/10000000000000 : ℝ)^35
        have hw : |(3053113727/10000000000 : ℝ)|=(3053113727/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2188582101/5000000000 : ℝ)|^43 ≤ (7247859550879/20000000000000 : ℝ)^35
        have hw : |(2188582101/5000000000 : ℝ)|=(2188582101/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4789875971/10000000000 : ℝ)|^43 ≤ (20240700258631/50000000000000 : ℝ)^35
        have hw : |(4789875971/10000000000 : ℝ)|=(4789875971/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c324039_s0_9 (p : ℝ) (hpa : (21/4 : ℝ) ≤ p) (hpb : p ≤ (43/8 : ℝ)) (x : Fin 3 → ℝ) :
    (2399801547/5000000000 : ℝ)*x 0 + (-1307488449/5000000000 : ℝ)*x 1 + (-4760113367/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2399801547/5000000000 : ℝ)^43 ≤ (317050177457/781250000000 : ℝ)^35 := by
    have hnat : (2399801547 : ℕ)^43*781250000000^35 ≤ 317050177457^35*5000000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2399801547 5000000000 317050177457 781250000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1307488449/5000000000 : ℝ)^43 ≤ (19244988335727/100000000000000 : ℝ)^35 := by
    have hnat : (1307488449 : ℕ)^43*100000000000000^35 ≤ 19244988335727^35*5000000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1307488449 5000000000 19244988335727 100000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4760113367/10000000000 : ℝ)^43 ≤ (40172588929481/100000000000000 : ℝ)^35 := by
    have hnat : (4760113367 : ℕ)^43*100000000000000^35 ≤ 40172588929481^35*10000000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4760113367 10000000000 40172588929481 100000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (43/8 : ℝ)) 43 35 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2399801547/5000000000 : ℝ), (-1307488449/5000000000 : ℝ), (-4760113367/10000000000 : ℝ)] ![(317050177457/781250000000 : ℝ), (19244988335727/100000000000000 : ℝ), (40172588929481/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2399801547/5000000000 : ℝ)|^43 ≤ (317050177457/781250000000 : ℝ)^35
        have hw : |(2399801547/5000000000 : ℝ)|=(2399801547/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1307488449/5000000000 : ℝ)|^43 ≤ (19244988335727/100000000000000 : ℝ)^35
        have hw : |(-1307488449/5000000000 : ℝ)|=(1307488449/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-4760113367/10000000000 : ℝ)|^43 ≤ (40172588929481/100000000000000 : ℝ)^35
        have hw : |(-4760113367/10000000000 : ℝ)|=(4760113367/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c324039_s0_13 (p : ℝ) (hpa : (21/4 : ℝ) ≤ p) (hpb : p ≤ (43/8 : ℝ)) (x : Fin 3 → ℝ) :
    (6554795627/10000000000 : ℝ)*x 0 + (53977/250000000 : ℝ)*x 1 + (4789875971/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6554795627/10000000000 : ℝ)^43 ≤ (29757731694141/50000000000000 : ℝ)^35 := by
    have hnat : (6554795627 : ℕ)^43*50000000000000^35 ≤ 29757731694141^35*10000000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6554795627 10000000000 29757731694141 50000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (53977/250000000 : ℝ)^43 ≤ (125443249/4000000000000 : ℝ)^35 := by
    have hnat : (53977 : ℕ)^43*4000000000000^35 ≤ 125443249^35*250000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      53977 250000000 125443249 4000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4789875971/10000000000 : ℝ)^43 ≤ (20240700258631/50000000000000 : ℝ)^35 := by
    have hnat : (4789875971 : ℕ)^43*50000000000000^35 ≤ 20240700258631^35*10000000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4789875971 10000000000 20240700258631 50000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (43/8 : ℝ)) 43 35 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6554795627/10000000000 : ℝ), (53977/250000000 : ℝ), (4789875971/10000000000 : ℝ)] ![(29757731694141/50000000000000 : ℝ), (125443249/4000000000000 : ℝ), (20240700258631/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6554795627/10000000000 : ℝ)|^43 ≤ (29757731694141/50000000000000 : ℝ)^35
        have hw : |(6554795627/10000000000 : ℝ)|=(6554795627/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(53977/250000000 : ℝ)|^43 ≤ (125443249/4000000000000 : ℝ)^35
        have hw : |(53977/250000000 : ℝ)|=(53977/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4789875971/10000000000 : ℝ)|^43 ≤ (20240700258631/50000000000000 : ℝ)^35
        have hw : |(4789875971/10000000000 : ℝ)|=(4789875971/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c324039_s0_14 (p : ℝ) (hpa : (21/4 : ℝ) ≤ p) (hpb : p ≤ (43/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-80843051/5000000000 : ℝ)*x 0 + (-2735498029/5000000000 : ℝ)*x 1 + (1169129829/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (80843051/5000000000 : ℝ)^43 ≤ (629834504277/100000000000000 : ℝ)^35 := by
    have hnat : (80843051 : ℕ)^43*100000000000000^35 ≤ 629834504277^35*5000000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      80843051 5000000000 629834504277 100000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2735498029/5000000000 : ℝ)^43 ≤ (23832295190239/50000000000000 : ℝ)^35 := by
    have hnat : (2735498029 : ℕ)^43*50000000000000^35 ≤ 23832295190239^35*5000000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2735498029 5000000000 23832295190239 50000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1169129829/2000000000 : ℝ)^43 ≤ (6463196888809/12500000000000 : ℝ)^35 := by
    have hnat : (1169129829 : ℕ)^43*12500000000000^35 ≤ 6463196888809^35*2000000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1169129829 2000000000 6463196888809 12500000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (43/8 : ℝ)) 43 35 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-80843051/5000000000 : ℝ), (-2735498029/5000000000 : ℝ), (1169129829/2000000000 : ℝ)] ![(629834504277/100000000000000 : ℝ), (23832295190239/50000000000000 : ℝ), (6463196888809/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-80843051/5000000000 : ℝ)|^43 ≤ (629834504277/100000000000000 : ℝ)^35
        have hw : |(-80843051/5000000000 : ℝ)|=(80843051/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2735498029/5000000000 : ℝ)|^43 ≤ (23832295190239/50000000000000 : ℝ)^35
        have hw : |(-2735498029/5000000000 : ℝ)|=(2735498029/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1169129829/2000000000 : ℝ)|^43 ≤ (6463196888809/12500000000000 : ℝ)^35
        have hw : |(1169129829/2000000000 : ℝ)|=(1169129829/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c324039_s0_15 (p : ℝ) (hpa : (21/4 : ℝ) ≤ p) (hpb : p ≤ (43/8 : ℝ)) (x : Fin 3 → ℝ) :
    (3338830211/10000000000 : ℝ)*x 0 + (1041518047/2500000000 : ℝ)*x 1 + (591872047/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3338830211/10000000000 : ℝ)^43 ≤ (6495934237867/25000000000000 : ℝ)^35 := by
    have hnat : (3338830211 : ℕ)^43*25000000000000^35 ≤ 6495934237867^35*10000000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3338830211 10000000000 6495934237867 25000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1041518047/2500000000 : ℝ)^43 ≤ (34104147684891/100000000000000 : ℝ)^35 := by
    have hnat : (1041518047 : ℕ)^43*100000000000000^35 ≤ 34104147684891^35*2500000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1041518047 2500000000 34104147684891 100000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (591872047/1250000000 : ℝ)^43 ≤ (9978028836271/25000000000000 : ℝ)^35 := by
    have hnat : (591872047 : ℕ)^43*25000000000000^35 ≤ 9978028836271^35*1250000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      591872047 1250000000 9978028836271 25000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (43/8 : ℝ)) 43 35 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3338830211/10000000000 : ℝ), (1041518047/2500000000 : ℝ), (591872047/1250000000 : ℝ)] ![(6495934237867/25000000000000 : ℝ), (34104147684891/100000000000000 : ℝ), (9978028836271/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3338830211/10000000000 : ℝ)|^43 ≤ (6495934237867/25000000000000 : ℝ)^35
        have hw : |(3338830211/10000000000 : ℝ)|=(3338830211/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1041518047/2500000000 : ℝ)|^43 ≤ (34104147684891/100000000000000 : ℝ)^35
        have hw : |(1041518047/2500000000 : ℝ)|=(1041518047/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(591872047/1250000000 : ℝ)|^43 ≤ (9978028836271/25000000000000 : ℝ)^35
        have hw : |(591872047/1250000000 : ℝ)|=(591872047/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c324039_s0_16 (p : ℝ) (hpa : (21/4 : ℝ) ≤ p) (hpb : p ≤ (43/8 : ℝ)) (x : Fin 3 → ℝ) :
    (1536482969/2500000000 : ℝ)*x 0 + (-1325428417/5000000000 : ℝ)*x 1 + (-3282107871/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1536482969/2500000000 : ℝ)^43 ≤ (54987622213609/100000000000000 : ℝ)^35 := by
    have hnat : (1536482969 : ℕ)^43*100000000000000^35 ≤ 54987622213609^35*2500000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1536482969 2500000000 54987622213609 100000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1325428417/5000000000 : ℝ)^43 ≤ (9784955486293/50000000000000 : ℝ)^35 := by
    have hnat : (1325428417 : ℕ)^43*50000000000000^35 ≤ 9784955486293^35*5000000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1325428417 5000000000 9784955486293 50000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3282107871/10000000000 : ℝ)^43 ≤ (12721233400643/50000000000000 : ℝ)^35 := by
    have hnat : (3282107871 : ℕ)^43*50000000000000^35 ≤ 12721233400643^35*10000000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3282107871 10000000000 12721233400643 50000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (43/8 : ℝ)) 43 35 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1536482969/2500000000 : ℝ), (-1325428417/5000000000 : ℝ), (-3282107871/10000000000 : ℝ)] ![(54987622213609/100000000000000 : ℝ), (9784955486293/50000000000000 : ℝ), (12721233400643/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1536482969/2500000000 : ℝ)|^43 ≤ (54987622213609/100000000000000 : ℝ)^35
        have hw : |(1536482969/2500000000 : ℝ)|=(1536482969/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1325428417/5000000000 : ℝ)|^43 ≤ (9784955486293/50000000000000 : ℝ)^35
        have hw : |(-1325428417/5000000000 : ℝ)|=(1325428417/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3282107871/10000000000 : ℝ)|^43 ≤ (12721233400643/50000000000000 : ℝ)^35
        have hw : |(-3282107871/10000000000 : ℝ)|=(3282107871/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c324039_s0_20 (p : ℝ) (hpa : (21/4 : ℝ) ≤ p) (hpb : p ≤ (43/8 : ℝ)) (x : Fin 3 → ℝ) :
    (9197183891/10000000000 : ℝ)*x 0 + (-109001/5000000000 : ℝ)*x 1 + (150605567/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (9197183891/10000000000 : ℝ)^43 ≤ (90229263343393/100000000000000 : ℝ)^35 := by
    have hnat : (9197183891 : ℕ)^43*100000000000000^35 ≤ 90229263343393^35*10000000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      9197183891 10000000000 90229263343393 100000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (109001/5000000000 : ℝ)^43 ≤ (11717791/6250000000000 : ℝ)^35 := by
    have hnat : (109001 : ℕ)^43*6250000000000^35 ≤ 11717791^35*5000000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      109001 5000000000 11717791 6250000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (150605567/1000000000 : ℝ)^43 ≤ (4885274579339/50000000000000 : ℝ)^35 := by
    have hnat : (150605567 : ℕ)^43*50000000000000^35 ≤ 4885274579339^35*1000000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      150605567 1000000000 4885274579339 50000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (43/8 : ℝ)) 43 35 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(9197183891/10000000000 : ℝ), (-109001/5000000000 : ℝ), (150605567/1000000000 : ℝ)] ![(90229263343393/100000000000000 : ℝ), (11717791/6250000000000 : ℝ), (4885274579339/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(9197183891/10000000000 : ℝ)|^43 ≤ (90229263343393/100000000000000 : ℝ)^35
        have hw : |(9197183891/10000000000 : ℝ)|=(9197183891/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-109001/5000000000 : ℝ)|^43 ≤ (11717791/6250000000000 : ℝ)^35
        have hw : |(-109001/5000000000 : ℝ)|=(109001/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(150605567/1000000000 : ℝ)|^43 ≤ (4885274579339/50000000000000 : ℝ)^35
        have hw : |(150605567/1000000000 : ℝ)|=(150605567/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c324039_s0_21 (p : ℝ) (hpa : (21/4 : ℝ) ≤ p) (hpb : p ≤ (43/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-647198287/10000000000 : ℝ)*x 0 + (-198578463/250000000 : ℝ)*x 1 + (565406731/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (647198287/10000000000 : ℝ)^43 ≤ (1730790385787/50000000000000 : ℝ)^35 := by
    have hnat : (647198287 : ℕ)^43*50000000000000^35 ≤ 1730790385787^35*10000000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      647198287 10000000000 1730790385787 50000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (198578463/250000000 : ℝ)^43 ≤ (15071732991921/20000000000000 : ℝ)^35 := by
    have hnat : (198578463 : ℕ)^43*20000000000000^35 ≤ 15071732991921^35*250000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      198578463 250000000 15071732991921 20000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (565406731/2000000000 : ℝ)^43 ≤ (21179754249707/100000000000000 : ℝ)^35 := by
    have hnat : (565406731 : ℕ)^43*100000000000000^35 ≤ 21179754249707^35*2000000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      565406731 2000000000 21179754249707 100000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (43/8 : ℝ)) 43 35 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-647198287/10000000000 : ℝ), (-198578463/250000000 : ℝ), (565406731/2000000000 : ℝ)] ![(1730790385787/50000000000000 : ℝ), (15071732991921/20000000000000 : ℝ), (21179754249707/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-647198287/10000000000 : ℝ)|^43 ≤ (1730790385787/50000000000000 : ℝ)^35
        have hw : |(-647198287/10000000000 : ℝ)|=(647198287/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-198578463/250000000 : ℝ)|^43 ≤ (15071732991921/20000000000000 : ℝ)^35
        have hw : |(-198578463/250000000 : ℝ)|=(198578463/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(565406731/2000000000 : ℝ)|^43 ≤ (21179754249707/100000000000000 : ℝ)^35
        have hw : |(565406731/2000000000 : ℝ)|=(565406731/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c324039_s0_22 (p : ℝ) (hpa : (21/4 : ℝ) ≤ p) (hpb : p ≤ (43/8 : ℝ)) (x : Fin 3 → ℝ) :
    (3106833851/5000000000 : ℝ)*x 0 + (3231449533/10000000000 : ℝ)*x 1 + (2621725331/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3106833851/5000000000 : ℝ)^43 ≤ (55733111111621/100000000000000 : ℝ)^35 := by
    have hnat : (3106833851 : ℕ)^43*100000000000000^35 ≤ 55733111111621^35*5000000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3106833851 5000000000 55733111111621 100000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3231449533/10000000000 : ℝ)^43 ≤ (24960865235001/100000000000000 : ℝ)^35 := by
    have hnat : (3231449533 : ℕ)^43*100000000000000^35 ≤ 24960865235001^35*10000000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3231449533 10000000000 24960865235001 100000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2621725331/10000000000 : ℝ)^43 ≤ (19306023642613/100000000000000 : ℝ)^35 := by
    have hnat : (2621725331 : ℕ)^43*100000000000000^35 ≤ 19306023642613^35*10000000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2621725331 10000000000 19306023642613 100000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (43/8 : ℝ)) 43 35 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3106833851/5000000000 : ℝ), (3231449533/10000000000 : ℝ), (2621725331/10000000000 : ℝ)] ![(55733111111621/100000000000000 : ℝ), (24960865235001/100000000000000 : ℝ), (19306023642613/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3106833851/5000000000 : ℝ)|^43 ≤ (55733111111621/100000000000000 : ℝ)^35
        have hw : |(3106833851/5000000000 : ℝ)|=(3106833851/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3231449533/10000000000 : ℝ)|^43 ≤ (24960865235001/100000000000000 : ℝ)^35
        have hw : |(3231449533/10000000000 : ℝ)|=(3231449533/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2621725331/10000000000 : ℝ)|^43 ≤ (19306023642613/100000000000000 : ℝ)^35
        have hw : |(2621725331/10000000000 : ℝ)|=(2621725331/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c324039_s0_23 (p : ℝ) (hpa : (21/4 : ℝ) ≤ p) (hpb : p ≤ (43/8 : ℝ)) (x : Fin 3 → ℝ) :
    (2374105557/10000000000 : ℝ)*x 0 + (-5976412431/10000000000 : ℝ)*x 1 + (-1865348653/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2374105557/10000000000 : ℝ)^43 ≤ (8545297309459/50000000000000 : ℝ)^35 := by
    have hnat : (2374105557 : ℕ)^43*50000000000000^35 ≤ 8545297309459^35*10000000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2374105557 10000000000 8545297309459 50000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5976412431/10000000000 : ℝ)^43 ≤ (53130176657477/100000000000000 : ℝ)^35 := by
    have hnat : (5976412431 : ℕ)^43*100000000000000^35 ≤ 53130176657477^35*10000000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5976412431 10000000000 53130176657477 100000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1865348653/5000000000 : ℝ)^43 ≤ (29779228708871/100000000000000 : ℝ)^35 := by
    have hnat : (1865348653 : ℕ)^43*100000000000000^35 ≤ 29779228708871^35*5000000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1865348653 5000000000 29779228708871 100000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (43/8 : ℝ)) 43 35 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2374105557/10000000000 : ℝ), (-5976412431/10000000000 : ℝ), (-1865348653/5000000000 : ℝ)] ![(8545297309459/50000000000000 : ℝ), (53130176657477/100000000000000 : ℝ), (29779228708871/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2374105557/10000000000 : ℝ)|^43 ≤ (8545297309459/50000000000000 : ℝ)^35
        have hw : |(2374105557/10000000000 : ℝ)|=(2374105557/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-5976412431/10000000000 : ℝ)|^43 ≤ (53130176657477/100000000000000 : ℝ)^35
        have hw : |(-5976412431/10000000000 : ℝ)|=(5976412431/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1865348653/5000000000 : ℝ)|^43 ≤ (29779228708871/100000000000000 : ℝ)^35
        have hw : |(-1865348653/5000000000 : ℝ)|=(1865348653/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c324039_s0_27 (p : ℝ) (hpa : (21/4 : ℝ) ≤ p) (hpb : p ≤ (43/8 : ℝ)) (x : Fin 3 → ℝ) :
    (8519740229/10000000000 : ℝ)*x 0 + (657/2500000000 : ℝ)*x 1 + (76918699/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (8519740229/10000000000 : ℝ)^43 ≤ (5133384827013/6250000000000 : ℝ)^35 := by
    have hnat : (8519740229 : ℕ)^43*6250000000000^35 ≤ 5133384827013^35*10000000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8519740229 10000000000 5133384827013 6250000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (657/2500000000 : ℝ)^43 ≤ (411633/50000000000000 : ℝ)^35 := by
    have hnat : (657 : ℕ)^43*50000000000000^35 ≤ 411633^35*2500000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      657 2500000000 411633 50000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (76918699/312500000 : ℝ)^43 ≤ (17865841936089/100000000000000 : ℝ)^35 := by
    have hnat : (76918699 : ℕ)^43*100000000000000^35 ≤ 17865841936089^35*312500000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      76918699 312500000 17865841936089 100000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (43/8 : ℝ)) 43 35 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(8519740229/10000000000 : ℝ), (657/2500000000 : ℝ), (76918699/312500000 : ℝ)] ![(5133384827013/6250000000000 : ℝ), (411633/50000000000000 : ℝ), (17865841936089/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(8519740229/10000000000 : ℝ)|^43 ≤ (5133384827013/6250000000000 : ℝ)^35
        have hw : |(8519740229/10000000000 : ℝ)|=(8519740229/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(657/2500000000 : ℝ)|^43 ≤ (411633/50000000000000 : ℝ)^35
        have hw : |(657/2500000000 : ℝ)|=(657/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(76918699/312500000 : ℝ)|^43 ≤ (17865841936089/100000000000000 : ℝ)^35
        have hw : |(76918699/312500000 : ℝ)|=(76918699/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c324039_s1_0 (p : ℝ) (hpa : (21/4 : ℝ) ≤ p) (hpb : p ≤ (43/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-2113068341/10000000000 : ℝ)*x 0 + (-1289490253/2500000000 : ℝ)*x 1 + (2412767157/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2113068341/10000000000 : ℝ)^43 ≤ (14811807782417/100000000000000 : ℝ)^35 := by
    have hnat : (2113068341 : ℕ)^43*100000000000000^35 ≤ 14811807782417^35*10000000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2113068341 10000000000 14811807782417 100000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1289490253/2500000000 : ℝ)^43 ≤ (8867245835981/20000000000000 : ℝ)^35 := by
    have hnat : (1289490253 : ℕ)^43*20000000000000^35 ≤ 8867245835981^35*2500000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1289490253 2500000000 8867245835981 20000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2412767157/5000000000 : ℝ)^43 ≤ (10212990754389/25000000000000 : ℝ)^35 := by
    have hnat : (2412767157 : ℕ)^43*25000000000000^35 ≤ 10212990754389^35*5000000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2412767157 5000000000 10212990754389 25000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (43/8 : ℝ)) 43 35 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2113068341/10000000000 : ℝ), (-1289490253/2500000000 : ℝ), (2412767157/5000000000 : ℝ)] ![(14811807782417/100000000000000 : ℝ), (8867245835981/20000000000000 : ℝ), (10212990754389/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2113068341/10000000000 : ℝ)|^43 ≤ (14811807782417/100000000000000 : ℝ)^35
        have hw : |(-2113068341/10000000000 : ℝ)|=(2113068341/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1289490253/2500000000 : ℝ)|^43 ≤ (8867245835981/20000000000000 : ℝ)^35
        have hw : |(-1289490253/2500000000 : ℝ)|=(1289490253/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2412767157/5000000000 : ℝ)|^43 ≤ (10212990754389/25000000000000 : ℝ)^35
        have hw : |(2412767157/5000000000 : ℝ)|=(2412767157/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c324039_s1_1 (p : ℝ) (hpa : (21/4 : ℝ) ≤ p) (hpb : p ≤ (43/8 : ℝ)) (x : Fin 3 → ℝ) :
    (579303789/1250000000 : ℝ)*x 0 + (1877753283/5000000000 : ℝ)*x 1 + (3865223499/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (579303789/1250000000 : ℝ)^43 ≤ (38873412427301/100000000000000 : ℝ)^35 := by
    have hnat : (579303789 : ℕ)^43*100000000000000^35 ≤ 38873412427301^35*1250000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      579303789 1250000000 38873412427301 100000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1877753283/5000000000 : ℝ)^43 ≤ (30022710804571/100000000000000 : ℝ)^35 := by
    have hnat : (1877753283 : ℕ)^43*100000000000000^35 ≤ 30022710804571^35*5000000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1877753283 5000000000 30022710804571 100000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3865223499/10000000000 : ℝ)^43 ≤ (31103876749943/100000000000000 : ℝ)^35 := by
    have hnat : (3865223499 : ℕ)^43*100000000000000^35 ≤ 31103876749943^35*10000000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3865223499 10000000000 31103876749943 100000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (43/8 : ℝ)) 43 35 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(579303789/1250000000 : ℝ), (1877753283/5000000000 : ℝ), (3865223499/10000000000 : ℝ)] ![(38873412427301/100000000000000 : ℝ), (30022710804571/100000000000000 : ℝ), (31103876749943/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(579303789/1250000000 : ℝ)|^43 ≤ (38873412427301/100000000000000 : ℝ)^35
        have hw : |(579303789/1250000000 : ℝ)|=(579303789/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1877753283/5000000000 : ℝ)|^43 ≤ (30022710804571/100000000000000 : ℝ)^35
        have hw : |(1877753283/5000000000 : ℝ)|=(1877753283/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3865223499/10000000000 : ℝ)|^43 ≤ (31103876749943/100000000000000 : ℝ)^35
        have hw : |(3865223499/10000000000 : ℝ)|=(3865223499/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c324039_s1_2 (p : ℝ) (hpa : (21/4 : ℝ) ≤ p) (hpb : p ≤ (43/8 : ℝ)) (x : Fin 3 → ℝ) :
    (27937117/62500000 : ℝ)*x 0 + (-383846947/1000000000 : ℝ)*x 1 + (-1976563889/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (27937117/62500000 : ℝ)^43 ≤ (37185232340949/100000000000000 : ℝ)^35 := by
    have hnat : (27937117 : ℕ)^43*100000000000000^35 ≤ 37185232340949^35*62500000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      27937117 62500000 37185232340949 100000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (383846947/1000000000 : ℝ)^43 ≤ (6167916804189/20000000000000 : ℝ)^35 := by
    have hnat : (383846947 : ℕ)^43*20000000000000^35 ≤ 6167916804189^35*1000000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      383846947 1000000000 6167916804189 20000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1976563889/5000000000 : ℝ)^43 ≤ (15987591813273/50000000000000 : ℝ)^35 := by
    have hnat : (1976563889 : ℕ)^43*50000000000000^35 ≤ 15987591813273^35*5000000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1976563889 5000000000 15987591813273 50000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (43/8 : ℝ)) 43 35 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(27937117/62500000 : ℝ), (-383846947/1000000000 : ℝ), (-1976563889/5000000000 : ℝ)] ![(37185232340949/100000000000000 : ℝ), (6167916804189/20000000000000 : ℝ), (15987591813273/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(27937117/62500000 : ℝ)|^43 ≤ (37185232340949/100000000000000 : ℝ)^35
        have hw : |(27937117/62500000 : ℝ)|=(27937117/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-383846947/1000000000 : ℝ)|^43 ≤ (6167916804189/20000000000000 : ℝ)^35
        have hw : |(-383846947/1000000000 : ℝ)|=(383846947/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1976563889/5000000000 : ℝ)|^43 ≤ (15987591813273/50000000000000 : ℝ)^35
        have hw : |(-1976563889/5000000000 : ℝ)|=(1976563889/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c324039_s1_6 (p : ℝ) (hpa : (21/4 : ℝ) ≤ p) (hpb : p ≤ (43/8 : ℝ)) (x : Fin 3 → ℝ) :
    (6861774631/10000000000 : ℝ)*x 0 + (-118777497/500000000 : ℝ)*x 1 + (1345722963/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6861774631/10000000000 : ℝ)^43 ≤ (15739484502527/25000000000000 : ℝ)^35 := by
    have hnat : (6861774631 : ℕ)^43*25000000000000^35 ≤ 15739484502527^35*10000000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6861774631 10000000000 15739484502527 25000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (118777497/500000000 : ℝ)^43 ≤ (17103369889839/100000000000000 : ℝ)^35 := by
    have hnat : (118777497 : ℕ)^43*100000000000000^35 ≤ 17103369889839^35*500000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      118777497 500000000 17103369889839 100000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1345722963/5000000000 : ℝ)^43 ≤ (19938692083209/100000000000000 : ℝ)^35 := by
    have hnat : (1345722963 : ℕ)^43*100000000000000^35 ≤ 19938692083209^35*5000000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1345722963 5000000000 19938692083209 100000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (43/8 : ℝ)) 43 35 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6861774631/10000000000 : ℝ), (-118777497/500000000 : ℝ), (1345722963/5000000000 : ℝ)] ![(15739484502527/25000000000000 : ℝ), (17103369889839/100000000000000 : ℝ), (19938692083209/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6861774631/10000000000 : ℝ)|^43 ≤ (15739484502527/25000000000000 : ℝ)^35
        have hw : |(6861774631/10000000000 : ℝ)|=(6861774631/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-118777497/500000000 : ℝ)|^43 ≤ (17103369889839/100000000000000 : ℝ)^35
        have hw : |(-118777497/500000000 : ℝ)|=(118777497/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1345722963/5000000000 : ℝ)|^43 ≤ (19938692083209/100000000000000 : ℝ)^35
        have hw : |(1345722963/5000000000 : ℝ)|=(1345722963/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c324039 (p : ℝ) (hpa : (21/4 : ℝ) ≤ p) (hpb : p ≤ (43/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (49571/25000 : ℝ) (83049/50000 : ℝ) (81117/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, false], ![true, true, true]]) : False := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (81117/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (81117/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (81117/100000 : ℝ)*P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (81117/100000 : ℝ)*P 1 ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 2+X 2 2)) ∧ ((-1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 2) ∧ ((-1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (81117/100000 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (81117/100000 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base3 : ((1 : ℝ)*N 1+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 1]
  have base7 : ((1 : ℝ)*T) ≤ (83049/50000 : ℝ) := by
    linarith only [f.Tcap]
  have base13 : ((1 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 2).2]
  have base21 : ((1 : ℝ)*X 2 0+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 0).2]
  have base24 : ((-1 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 2).1]
  have base27 : ((1 : ℝ)*X 0 0+(1 : ℝ)*X 1 0+(1 : ℝ)*X 2 0+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [(f.column 0).2]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base43 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 2+(1 : ℝ)*P 1) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 1,f.sum]
  have base49 : ((1 : ℝ)*X 0 2+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.1]
  have base53 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 1+(1 : ℝ)*P 2) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 2,f.sum]
  have base59 : ((-1 : ℝ)*X 0 1+(-1 : ℝ)*X 1 1) ≤ (0 : ℝ) := by
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
  have s0_pow0 : (1 : ℝ) ^ (21/4 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^21 ≤ (1 : ℝ)^4 := by
      have hnat : (1 : ℕ)^21*1^4 ≤ 1^4*1^21 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 21 4 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 21 4 (by norm_num) hpowers
    exact h
  have s0_corner0a : (2 : ℝ) ≤ (1141140309994013/1000000000000000 : ℝ) ^ (21/4 : ℝ) := by
    have hpowers : (2 : ℝ)^4 ≤ (1141140309994013/1000000000000000 : ℝ)^21 := by
      have hnat : (2 : ℕ)^4*1000000000000000^21 ≤ 1141140309994013^21*1^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 1141140309994013 1000000000000000 4 21 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1141140309994013/1000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 21 4 (by norm_num) hpowers
    exact h
  have s0_corner0b : (3 : ℝ) ≤ (12327648392357461/10000000000000000 : ℝ) ^ (21/4 : ℝ) := by
    have hpowers : (3 : ℝ)^4 ≤ (12327648392357461/10000000000000000 : ℝ)^21 := by
      have hnat : (3 : ℕ)^4*10000000000000000^21 ≤ 12327648392357461^21*1^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 12327648392357461 10000000000000000 4 21 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12327648392357461/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 21 4 (by norm_num) hpowers
    exact h
  have major_s0_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(141140309994013/1000000000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(916245292417331/10000000000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (21/4 : ℝ)) (rho := (1 : ℝ)) (alpha := (141140309994013/1000000000000000 : ℝ)) (beta := (916245292417331/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow0,s0_corner0a]) (by linarith only [s0_pow0,s0_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, false], ![true, true, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (1 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order0.2.2])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(141140309994013/1000000000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(916245292417331/10000000000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow1 : (1 : ℝ) ^ (21/4 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^21 ≤ (1 : ℝ)^4 := by
      have hnat : (1 : ℕ)^21*1^4 ≤ 1^4*1^21 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 21 4 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 21 4 (by norm_num) hpowers
    exact h
  have s0_corner1a : (2 : ℝ) ≤ (1141140309994013/1000000000000000 : ℝ) ^ (21/4 : ℝ) := by
    have hpowers : (2 : ℝ)^4 ≤ (1141140309994013/1000000000000000 : ℝ)^21 := by
      have hnat : (2 : ℕ)^4*1000000000000000^21 ≤ 1141140309994013^21*1^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 1141140309994013 1000000000000000 4 21 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1141140309994013/1000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 21 4 (by norm_num) hpowers
    exact h
  have s0_corner1b : (3 : ℝ) ≤ (12327648392357461/10000000000000000 : ℝ) ^ (21/4 : ℝ) := by
    have hpowers : (3 : ℝ)^4 ≤ (12327648392357461/10000000000000000 : ℝ)^21 := by
      have hnat : (3 : ℕ)^4*10000000000000000^21 ≤ 12327648392357461^21*1^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 12327648392357461 10000000000000000 4 21 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12327648392357461/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 21 4 (by norm_num) hpowers
    exact h
  have major_s0_1 : P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1))+(141140309994013/1000000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(916245292417331/10000000000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (21/4 : ℝ)) (rho := (1 : ℝ)) (alpha := (141140309994013/1000000000000000 : ℝ)) (beta := (916245292417331/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow1,s0_corner1a]) (by linarith only [s0_pow1,s0_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, false], ![true, true, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (1 : ℝ)*((-1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order1.2.2])
    change lpNorm p (pair X 1) ≤ ((-1 : ℝ)*pair X 1 1)+(141140309994013/1000000000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(916245292417331/10000000000000000 : ℝ)*((-1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow2 : (1 : ℝ) ^ (21/4 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^21 ≤ (1 : ℝ)^4 := by
      have hnat : (1 : ℕ)^21*1^4 ≤ 1^4*1^21 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 21 4 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 21 4 (by norm_num) hpowers
    exact h
  have s0_corner2a : (2 : ℝ) ≤ (1141140309994013/1000000000000000 : ℝ) ^ (21/4 : ℝ) := by
    have hpowers : (2 : ℝ)^4 ≤ (1141140309994013/1000000000000000 : ℝ)^21 := by
      have hnat : (2 : ℕ)^4*1000000000000000^21 ≤ 1141140309994013^21*1^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 1141140309994013 1000000000000000 4 21 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1141140309994013/1000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 21 4 (by norm_num) hpowers
    exact h
  have s0_corner2b : (3 : ℝ) ≤ (12327648392357461/10000000000000000 : ℝ) ^ (21/4 : ℝ) := by
    have hpowers : (3 : ℝ)^4 ≤ (12327648392357461/10000000000000000 : ℝ)^21 := by
      have hnat : (3 : ℕ)^4*10000000000000000^21 ≤ 12327648392357461^21*1^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 12327648392357461 10000000000000000 4 21 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12327648392357461/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 21 4 (by norm_num) hpowers
    exact h
  have major_s0_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(141140309994013/1000000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(916245292417331/10000000000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (21/4 : ℝ)) (rho := (1 : ℝ)) (alpha := (141140309994013/1000000000000000 : ℝ)) (beta := (916245292417331/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow2,s0_corner2a]) (by linarith only [s0_pow2,s0_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, false], ![true, true, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (1 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order2.2.2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(141140309994013/1000000000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(916245292417331/10000000000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s0_0 : ((-57532233/500000000 : ℝ)*X 0 0+(-6192254501/10000000000 : ℝ)*X 0 1+(2249544041/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c324039_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_1 : ((4703900879/10000000000 : ℝ)*X 1 0+(3742487901/10000000000 : ℝ)*X 1 1+(3805509077/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c324039_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_2 : ((1175974999/2500000000 : ℝ)*X 2 0+(-3698735101/10000000000 : ℝ)*X 2 1+(-6014033/15625000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c324039_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_7 : ((-235097687/10000000000 : ℝ)*X 0 0+(-3951419171/5000000000 : ℝ)*X 0 1+(1570919303/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c324039_s0_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_8 : ((3053113727/10000000000 : ℝ)*X 1 0+(2188582101/5000000000 : ℝ)*X 1 1+(4789875971/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c324039_s0_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_9 : ((2399801547/5000000000 : ℝ)*X 2 0+(-1307488449/5000000000 : ℝ)*X 2 1+(-4760113367/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c324039_s0_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_13 : ((6554795627/10000000000 : ℝ)*X 0 0+(53977/250000000 : ℝ)*X 0 1+(4789875971/10000000000 : ℝ)*X 0 2+(6554795627/10000000000 : ℝ)*X 1 0+(53977/250000000 : ℝ)*X 1 1+(4789875971/10000000000 : ℝ)*X 1 2+(6554795627/10000000000 : ℝ)*X 2 0+(53977/250000000 : ℝ)*X 2 1+(4789875971/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c324039_s0_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_14 : ((-80843051/5000000000 : ℝ)*X 0 0+(-2735498029/5000000000 : ℝ)*X 0 1+(1169129829/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c324039_s0_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_15 : ((3338830211/10000000000 : ℝ)*X 1 0+(1041518047/2500000000 : ℝ)*X 1 1+(591872047/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c324039_s0_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_16 : ((1536482969/2500000000 : ℝ)*X 2 0+(-1325428417/5000000000 : ℝ)*X 2 1+(-3282107871/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c324039_s0_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_20 : ((9197183891/10000000000 : ℝ)*X 0 0+(-109001/5000000000 : ℝ)*X 0 1+(150605567/1000000000 : ℝ)*X 0 2+(9197183891/10000000000 : ℝ)*X 1 0+(-109001/5000000000 : ℝ)*X 1 1+(150605567/1000000000 : ℝ)*X 1 2+(9197183891/10000000000 : ℝ)*X 2 0+(-109001/5000000000 : ℝ)*X 2 1+(150605567/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c324039_s0_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_21 : ((-647198287/10000000000 : ℝ)*X 0 0+(-198578463/250000000 : ℝ)*X 0 1+(565406731/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c324039_s0_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_22 : ((3106833851/5000000000 : ℝ)*X 1 0+(3231449533/10000000000 : ℝ)*X 1 1+(2621725331/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c324039_s0_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_23 : ((2374105557/10000000000 : ℝ)*X 2 0+(-5976412431/10000000000 : ℝ)*X 2 1+(-1865348653/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c324039_s0_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_27 : ((8519740229/10000000000 : ℝ)*X 0 0+(657/2500000000 : ℝ)*X 0 1+(76918699/312500000 : ℝ)*X 0 2+(8519740229/10000000000 : ℝ)*X 1 0+(657/2500000000 : ℝ)*X 1 1+(76918699/312500000 : ℝ)*X 1 2+(8519740229/10000000000 : ℝ)*X 2 0+(657/2500000000 : ℝ)*X 2 1+(76918699/312500000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c324039_s0_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s0_0 : (0 : ℝ) ≤ ((12541/25000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(12541/25000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (6014975761800430019277/1250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (294431039599/250000000000 : ℝ)*(base3) + (111960851549/100000000000 : ℝ)*(base7) + (432981/200000000000 : ℝ)*(base40) + (287612298603/500000000000 : ℝ)*(base49) + (1790984229693/1000000000000 : ℝ)*(major_s0_0) + (1790984229693/1000000000000 : ℝ)*(major_s0_1) + (1790984229693/1000000000000 : ℝ)*(major_s0_2) + (205883707841/100000000000 : ℝ)*(sp_s0_7) + (3236542546563/1000000000000 : ℝ)*(sp_s0_8) + (257354597399/125000000000 : ℝ)*(sp_s0_9) + (422563143853/500000000000 : ℝ)*(sp_s0_13) + (2697841/500000000000 : ℝ)*(sp_s0_14) + (963437/40000000000 : ℝ)*(sp_s0_15) + (56949/10000000000 : ℝ)*(sp_s0_23) + (903241930611/1000000000000 : ℝ)*(f.failure) + (514710618523/250000000000 : ℝ)*(f.sum) + (102088374571991/500000000000000000000000000 : ℝ)*base62 + (608557785990617/10000000000000000000000000000 : ℝ)*base64 + (49704205990617/10000000000000000000000000000 : ℝ)*base67 + (52848966971991/1000000000000000000000000000 : ℝ)*base68 + (529644719710527/10000000000000000000000000000 : ℝ)*base70 + (642463080990617/10000000000000000000000000000 : ℝ)*base72 + (10121854171991/1000000000000000000000000000 : ℝ)*base74 + (171383969571991/1000000000000000000000000000 : ℝ)*base76 + (1123756831/5000000000000000000000 : ℝ)*base78 + (7119/25000000000000000 : ℝ)*base86 + (7119/25000000000000000 : ℝ)*base88 + (7119/25000000000000000 : ℝ)*base90 + (1/1000000000000 : ℝ)*base93 + hcertificate_margin
  have ratio_s0_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-8551/20000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(-8551/20000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (35901322304240468492571/5000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (633450054601/1000000000000 : ℝ)*(base7) + (295757/100000000000 : ℝ)*(base13) + (875092348211/1000000000000 : ℝ)*(base40) + (9650753/1000000000000 : ℝ)*(base53) + (2616287801283/1000000000000 : ℝ)*(major_s0_0) + (2616287801283/1000000000000 : ℝ)*(major_s0_1) + (261627815053/100000000000 : ℝ)*(major_s0_2) + (11875169/250000000000 : ℝ)*(sp_s0_0) + (1472149/125000000000 : ℝ)*(sp_s0_1) + (712466446669/200000000000 : ℝ)*(sp_s0_14) + (3562370914399/1000000000000 : ℝ)*(sp_s0_15) + (445299042793/125000000000 : ℝ)*(sp_s0_16) + (488219893569/250000000000 : ℝ)*(sp_s0_20) + (3538989/100000000000 : ℝ)*(sp_s0_27) + (659732454783/500000000000 : ℝ)*(f.failure) + (445299042793/125000000000 : ℝ)*(f.sum) + (404028538895569/1000000000000000000000000000 : ℝ)*base63 + (102683608316457/1000000000000000000000000000 : ℝ)*base64 + (1902241930235673/10000000000000000000000000000 : ℝ)*base66 + (30969374447689/100000000000000000000000000 : ℝ)*base69 + (130844756798889/500000000000000000000000000 : ℝ)*base70 + (1551859785235673/10000000000000000000000000000 : ℝ)*base73 + (238079656718679/1000000000000000000000000000 : ℝ)*base75 + (182030883481321/1000000000000000000000000000 : ℝ)*base76 + (135104537/312500000000000000000 : ℝ)*base79 + (10593/12500000000000000 : ℝ)*base87 + (10593/12500000000000000 : ℝ)*base89 + (10593/12500000000000000 : ℝ)*base91 + (1/1000000000000 : ℝ)*base92 + hcertificate_margin
  have ratio_s0_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(8129/12500 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(8129/12500 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (12966609750227678417613/1000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (232790380873/1000000000000 : ℝ)*(base3) + (1238745934579/1000000000000 : ℝ)*(base7) + (85419953909/250000000000 : ℝ)*(base40) + (2359661/250000000000 : ℝ)*(base43) + (5932981/1000000000000 : ℝ)*(base49) + (19480116813/10000000000 : ℝ)*(major_s0_0) + (389600448531/200000000000 : ℝ)*(major_s0_1) + (19480116813/10000000000 : ℝ)*(major_s0_2) + (7873227/500000000000 : ℝ)*(sp_s0_2) + (21142121/250000000000 : ℝ)*(sp_s0_20) + (445546078701/200000000000 : ℝ)*(sp_s0_21) + (1230265106511/500000000000 : ℝ)*(sp_s0_22) + (2227714647051/1000000000000 : ℝ)*(sp_s0_23) + (994153059661/500000000000 : ℝ)*(sp_s0_27) + (9824351341/10000000000 : ℝ)*(f.failure) + (2227739832149/1000000000000 : ℝ)*(f.sum) + (20402736516283/200000000000000000000000000 : ℝ)*base63 + (70354859206103/100000000000000000000000000 : ℝ)*base65 + (1101792851909239/2000000000000000000000000000 : ℝ)*base67 + (3174659214569/10000000000000000000000000 : ℝ)*base69 + (32156747648207/100000000000000000000000000 : ℝ)*base70 + (60760715106103/100000000000000000000000000 : ℝ)*base73 + (27265273184903/200000000000000000000000000 : ℝ)*base75 + (2521614227569/10000000000000000000000000 : ℝ)*base77 + (1938394137831299/2000000000000000000000000000 : ℝ)*base79 + (289/250000000000000 : ℝ)*base86 + (39/250000000000000 : ℝ)*base88 + (289/250000000000000 : ℝ)*base90 + hcertificate_margin
  have s1_pow0 : (12541/25000 : ℝ) ^ (21/4 : ℝ) ≤ (534673711288469981/20000000000000000000 : ℝ) := by
    have hpowers : (12541/25000 : ℝ)^21 ≤ (534673711288469981/20000000000000000000 : ℝ)^4 := by
      have hnat : (12541 : ℕ)^21*20000000000000000000^4 ≤ 534673711288469981^4*25000^21 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12541 25000 534673711288469981 20000000000000000000 21 4 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (12541/25000 : ℝ)) (X := (534673711288469981/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 21 4 (by norm_num) hpowers
    exact h
  have s1_corner0a : (20534673711288469981/20000000000000000000 : ℝ) ≤ (10050379019257463/10000000000000000 : ℝ) ^ (21/4 : ℝ) := by
    have hpowers : (20534673711288469981/20000000000000000000 : ℝ)^4 ≤ (10050379019257463/10000000000000000 : ℝ)^21 := by
      have hnat : (20534673711288469981 : ℕ)^4*10000000000000000^21 ≤ 10050379019257463^21*20000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20534673711288469981 20000000000000000000 10050379019257463 10000000000000000 4 21 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10050379019257463/10000000000000000 : ℝ)) (X := (20534673711288469981/20000000000000000000 : ℝ)) (by norm_num) 21 4 (by norm_num) hpowers
    exact h
  have s1_corner0b : (10534673711288469981/10000000000000000000 : ℝ) ≤ (5049853547244421/5000000000000000 : ℝ) ^ (21/4 : ℝ) := by
    have hpowers : (10534673711288469981/10000000000000000000 : ℝ)^4 ≤ (5049853547244421/5000000000000000 : ℝ)^21 := by
      have hnat : (10534673711288469981 : ℕ)^4*5000000000000000^21 ≤ 5049853547244421^21*10000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10534673711288469981 10000000000000000000 5049853547244421 5000000000000000 4 21 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5049853547244421/5000000000000000 : ℝ)) (X := (10534673711288469981/10000000000000000000 : ℝ)) (by norm_num) 21 4 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(50379019257463/5016400000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(49328075231379/5016400000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (21/4 : ℝ)) (rho := (12541/25000 : ℝ)) (alpha := (50379019257463/5016400000000000 : ℝ)) (beta := (49328075231379/5016400000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, false], ![true, true, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (12541/25000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(50379019257463/5016400000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(49328075231379/5016400000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (8551/20000 : ℝ) ^ (21/4 : ℝ) ≤ (115526410999075583/10000000000000000000 : ℝ) := by
    have hpowers : (8551/20000 : ℝ)^21 ≤ (115526410999075583/10000000000000000000 : ℝ)^4 := by
      have hnat : (8551 : ℕ)^21*10000000000000000000^4 ≤ 115526410999075583^4*20000^21 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8551 20000 115526410999075583 10000000000000000000 21 4 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (8551/20000 : ℝ)) (X := (115526410999075583/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 21 4 (by norm_num) hpowers
    exact h
  have s1_corner1a : (10115526410999075583/10000000000000000000 : ℝ) ≤ (2004380568974067/2000000000000000 : ℝ) ^ (21/4 : ℝ) := by
    have hpowers : (10115526410999075583/10000000000000000000 : ℝ)^4 ≤ (2004380568974067/2000000000000000 : ℝ)^21 := by
      have hnat : (10115526410999075583 : ℕ)^4*2000000000000000^21 ≤ 2004380568974067^21*10000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10115526410999075583 10000000000000000000 2004380568974067 2000000000000000 4 21 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2004380568974067/2000000000000000 : ℝ)) (X := (10115526410999075583/10000000000000000000 : ℝ)) (by norm_num) 21 4 (by norm_num) hpowers
    exact h
  have s1_corner1b : (5115526410999075583/5000000000000000000 : ℝ) ≤ (10043604117790409/10000000000000000 : ℝ) ^ (21/4 : ℝ) := by
    have hpowers : (5115526410999075583/5000000000000000000 : ℝ)^4 ≤ (10043604117790409/10000000000000000 : ℝ)^21 := by
      have hnat : (5115526410999075583 : ℕ)^4*10000000000000000^21 ≤ 10043604117790409^21*5000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5115526410999075583 5000000000000000000 10043604117790409 10000000000000000 4 21 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10043604117790409/10000000000000000 : ℝ)) (X := (5115526410999075583/5000000000000000000 : ℝ)) (by norm_num) 21 4 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1))+(4380568974067/855100000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(10850636460037/2137750000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (21/4 : ℝ)) (rho := (8551/20000 : ℝ)) (alpha := (4380568974067/855100000000000 : ℝ)) (beta := (10850636460037/2137750000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, false], ![true, true, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (8551/20000 : ℝ)*((-1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((-1 : ℝ)*pair X 1 1)+(4380568974067/855100000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(10850636460037/2137750000000000 : ℝ)*((-1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (8129/12500 : ℝ) ^ (21/4 : ℝ) ≤ (10445213716020619689/100000000000000000000 : ℝ) := by
    have hpowers : (8129/12500 : ℝ)^21 ≤ (10445213716020619689/100000000000000000000 : ℝ)^4 := by
      have hnat : (8129 : ℕ)^21*100000000000000000000^4 ≤ 10445213716020619689^4*12500^21 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8129 12500 10445213716020619689 100000000000000000000 21 4 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (8129/12500 : ℝ)) (X := (10445213716020619689/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 21 4 (by norm_num) hpowers
    exact h
  have s1_corner2a : (110445213716020619689/100000000000000000000 : ℝ) ≤ (5095519424148947/5000000000000000 : ℝ) ^ (21/4 : ℝ) := by
    have hpowers : (110445213716020619689/100000000000000000000 : ℝ)^4 ≤ (5095519424148947/5000000000000000 : ℝ)^21 := by
      have hnat : (110445213716020619689 : ℕ)^4*5000000000000000^21 ≤ 5095519424148947^21*100000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        110445213716020619689 100000000000000000000 5095519424148947 5000000000000000 4 21 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5095519424148947/5000000000000000 : ℝ)) (X := (110445213716020619689/100000000000000000000 : ℝ)) (by norm_num) 21 4 (by norm_num) hpowers
    exact h
  have s1_corner2b : (60445213716020619689/50000000000000000000 : ℝ) ≤ (10367969184763421/10000000000000000 : ℝ) ^ (21/4 : ℝ) := by
    have hpowers : (60445213716020619689/50000000000000000000 : ℝ)^4 ≤ (10367969184763421/10000000000000000 : ℝ)^21 := by
      have hnat : (60445213716020619689 : ℕ)^4*10000000000000000^21 ≤ 10367969184763421^21*50000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        60445213716020619689 50000000000000000000 10367969184763421 10000000000000000 4 21 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10367969184763421/10000000000000000 : ℝ)) (X := (60445213716020619689/50000000000000000000 : ℝ)) (by norm_num) 21 4 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(95519424148947/3251600000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(176930336465527/6503200000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (21/4 : ℝ)) (rho := (8129/12500 : ℝ)) (alpha := (95519424148947/3251600000000000 : ℝ)) (beta := (176930336465527/6503200000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, false], ![true, true, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (8129/12500 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(95519424148947/3251600000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(176930336465527/6503200000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-2113068341/10000000000 : ℝ)*X 0 0+(-1289490253/2500000000 : ℝ)*X 0 1+(2412767157/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c324039_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_1 : ((579303789/1250000000 : ℝ)*X 1 0+(1877753283/5000000000 : ℝ)*X 1 1+(3865223499/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c324039_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((27937117/62500000 : ℝ)*X 2 0+(-383846947/1000000000 : ℝ)*X 2 1+(-1976563889/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c324039_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_6 : ((6861774631/10000000000 : ℝ)*X 0 0+(-118777497/500000000 : ℝ)*X 0 1+(1345722963/5000000000 : ℝ)*X 0 2+(6861774631/10000000000 : ℝ)*X 1 0+(-118777497/500000000 : ℝ)*X 1 1+(1345722963/5000000000 : ℝ)*X 1 2+(6861774631/10000000000 : ℝ)*X 2 0+(-118777497/500000000 : ℝ)*X 2 1+(1345722963/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c324039_s1_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have hsep : (-111213/12500 : ℝ) < ((-49571/25000 : ℝ)*P 0+(-49571/25000 : ℝ)*P 1+(-49571/25000 : ℝ)*P 2+(1 : ℝ)*T) := by
    have hcertificate_margin : (-111213/12500 : ℝ) < (-61166235572541487212442095540320811/6973907533912000000000000000000000 : ℝ) := by norm_num
    linear_combination (33623/1000000000000 : ℝ)*(base13) + (31873/500000000000 : ℝ)*(base21) + (14963/1000000000000 : ℝ)*(base24) + (46431/1000000000000 : ℝ)*(base27) + (603166127059/1000000000000 : ℝ)*(base40) + (292849655113/1000000000000 : ℝ)*(base49) + (657/100000000000 : ℝ)*(base53) + (183369745367/1000000000000 : ℝ)*(base59) + (49571/25000 : ℝ)*(major_s1_0) + (49571/25000 : ℝ)*(major_s1_1) + (198283999343/100000000000 : ℝ)*(major_s1_2) + (730893864429/250000000000 : ℝ)*(sp_s1_0) + (2923575491339/1000000000000 : ℝ)*(sp_s1_1) + (1827234637/625000000 : ℝ)*(sp_s1_2) + (999999953569/1000000000000 : ℝ)*(sp_s1_6) + (2923575497909/1000000000000 : ℝ)*(f.sum) + (122161687302772343/2780443160000000000000000000000 : ℝ)*base63 + (1761594189151/26012800000000000000000000 : ℝ)*base64 + (11312828707809/42755000000000000000000000 : ℝ)*base66 + (20196086398591/325160000000000000000000000 : ℝ)*base68 + (4542994712109868667/8155663120000000000000000000000 : ℝ)*base70 + (4428645685049/25082000000000000000000000 : ℝ)*base73 + (15290075534511/85510000000000000000000000 : ℝ)*base75 + (1835621689787/6270500000000000000000000 : ℝ)*base76 + (584248675416824623/536190455000000000000000000000 : ℝ)*base79 + hcertificate_margin
  linarith only [hsep,f.failure]

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem collision_support_c324040_s0_0 (p : ℝ) (hpa : (21/4 : ℝ) ≤ p) (hpb : p ≤ (43/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-364338109/1250000000 : ℝ)*x 0 + (-1161804367/2500000000 : ℝ)*x 1 + (-2323608751/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (364338109/1250000000 : ℝ)^43 ≤ (2748692894483/12500000000000 : ℝ)^35 := by
    have hnat : (364338109 : ℕ)^43*12500000000000^35 ≤ 2748692894483^35*1250000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      364338109 1250000000 2748692894483 12500000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1161804367/2500000000 : ℝ)^43 ≤ (39005228240577/100000000000000 : ℝ)^35 := by
    have hnat : (1161804367 : ℕ)^43*100000000000000^35 ≤ 39005228240577^35*2500000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1161804367 2500000000 39005228240577 100000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2323608751/5000000000 : ℝ)^43 ≤ (19502614295587/50000000000000 : ℝ)^35 := by
    have hnat : (2323608751 : ℕ)^43*50000000000000^35 ≤ 19502614295587^35*5000000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2323608751 5000000000 19502614295587 50000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (43/8 : ℝ)) 43 35 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-364338109/1250000000 : ℝ), (-1161804367/2500000000 : ℝ), (-2323608751/5000000000 : ℝ)] ![(2748692894483/12500000000000 : ℝ), (39005228240577/100000000000000 : ℝ), (19502614295587/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-364338109/1250000000 : ℝ)|^43 ≤ (2748692894483/12500000000000 : ℝ)^35
        have hw : |(-364338109/1250000000 : ℝ)|=(364338109/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1161804367/2500000000 : ℝ)|^43 ≤ (39005228240577/100000000000000 : ℝ)^35
        have hw : |(-1161804367/2500000000 : ℝ)|=(1161804367/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2323608751/5000000000 : ℝ)|^43 ≤ (19502614295587/50000000000000 : ℝ)^35
        have hw : |(-2323608751/5000000000 : ℝ)|=(2323608751/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c324040_s0_1 (p : ℝ) (hpa : (21/4 : ℝ) ≤ p) (hpb : p ≤ (43/8 : ℝ)) (x : Fin 3 → ℝ) :
    (364338109/1250000000 : ℝ)*x 0 + (1161804367/2500000000 : ℝ)*x 1 + (-2323608751/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (364338109/1250000000 : ℝ)^43 ≤ (2748692894483/12500000000000 : ℝ)^35 := by
    have hnat : (364338109 : ℕ)^43*12500000000000^35 ≤ 2748692894483^35*1250000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      364338109 1250000000 2748692894483 12500000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1161804367/2500000000 : ℝ)^43 ≤ (39005228240577/100000000000000 : ℝ)^35 := by
    have hnat : (1161804367 : ℕ)^43*100000000000000^35 ≤ 39005228240577^35*2500000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1161804367 2500000000 39005228240577 100000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2323608751/5000000000 : ℝ)^43 ≤ (19502614295587/50000000000000 : ℝ)^35 := by
    have hnat : (2323608751 : ℕ)^43*50000000000000^35 ≤ 19502614295587^35*5000000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2323608751 5000000000 19502614295587 50000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (43/8 : ℝ)) 43 35 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(364338109/1250000000 : ℝ), (1161804367/2500000000 : ℝ), (-2323608751/5000000000 : ℝ)] ![(2748692894483/12500000000000 : ℝ), (39005228240577/100000000000000 : ℝ), (19502614295587/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(364338109/1250000000 : ℝ)|^43 ≤ (2748692894483/12500000000000 : ℝ)^35
        have hw : |(364338109/1250000000 : ℝ)|=(364338109/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1161804367/2500000000 : ℝ)|^43 ≤ (39005228240577/100000000000000 : ℝ)^35
        have hw : |(1161804367/2500000000 : ℝ)|=(1161804367/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2323608751/5000000000 : ℝ)|^43 ≤ (19502614295587/50000000000000 : ℝ)^35
        have hw : |(-2323608751/5000000000 : ℝ)|=(2323608751/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c324040_s0_2 (p : ℝ) (hpa : (21/4 : ℝ) ≤ p) (hpb : p ≤ (43/8 : ℝ)) (x : Fin 3 → ℝ) :
    (2885092999/5000000000 : ℝ)*x 0 + (-3188788687/10000000000 : ℝ)*x 1 + (318878871/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2885092999/5000000000 : ℝ)^43 ≤ (508867397277/1000000000000 : ℝ)^35 := by
    have hnat : (2885092999 : ℕ)^43*1000000000000^35 ≤ 508867397277^35*5000000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2885092999 5000000000 508867397277 1000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3188788687/10000000000 : ℝ)^43 ≤ (12278315009777/50000000000000 : ℝ)^35 := by
    have hnat : (3188788687 : ℕ)^43*50000000000000^35 ≤ 12278315009777^35*10000000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3188788687 10000000000 12278315009777 50000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (318878871/1000000000 : ℝ)^43 ≤ (613915755929/2500000000000 : ℝ)^35 := by
    have hnat : (318878871 : ℕ)^43*2500000000000^35 ≤ 613915755929^35*1000000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      318878871 1000000000 613915755929 2500000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (43/8 : ℝ)) 43 35 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2885092999/5000000000 : ℝ), (-3188788687/10000000000 : ℝ), (318878871/1000000000 : ℝ)] ![(508867397277/1000000000000 : ℝ), (12278315009777/50000000000000 : ℝ), (613915755929/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2885092999/5000000000 : ℝ)|^43 ≤ (508867397277/1000000000000 : ℝ)^35
        have hw : |(2885092999/5000000000 : ℝ)|=(2885092999/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3188788687/10000000000 : ℝ)|^43 ≤ (12278315009777/50000000000000 : ℝ)^35
        have hw : |(-3188788687/10000000000 : ℝ)|=(3188788687/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(318878871/1000000000 : ℝ)|^43 ≤ (613915755929/2500000000000 : ℝ)^35
        have hw : |(318878871/1000000000 : ℝ)|=(318878871/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c324040_s0_6 (p : ℝ) (hpa : (21/4 : ℝ) ≤ p) (hpb : p ≤ (43/8 : ℝ)) (x : Fin 3 → ℝ) :
    (2885092999/5000000000 : ℝ)*x 0 + (-3188788687/10000000000 : ℝ)*x 1 + (-318878871/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2885092999/5000000000 : ℝ)^43 ≤ (508867397277/1000000000000 : ℝ)^35 := by
    have hnat : (2885092999 : ℕ)^43*1000000000000^35 ≤ 508867397277^35*5000000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2885092999 5000000000 508867397277 1000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3188788687/10000000000 : ℝ)^43 ≤ (12278315009777/50000000000000 : ℝ)^35 := by
    have hnat : (3188788687 : ℕ)^43*50000000000000^35 ≤ 12278315009777^35*10000000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3188788687 10000000000 12278315009777 50000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (318878871/1000000000 : ℝ)^43 ≤ (613915755929/2500000000000 : ℝ)^35 := by
    have hnat : (318878871 : ℕ)^43*2500000000000^35 ≤ 613915755929^35*1000000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      318878871 1000000000 613915755929 2500000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (43/8 : ℝ)) 43 35 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2885092999/5000000000 : ℝ), (-3188788687/10000000000 : ℝ), (-318878871/1000000000 : ℝ)] ![(508867397277/1000000000000 : ℝ), (12278315009777/50000000000000 : ℝ), (613915755929/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2885092999/5000000000 : ℝ)|^43 ≤ (508867397277/1000000000000 : ℝ)^35
        have hw : |(2885092999/5000000000 : ℝ)|=(2885092999/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3188788687/10000000000 : ℝ)|^43 ≤ (12278315009777/50000000000000 : ℝ)^35
        have hw : |(-3188788687/10000000000 : ℝ)|=(3188788687/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-318878871/1000000000 : ℝ)|^43 ≤ (613915755929/2500000000000 : ℝ)^35
        have hw : |(-318878871/1000000000 : ℝ)|=(318878871/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c324040 (p : ℝ) (hpa : (21/4 : ℝ) ≤ p) (hpb : p ≤ (43/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (49571/25000 : ℝ) (83049/50000 : ℝ) (81117/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![false, false, false]]) : False := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (81117/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (81117/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (81117/100000 : ℝ)*P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (81117/100000 : ℝ)*P 1 ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (81117/100000 : ℝ)*P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (81117/100000 : ℝ)*P 2 ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((-1 : ℝ)*(X 0 1+X 1 1)) ∧ ((-1 : ℝ)*(X 0 1+X 1 1)) ≤ ((-1 : ℝ)*(X 0 0+X 1 0)) ∧ ((-1 : ℝ)*(X 0 0+X 1 0)) ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((-1 : ℝ)*pair X 2 1) ∧ ((-1 : ℝ)*pair X 2 1) ≤ ((-1 : ℝ)*pair X 2 0) ∧ ((-1 : ℝ)*pair X 2 0) ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base5 : ((1 : ℝ)*N 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 2]
  have base10 : ((-1 : ℝ)*X 0 1+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 1).1]
  have base27 : ((1 : ℝ)*X 0 0+(1 : ℝ)*X 1 0+(1 : ℝ)*X 2 0+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [(f.column 0).2]
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base49 : ((-1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.1]
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
  have s0_pow0 : (1 : ℝ) ^ (21/4 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^21 ≤ (1 : ℝ)^4 := by
      have hnat : (1 : ℕ)^21*1^4 ≤ 1^4*1^21 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 21 4 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 21 4 (by norm_num) hpowers
    exact h
  have s0_corner0a : (2 : ℝ) ≤ (1141140309994013/1000000000000000 : ℝ) ^ (21/4 : ℝ) := by
    have hpowers : (2 : ℝ)^4 ≤ (1141140309994013/1000000000000000 : ℝ)^21 := by
      have hnat : (2 : ℕ)^4*1000000000000000^21 ≤ 1141140309994013^21*1^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 1141140309994013 1000000000000000 4 21 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1141140309994013/1000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 21 4 (by norm_num) hpowers
    exact h
  have s0_corner0b : (3 : ℝ) ≤ (12327648392357461/10000000000000000 : ℝ) ^ (21/4 : ℝ) := by
    have hpowers : (3 : ℝ)^4 ≤ (12327648392357461/10000000000000000 : ℝ)^21 := by
      have hnat : (3 : ℕ)^4*10000000000000000^21 ≤ 12327648392357461^21*1^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 12327648392357461 10000000000000000 4 21 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12327648392357461/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 21 4 (by norm_num) hpowers
    exact h
  have major_s0_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(141140309994013/1000000000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(916245292417331/10000000000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (21/4 : ℝ)) (rho := (1 : ℝ)) (alpha := (141140309994013/1000000000000000 : ℝ)) (beta := (916245292417331/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow0,s0_corner0a]) (by linarith only [s0_pow0,s0_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![false, false, false]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (1 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order0.2.2])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(141140309994013/1000000000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(916245292417331/10000000000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow1 : (1 : ℝ) ^ (21/4 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^21 ≤ (1 : ℝ)^4 := by
      have hnat : (1 : ℕ)^21*1^4 ≤ 1^4*1^21 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 21 4 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 21 4 (by norm_num) hpowers
    exact h
  have s0_corner1a : (2 : ℝ) ≤ (1141140309994013/1000000000000000 : ℝ) ^ (21/4 : ℝ) := by
    have hpowers : (2 : ℝ)^4 ≤ (1141140309994013/1000000000000000 : ℝ)^21 := by
      have hnat : (2 : ℕ)^4*1000000000000000^21 ≤ 1141140309994013^21*1^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 1141140309994013 1000000000000000 4 21 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1141140309994013/1000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 21 4 (by norm_num) hpowers
    exact h
  have s0_corner1b : (3 : ℝ) ≤ (12327648392357461/10000000000000000 : ℝ) ^ (21/4 : ℝ) := by
    have hpowers : (3 : ℝ)^4 ≤ (12327648392357461/10000000000000000 : ℝ)^21 := by
      have hnat : (3 : ℕ)^4*10000000000000000^21 ≤ 12327648392357461^21*1^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 12327648392357461 10000000000000000 4 21 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12327648392357461/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 21 4 (by norm_num) hpowers
    exact h
  have major_s0_1 : P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1))+(141140309994013/1000000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(916245292417331/10000000000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (21/4 : ℝ)) (rho := (1 : ℝ)) (alpha := (141140309994013/1000000000000000 : ℝ)) (beta := (916245292417331/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow1,s0_corner1a]) (by linarith only [s0_pow1,s0_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![false, false, false]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (1 : ℝ)*((-1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order1.2.2])
    change lpNorm p (pair X 1) ≤ ((-1 : ℝ)*pair X 1 1)+(141140309994013/1000000000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(916245292417331/10000000000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow2 : (1 : ℝ) ^ (21/4 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^21 ≤ (1 : ℝ)^4 := by
      have hnat : (1 : ℕ)^21*1^4 ≤ 1^4*1^21 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 21 4 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 21 4 (by norm_num) hpowers
    exact h
  have s0_corner2a : (2 : ℝ) ≤ (1141140309994013/1000000000000000 : ℝ) ^ (21/4 : ℝ) := by
    have hpowers : (2 : ℝ)^4 ≤ (1141140309994013/1000000000000000 : ℝ)^21 := by
      have hnat : (2 : ℕ)^4*1000000000000000^21 ≤ 1141140309994013^21*1^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 1141140309994013 1000000000000000 4 21 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1141140309994013/1000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 21 4 (by norm_num) hpowers
    exact h
  have s0_corner2b : (3 : ℝ) ≤ (12327648392357461/10000000000000000 : ℝ) ^ (21/4 : ℝ) := by
    have hpowers : (3 : ℝ)^4 ≤ (12327648392357461/10000000000000000 : ℝ)^21 := by
      have hnat : (3 : ℕ)^4*10000000000000000^21 ≤ 12327648392357461^21*1^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 12327648392357461 10000000000000000 4 21 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12327648392357461/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 21 4 (by norm_num) hpowers
    exact h
  have major_s0_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(141140309994013/1000000000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 1 0))+(916245292417331/10000000000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (21/4 : ℝ)) (rho := (1 : ℝ)) (alpha := (141140309994013/1000000000000000 : ℝ)) (beta := (916245292417331/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow2,s0_corner2a]) (by linarith only [s0_pow2,s0_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![false, false, false]] hX 2 (by
        change ((-1 : ℝ)*pair X 2 0) ≤ (1 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order2.2.2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(141140309994013/1000000000000000 : ℝ)*((-1 : ℝ)*pair X 2 0)+(916245292417331/10000000000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s0_0 : ((-364338109/1250000000 : ℝ)*X 0 0+(-1161804367/2500000000 : ℝ)*X 0 1+(-2323608751/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c324040_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_1 : ((364338109/1250000000 : ℝ)*X 1 0+(1161804367/2500000000 : ℝ)*X 1 1+(-2323608751/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c324040_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_2 : ((2885092999/5000000000 : ℝ)*X 2 0+(-3188788687/10000000000 : ℝ)*X 2 1+(318878871/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c324040_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_6 : ((2885092999/5000000000 : ℝ)*X 0 0+(-3188788687/10000000000 : ℝ)*X 0 1+(-318878871/1000000000 : ℝ)*X 0 2+(2885092999/5000000000 : ℝ)*X 1 0+(-3188788687/10000000000 : ℝ)*X 1 1+(-318878871/1000000000 : ℝ)*X 1 2+(2885092999/5000000000 : ℝ)*X 2 0+(-3188788687/10000000000 : ℝ)*X 2 1+(-318878871/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c324040_s0_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have hsep : (-111213/12500 : ℝ) < ((-49571/25000 : ℝ)*P 0+(-49571/25000 : ℝ)*P 1+(-49571/25000 : ℝ)*P 2+(1 : ℝ)*T) := by
    have hcertificate_margin : (-111213/12500 : ℝ) < (-10955106329848231134066137277/1250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (827247801017/1000000000000 : ℝ)*(base5) + (153771/1000000000000 : ℝ)*(base10) + (51479/1000000000000 : ℝ)*(base27) + (210249460997/250000000000 : ℝ)*(base39) + (28283874083/62500000000 : ℝ)*(base40) + (388455930121/1000000000000 : ℝ)*(base49) + (15611/250000000000 : ℝ)*(base53) + (30072376261/40000000000 : ℝ)*(base60) + (49571/25000 : ℝ)*(major_s0_0) + (49571/25000 : ℝ)*(major_s0_1) + (495709984389/250000000000 : ℝ)*(major_s0_2) + (1460680735871/500000000000 : ℝ)*(sp_s0_0) + (2921361625513/1000000000000 : ℝ)*(sp_s0_1) + (1874304744487/500000000000 : ℝ)*(sp_s0_2) + (10797009219/62500000000 : ℝ)*(sp_s0_6) + (2921361687957/1000000000000 : ℝ)*(f.sum) + (28536267336943/250000000000000000000000000 : ℝ)*base63 + (1359570957045759/2500000000000000000000000000 : ℝ)*base64 + (922827091/2500000000000000000000 : ℝ)*base67 + (5606121663057/250000000000000000000000000 : ℝ)*base68 + (162441242045759/2500000000000000000000000000 : ℝ)*base70 + (486904203/5000000000000000000000 : ℝ)*base73 + (1108566461/2500000000000000000000 : ℝ)*base74 + (1070146793/5000000000000000000000 : ℝ)*base77 + (329480181/500000000000000000000 : ℝ)*base78 + hcertificate_margin
  linarith only [hsep,f.failure]

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
namespace HlawkaSchatten.DiagonalCutoff4
theorem coarse_distinct_p024_b019 (p : ℝ) (hpa : (21/4 : ℝ) ≤ p) (hpb : p ≤ (85/16 : ℝ))
    (c : Fin 88) (hlo : 39 ≤ c.val) (hhi : c.val < 41)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (49571/25000 : ℝ) (83049/50000 : ℝ) (81117/100000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  have hc : c=39 ∨ c=40 := by omega
  rcases hc with rfl|rfl
  · exact collision_c324039 p hpa (by linarith only [hpb]) X hX
  · exact collision_c324040 p hpa (by linarith only [hpb]) X hX

end HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p : ℝ) (hpa : (21/4 : ℝ) ≤ p) (hpb : p ≤ (85/16 : ℝ))
    (c : Fin 88) (hlo : 39 ≤ c.val) (hhi : c.val < 41)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (49571/25000 : ℝ) (83049/50000 : ℝ) (81117/100000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  exact HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p024_b019 p hpa hpb c hlo hhi hn63 hn87 X hX

#print axioms solution
