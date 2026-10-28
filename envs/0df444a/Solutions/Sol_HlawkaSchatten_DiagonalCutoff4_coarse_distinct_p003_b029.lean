-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p003_b029
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:54:55.872434+00:00
-- url     : https://prove2.me/submissions/6ecbbd8c-c7a9-4efd-8622-16cd6d4d4892

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
theorem collision_support_c303069_s0_0 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-404964711/2000000000 : ℝ)*x 0 + (-7531473683/10000000000 : ℝ)*x 1 + (2849890981/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (404964711/2000000000 : ℝ)^33 ≤ (607296932831/5000000000000 : ℝ)^25 := by
    have hnat : (404964711 : ℕ)^33*5000000000000^25 ≤ 607296932831^25*2000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      404964711 2000000000 607296932831 5000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (7531473683/10000000000 : ℝ)^33 ≤ (68783069239527/100000000000000 : ℝ)^25 := by
    have hnat : (7531473683 : ℕ)^33*100000000000000^25 ≤ 68783069239527^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7531473683 10000000000 68783069239527 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2849890981/10000000000 : ℝ)^33 ≤ (2383874010901/12500000000000 : ℝ)^25 := by
    have hnat : (2849890981 : ℕ)^33*12500000000000^25 ≤ 2383874010901^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2849890981 10000000000 2383874010901 12500000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-404964711/2000000000 : ℝ), (-7531473683/10000000000 : ℝ), (2849890981/10000000000 : ℝ)] ![(607296932831/5000000000000 : ℝ), (68783069239527/100000000000000 : ℝ), (2383874010901/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-404964711/2000000000 : ℝ)|^33 ≤ (607296932831/5000000000000 : ℝ)^25
        have hw : |(-404964711/2000000000 : ℝ)|=(404964711/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-7531473683/10000000000 : ℝ)|^33 ≤ (68783069239527/100000000000000 : ℝ)^25
        have hw : |(-7531473683/10000000000 : ℝ)|=(7531473683/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2849890981/10000000000 : ℝ)|^33 ≤ (2383874010901/12500000000000 : ℝ)^25
        have hw : |(2849890981/10000000000 : ℝ)|=(2849890981/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c303069_s0_1 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (1472334407/2500000000 : ℝ)*x 0 + (34232013/125000000 : ℝ)*x 1 + (847429083/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1472334407/2500000000 : ℝ)^33 ≤ (388398682219/781250000000 : ℝ)^25 := by
    have hnat : (1472334407 : ℕ)^33*781250000000^25 ≤ 388398682219^25*2500000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1472334407 2500000000 388398682219 781250000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (34232013/125000000 : ℝ)^33 ≤ (565431010433/3125000000000 : ℝ)^25 := by
    have hnat : (34232013 : ℕ)^33*3125000000000^25 ≤ 565431010433^25*125000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      34232013 125000000 565431010433 3125000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (847429083/2000000000 : ℝ)^33 ≤ (402389704049/1250000000000 : ℝ)^25 := by
    have hnat : (847429083 : ℕ)^33*1250000000000^25 ≤ 402389704049^25*2000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      847429083 2000000000 402389704049 1250000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1472334407/2500000000 : ℝ), (34232013/125000000 : ℝ), (847429083/2000000000 : ℝ)] ![(388398682219/781250000000 : ℝ), (565431010433/3125000000000 : ℝ), (402389704049/1250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1472334407/2500000000 : ℝ)|^33 ≤ (388398682219/781250000000 : ℝ)^25
        have hw : |(1472334407/2500000000 : ℝ)|=(1472334407/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(34232013/125000000 : ℝ)|^33 ≤ (565431010433/3125000000000 : ℝ)^25
        have hw : |(34232013/125000000 : ℝ)|=(34232013/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(847429083/2000000000 : ℝ)|^33 ≤ (402389704049/1250000000000 : ℝ)^25
        have hw : |(847429083/2000000000 : ℝ)|=(847429083/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c303069_s0_7 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-723847061/5000000000 : ℝ)*x 0 + (-1682638353/2000000000 : ℝ)*x 1 + (2081108479/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (723847061/5000000000 : ℝ)^33 ≤ (7799978230669/100000000000000 : ℝ)^25 := by
    have hnat : (723847061 : ℕ)^33*100000000000000^25 ≤ 7799978230669^25*5000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      723847061 5000000000 7799978230669 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1682638353/2000000000 : ℝ)^33 ≤ (19901611720269/25000000000000 : ℝ)^25 := by
    have hnat : (1682638353 : ℕ)^33*25000000000000^25 ≤ 19901611720269^25*2000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1682638353 2000000000 19901611720269 25000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2081108479/10000000000 : ℝ)^33 ≤ (12593574875549/100000000000000 : ℝ)^25 := by
    have hnat : (2081108479 : ℕ)^33*100000000000000^25 ≤ 12593574875549^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2081108479 10000000000 12593574875549 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-723847061/5000000000 : ℝ), (-1682638353/2000000000 : ℝ), (2081108479/10000000000 : ℝ)] ![(7799978230669/100000000000000 : ℝ), (19901611720269/25000000000000 : ℝ), (12593574875549/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-723847061/5000000000 : ℝ)|^33 ≤ (7799978230669/100000000000000 : ℝ)^25
        have hw : |(-723847061/5000000000 : ℝ)|=(723847061/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1682638353/2000000000 : ℝ)|^33 ≤ (19901611720269/25000000000000 : ℝ)^25
        have hw : |(-1682638353/2000000000 : ℝ)|=(1682638353/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2081108479/10000000000 : ℝ)|^33 ≤ (12593574875549/100000000000000 : ℝ)^25
        have hw : |(2081108479/10000000000 : ℝ)|=(2081108479/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c303069_s0_8 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (2813788467/5000000000 : ℝ)*x 0 + (2691971983/10000000000 : ℝ)*x 1 + (570297463/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2813788467/5000000000 : ℝ)^33 ≤ (2926202111401/6250000000000 : ℝ)^25 := by
    have hnat : (2813788467 : ℕ)^33*6250000000000^25 ≤ 2926202111401^25*5000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2813788467 5000000000 2926202111401 6250000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2691971983/10000000000 : ℝ)^33 ≤ (4422146393871/25000000000000 : ℝ)^25 := by
    have hnat : (2691971983 : ℕ)^33*25000000000000^25 ≤ 4422146393871^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2691971983 10000000000 4422146393871 25000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (570297463/1250000000 : ℝ)^33 ≤ (8873045157633/25000000000000 : ℝ)^25 := by
    have hnat : (570297463 : ℕ)^33*25000000000000^25 ≤ 8873045157633^25*1250000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      570297463 1250000000 8873045157633 25000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2813788467/5000000000 : ℝ), (2691971983/10000000000 : ℝ), (570297463/1250000000 : ℝ)] ![(2926202111401/6250000000000 : ℝ), (4422146393871/25000000000000 : ℝ), (8873045157633/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2813788467/5000000000 : ℝ)|^33 ≤ (2926202111401/6250000000000 : ℝ)^25
        have hw : |(2813788467/5000000000 : ℝ)|=(2813788467/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2691971983/10000000000 : ℝ)|^33 ≤ (4422146393871/25000000000000 : ℝ)^25
        have hw : |(2691971983/10000000000 : ℝ)|=(2691971983/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(570297463/1250000000 : ℝ)|^33 ≤ (8873045157633/25000000000000 : ℝ)^25
        have hw : |(570297463/1250000000 : ℝ)|=(570297463/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c303069_s0_9 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (421830281/1000000000 : ℝ)*x 0 + (-2533567579/10000000000 : ℝ)*x 1 + (-6063950671/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (421830281/1000000000 : ℝ)^33 ≤ (6400469444933/20000000000000 : ℝ)^25 := by
    have hnat : (421830281 : ℕ)^33*20000000000000^25 ≤ 6400469444933^25*1000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      421830281 1000000000 6400469444933 20000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2533567579/10000000000 : ℝ)^33 ≤ (4081942655613/25000000000000 : ℝ)^25 := by
    have hnat : (2533567579 : ℕ)^33*25000000000000^25 ≤ 4081942655613^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2533567579 10000000000 4081942655613 25000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6063950671/10000000000 : ℝ)^33 ≤ (51669882133583/100000000000000 : ℝ)^25 := by
    have hnat : (6063950671 : ℕ)^33*100000000000000^25 ≤ 51669882133583^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6063950671 10000000000 51669882133583 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(421830281/1000000000 : ℝ), (-2533567579/10000000000 : ℝ), (-6063950671/10000000000 : ℝ)] ![(6400469444933/20000000000000 : ℝ), (4081942655613/25000000000000 : ℝ), (51669882133583/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(421830281/1000000000 : ℝ)|^33 ≤ (6400469444933/20000000000000 : ℝ)^25
        have hw : |(421830281/1000000000 : ℝ)|=(421830281/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2533567579/10000000000 : ℝ)|^33 ≤ (4081942655613/25000000000000 : ℝ)^25
        have hw : |(-2533567579/10000000000 : ℝ)|=(2533567579/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-6063950671/10000000000 : ℝ)|^33 ≤ (51669882133583/100000000000000 : ℝ)^25
        have hw : |(-6063950671/10000000000 : ℝ)|=(6063950671/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c303069_s0_13 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-2420833843/10000000000 : ℝ)*x 0 + (-7478753371/10000000000 : ℝ)*x 1 + (2550986453/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2420833843/10000000000 : ℝ)^33 ≤ (3843915083693/25000000000000 : ℝ)^25 := by
    have hnat : (2420833843 : ℕ)^33*25000000000000^25 ≤ 3843915083693^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2420833843 10000000000 3843915083693 25000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (7478753371/10000000000 : ℝ)^33 ≤ (68148226680217/100000000000000 : ℝ)^25 := by
    have hnat : (7478753371 : ℕ)^33*100000000000000^25 ≤ 68148226680217^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7478753371 10000000000 68148226680217 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2550986453/10000000000 : ℝ)^33 ≤ (16476112968387/100000000000000 : ℝ)^25 := by
    have hnat : (2550986453 : ℕ)^33*100000000000000^25 ≤ 16476112968387^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2550986453 10000000000 16476112968387 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2420833843/10000000000 : ℝ), (-7478753371/10000000000 : ℝ), (2550986453/10000000000 : ℝ)] ![(3843915083693/25000000000000 : ℝ), (68148226680217/100000000000000 : ℝ), (16476112968387/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2420833843/10000000000 : ℝ)|^33 ≤ (3843915083693/25000000000000 : ℝ)^25
        have hw : |(-2420833843/10000000000 : ℝ)|=(2420833843/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-7478753371/10000000000 : ℝ)|^33 ≤ (68148226680217/100000000000000 : ℝ)^25
        have hw : |(-7478753371/10000000000 : ℝ)|=(7478753371/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2550986453/10000000000 : ℝ)|^33 ≤ (16476112968387/100000000000000 : ℝ)^25
        have hw : |(2550986453/10000000000 : ℝ)|=(2550986453/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c303069_s0_14 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (2961244299/5000000000 : ℝ)*x 0 + (2475924407/10000000000 : ℝ)*x 1 + (4423792643/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2961244299/5000000000 : ℝ)^33 ≤ (25042379476051/50000000000000 : ℝ)^25 := by
    have hnat : (2961244299 : ℕ)^33*50000000000000^25 ≤ 25042379476051^25*5000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2961244299 5000000000 25042379476051 50000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2475924407/10000000000 : ℝ)^33 ≤ (7919601828969/50000000000000 : ℝ)^25 := by
    have hnat : (2475924407 : ℕ)^33*50000000000000^25 ≤ 7919601828969^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2475924407 10000000000 7919601828969 50000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4423792643/10000000000 : ℝ)^33 ≤ (6815207474551/20000000000000 : ℝ)^25 := by
    have hnat : (4423792643 : ℕ)^33*20000000000000^25 ≤ 6815207474551^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4423792643 10000000000 6815207474551 20000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2961244299/5000000000 : ℝ), (2475924407/10000000000 : ℝ), (4423792643/10000000000 : ℝ)] ![(25042379476051/50000000000000 : ℝ), (7919601828969/50000000000000 : ℝ), (6815207474551/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2961244299/5000000000 : ℝ)|^33 ≤ (25042379476051/50000000000000 : ℝ)^25
        have hw : |(2961244299/5000000000 : ℝ)|=(2961244299/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2475924407/10000000000 : ℝ)|^33 ≤ (7919601828969/50000000000000 : ℝ)^25
        have hw : |(2475924407/10000000000 : ℝ)|=(2475924407/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4423792643/10000000000 : ℝ)|^33 ≤ (6815207474551/20000000000000 : ℝ)^25
        have hw : |(4423792643/10000000000 : ℝ)|=(4423792643/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c303069_s0_15 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (230431721/625000000 : ℝ)*x 0 + (-1560350071/5000000000 : ℝ)*x 1 + (-3033756459/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (230431721/625000000 : ℝ)^33 ≤ (26791323276797/100000000000000 : ℝ)^25 := by
    have hnat : (230431721 : ℕ)^33*100000000000000^25 ≤ 26791323276797^25*625000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      230431721 625000000 26791323276797 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1560350071/5000000000 : ℝ)^33 ≤ (5374681117153/25000000000000 : ℝ)^25 := by
    have hnat : (1560350071 : ℕ)^33*25000000000000^25 ≤ 5374681117153^25*5000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1560350071 5000000000 5374681117153 25000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3033756459/5000000000 : ℝ)^33 ≤ (51709952248167/100000000000000 : ℝ)^25 := by
    have hnat : (3033756459 : ℕ)^33*100000000000000^25 ≤ 51709952248167^25*5000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3033756459 5000000000 51709952248167 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(230431721/625000000 : ℝ), (-1560350071/5000000000 : ℝ), (-3033756459/5000000000 : ℝ)] ![(26791323276797/100000000000000 : ℝ), (5374681117153/25000000000000 : ℝ), (51709952248167/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(230431721/625000000 : ℝ)|^33 ≤ (26791323276797/100000000000000 : ℝ)^25
        have hw : |(230431721/625000000 : ℝ)|=(230431721/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1560350071/5000000000 : ℝ)|^33 ≤ (5374681117153/25000000000000 : ℝ)^25
        have hw : |(-1560350071/5000000000 : ℝ)|=(1560350071/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3033756459/5000000000 : ℝ)|^33 ≤ (51709952248167/100000000000000 : ℝ)^25
        have hw : |(-3033756459/5000000000 : ℝ)|=(3033756459/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c303069_s0_19 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (2961244299/5000000000 : ℝ)*x 0 + (-993386941/2500000000 : ℝ)*x 1 + (2992522989/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2961244299/5000000000 : ℝ)^33 ≤ (25042379476051/50000000000000 : ℝ)^25 := by
    have hnat : (2961244299 : ℕ)^33*50000000000000^25 ≤ 25042379476051^25*5000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2961244299 5000000000 25042379476051 50000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (993386941/2500000000 : ℝ)^33 ≤ (369679655611/1250000000000 : ℝ)^25 := by
    have hnat : (993386941 : ℕ)^33*1250000000000^25 ≤ 369679655611^25*2500000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      993386941 2500000000 369679655611 1250000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2992522989/10000000000 : ℝ)^33 ≤ (4068173716429/20000000000000 : ℝ)^25 := by
    have hnat : (2992522989 : ℕ)^33*20000000000000^25 ≤ 4068173716429^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2992522989 10000000000 4068173716429 20000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2961244299/5000000000 : ℝ), (-993386941/2500000000 : ℝ), (2992522989/10000000000 : ℝ)] ![(25042379476051/50000000000000 : ℝ), (369679655611/1250000000000 : ℝ), (4068173716429/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2961244299/5000000000 : ℝ)|^33 ≤ (25042379476051/50000000000000 : ℝ)^25
        have hw : |(2961244299/5000000000 : ℝ)|=(2961244299/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-993386941/2500000000 : ℝ)|^33 ≤ (369679655611/1250000000000 : ℝ)^25
        have hw : |(-993386941/2500000000 : ℝ)|=(993386941/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2992522989/10000000000 : ℝ)|^33 ≤ (4068173716429/20000000000000 : ℝ)^25
        have hw : |(2992522989/10000000000 : ℝ)|=(2992522989/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c303069_s0_20 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-1169689939/10000000000 : ℝ)*x 0 + (-525824483/625000000 : ℝ)*x 1 + (579127117/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1169689939/10000000000 : ℝ)^33 ≤ (5886449137083/100000000000000 : ℝ)^25 := by
    have hnat : (1169689939 : ℕ)^33*100000000000000^25 ≤ 5886449137083^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1169689939 10000000000 5886449137083 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (525824483/625000000 : ℝ)^33 ≤ (19901611604737/25000000000000 : ℝ)^25 := by
    have hnat : (525824483 : ℕ)^33*25000000000000^25 ≤ 19901611604737^25*625000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      525824483 625000000 19901611604737 25000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (579127117/2500000000 : ℝ)^33 ≤ (14507104437783/100000000000000 : ℝ)^25 := by
    have hnat : (579127117 : ℕ)^33*100000000000000^25 ≤ 14507104437783^25*2500000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      579127117 2500000000 14507104437783 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1169689939/10000000000 : ℝ), (-525824483/625000000 : ℝ), (579127117/2500000000 : ℝ)] ![(5886449137083/100000000000000 : ℝ), (19901611604737/25000000000000 : ℝ), (14507104437783/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1169689939/10000000000 : ℝ)|^33 ≤ (5886449137083/100000000000000 : ℝ)^25
        have hw : |(-1169689939/10000000000 : ℝ)|=(1169689939/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-525824483/625000000 : ℝ)|^33 ≤ (19901611604737/25000000000000 : ℝ)^25
        have hw : |(-525824483/625000000 : ℝ)|=(525824483/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(579127117/2500000000 : ℝ)|^33 ≤ (14507104437783/100000000000000 : ℝ)^25
        have hw : |(579127117/2500000000 : ℝ)|=(579127117/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c303069_s0_21 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (3549861297/5000000000 : ℝ)*x 0 + (2132216417/10000000000 : ℝ)*x 1 + (831096003/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3549861297/5000000000 : ℝ)^33 ≤ (15906646519551/25000000000000 : ℝ)^25 := by
    have hnat : (3549861297 : ℕ)^33*25000000000000^25 ≤ 15906646519551^25*5000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3549861297 5000000000 15906646519551 25000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2132216417/10000000000 : ℝ)^33 ≤ (13003411115211/100000000000000 : ℝ)^25 := by
    have hnat : (2132216417 : ℕ)^33*100000000000000^25 ≤ 13003411115211^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2132216417 10000000000 13003411115211 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (831096003/2500000000 : ℝ)^33 ≤ (23370002786833/100000000000000 : ℝ)^25 := by
    have hnat : (831096003 : ℕ)^33*100000000000000^25 ≤ 23370002786833^25*2500000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      831096003 2500000000 23370002786833 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3549861297/5000000000 : ℝ), (2132216417/10000000000 : ℝ), (831096003/2500000000 : ℝ)] ![(15906646519551/25000000000000 : ℝ), (13003411115211/100000000000000 : ℝ), (23370002786833/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3549861297/5000000000 : ℝ)|^33 ≤ (15906646519551/25000000000000 : ℝ)^25
        have hw : |(3549861297/5000000000 : ℝ)|=(3549861297/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2132216417/10000000000 : ℝ)|^33 ≤ (13003411115211/100000000000000 : ℝ)^25
        have hw : |(2132216417/10000000000 : ℝ)|=(2132216417/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(831096003/2500000000 : ℝ)|^33 ≤ (23370002786833/100000000000000 : ℝ)^25
        have hw : |(831096003/2500000000 : ℝ)|=(831096003/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c303069_s0_22 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (793665291/2500000000 : ℝ)*x 0 + (-3372030279/10000000000 : ℝ)*x 1 + (-3143623461/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (793665291/2500000000 : ℝ)^33 ≤ (21990775280943/100000000000000 : ℝ)^25 := by
    have hnat : (793665291 : ℕ)^33*100000000000000^25 ≤ 21990775280943^25*2500000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      793665291 2500000000 21990775280943 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3372030279/10000000000 : ℝ)^33 ≤ (23813143809869/100000000000000 : ℝ)^25 := by
    have hnat : (3372030279 : ℕ)^33*100000000000000^25 ≤ 23813143809869^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3372030279 10000000000 23813143809869 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3143623461/5000000000 : ℝ)^33 ≤ (54196080896191/100000000000000 : ℝ)^25 := by
    have hnat : (3143623461 : ℕ)^33*100000000000000^25 ≤ 54196080896191^25*5000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3143623461 5000000000 54196080896191 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(793665291/2500000000 : ℝ), (-3372030279/10000000000 : ℝ), (-3143623461/5000000000 : ℝ)] ![(21990775280943/100000000000000 : ℝ), (23813143809869/100000000000000 : ℝ), (54196080896191/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(793665291/2500000000 : ℝ)|^33 ≤ (21990775280943/100000000000000 : ℝ)^25
        have hw : |(793665291/2500000000 : ℝ)|=(793665291/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3372030279/10000000000 : ℝ)|^33 ≤ (23813143809869/100000000000000 : ℝ)^25
        have hw : |(-3372030279/10000000000 : ℝ)|=(3372030279/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3143623461/5000000000 : ℝ)|^33 ≤ (54196080896191/100000000000000 : ℝ)^25
        have hw : |(-3143623461/5000000000 : ℝ)|=(3143623461/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c303069_s1_0 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-16923739/50000000 : ℝ)*x 0 + (-2762226337/5000000000 : ℝ)*x 1 + (4055096229/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (16923739/50000000 : ℝ)^33 ≤ (11965882657443/50000000000000 : ℝ)^25 := by
    have hnat : (16923739 : ℕ)^33*50000000000000^25 ≤ 11965882657443^25*50000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      16923739 50000000 11965882657443 50000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2762226337/5000000000 : ℝ)^33 ≤ (9138013925387/20000000000000 : ℝ)^25 := by
    have hnat : (2762226337 : ℕ)^33*20000000000000^25 ≤ 9138013925387^25*5000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2762226337 5000000000 9138013925387 20000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4055096229/10000000000 : ℝ)^33 ≤ (30378165046877/100000000000000 : ℝ)^25 := by
    have hnat : (4055096229 : ℕ)^33*100000000000000^25 ≤ 30378165046877^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4055096229 10000000000 30378165046877 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-16923739/50000000 : ℝ), (-2762226337/5000000000 : ℝ), (4055096229/10000000000 : ℝ)] ![(11965882657443/50000000000000 : ℝ), (9138013925387/20000000000000 : ℝ), (30378165046877/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-16923739/50000000 : ℝ)|^33 ≤ (11965882657443/50000000000000 : ℝ)^25
        have hw : |(-16923739/50000000 : ℝ)|=(16923739/50000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2762226337/5000000000 : ℝ)|^33 ≤ (9138013925387/20000000000000 : ℝ)^25
        have hw : |(-2762226337/5000000000 : ℝ)|=(2762226337/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4055096229/10000000000 : ℝ)|^33 ≤ (30378165046877/100000000000000 : ℝ)^25
        have hw : |(4055096229/10000000000 : ℝ)|=(4055096229/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c303069_s1_1 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (2630435919/5000000000 : ℝ)*x 0 + (3485092833/10000000000 : ℝ)*x 1 + (4247250447/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2630435919/5000000000 : ℝ)^33 ≤ (42834745699763/100000000000000 : ℝ)^25 := by
    have hnat : (2630435919 : ℕ)^33*100000000000000^25 ≤ 42834745699763^25*5000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2630435919 5000000000 42834745699763 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3485092833/10000000000 : ℝ)^33 ≤ (12436350331641/50000000000000 : ℝ)^25 := by
    have hnat : (3485092833 : ℕ)^33*50000000000000^25 ≤ 12436350331641^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3485092833 10000000000 12436350331641 50000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4247250447/10000000000 : ℝ)^33 ≤ (16146276809453/50000000000000 : ℝ)^25 := by
    have hnat : (4247250447 : ℕ)^33*50000000000000^25 ≤ 16146276809453^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4247250447 10000000000 16146276809453 50000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2630435919/5000000000 : ℝ), (3485092833/10000000000 : ℝ), (4247250447/10000000000 : ℝ)] ![(42834745699763/100000000000000 : ℝ), (12436350331641/50000000000000 : ℝ), (16146276809453/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2630435919/5000000000 : ℝ)|^33 ≤ (42834745699763/100000000000000 : ℝ)^25
        have hw : |(2630435919/5000000000 : ℝ)|=(2630435919/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3485092833/10000000000 : ℝ)|^33 ≤ (12436350331641/50000000000000 : ℝ)^25
        have hw : |(3485092833/10000000000 : ℝ)|=(3485092833/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4247250447/10000000000 : ℝ)|^33 ≤ (16146276809453/50000000000000 : ℝ)^25
        have hw : |(4247250447/10000000000 : ℝ)|=(4247250447/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c303069_s1_2 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (1026569673/2500000000 : ℝ)*x 0 + (-4007657237/10000000000 : ℝ)*x 1 + (-4919526127/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1026569673/2500000000 : ℝ)^33 ≤ (6177061311423/20000000000000 : ℝ)^25 := by
    have hnat : (1026569673 : ℕ)^33*20000000000000^25 ≤ 6177061311423^25*2500000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1026569673 2500000000 6177061311423 20000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4007657237/10000000000 : ℝ)^33 ≤ (747748519413/2500000000000 : ℝ)^25 := by
    have hnat : (4007657237 : ℕ)^33*2500000000000^25 ≤ 747748519413^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4007657237 10000000000 747748519413 2500000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4919526127/10000000000 : ℝ)^33 ≤ (39204752657889/100000000000000 : ℝ)^25 := by
    have hnat : (4919526127 : ℕ)^33*100000000000000^25 ≤ 39204752657889^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4919526127 10000000000 39204752657889 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1026569673/2500000000 : ℝ), (-4007657237/10000000000 : ℝ), (-4919526127/10000000000 : ℝ)] ![(6177061311423/20000000000000 : ℝ), (747748519413/2500000000000 : ℝ), (39204752657889/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1026569673/2500000000 : ℝ)|^33 ≤ (6177061311423/20000000000000 : ℝ)^25
        have hw : |(1026569673/2500000000 : ℝ)|=(1026569673/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-4007657237/10000000000 : ℝ)|^33 ≤ (747748519413/2500000000000 : ℝ)^25
        have hw : |(-4007657237/10000000000 : ℝ)|=(4007657237/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-4919526127/10000000000 : ℝ)|^33 ≤ (39204752657889/100000000000000 : ℝ)^25
        have hw : |(-4919526127/10000000000 : ℝ)|=(4919526127/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c303069_s1_6 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (241529593/500000000 : ℝ)*x 0 + (-430519381/1000000000 : ℝ)*x 1 + (3899873267/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (241529593/500000000 : ℝ)^33 ≤ (38271938109419/100000000000000 : ℝ)^25 := by
    have hnat : (241529593 : ℕ)^33*100000000000000^25 ≤ 38271938109419^25*500000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      241529593 500000000 38271938109419 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (430519381/1000000000 : ℝ)^33 ≤ (32875349116743/100000000000000 : ℝ)^25 := by
    have hnat : (430519381 : ℕ)^33*100000000000000^25 ≤ 32875349116743^25*1000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      430519381 1000000000 32875349116743 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3899873267/10000000000 : ℝ)^33 ≤ (5770542552513/20000000000000 : ℝ)^25 := by
    have hnat : (3899873267 : ℕ)^33*20000000000000^25 ≤ 5770542552513^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3899873267 10000000000 5770542552513 20000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(241529593/500000000 : ℝ), (-430519381/1000000000 : ℝ), (3899873267/10000000000 : ℝ)] ![(38271938109419/100000000000000 : ℝ), (32875349116743/100000000000000 : ℝ), (5770542552513/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(241529593/500000000 : ℝ)|^33 ≤ (38271938109419/100000000000000 : ℝ)^25
        have hw : |(241529593/500000000 : ℝ)|=(241529593/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-430519381/1000000000 : ℝ)|^33 ≤ (32875349116743/100000000000000 : ℝ)^25
        have hw : |(-430519381/1000000000 : ℝ)|=(430519381/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3899873267/10000000000 : ℝ)|^33 ≤ (5770542552513/20000000000000 : ℝ)^25
        have hw : |(3899873267/10000000000 : ℝ)|=(3899873267/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c303069 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (7521/5000 : ℝ) (91389/50000 : ℝ) (76461/100000 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, false], ![true, false, true]]) : False := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (76461/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (76461/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (76461/100000 : ℝ)*P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (76461/100000 : ℝ)*P 1 ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 0+X 2 0)) ∧ ((-1 : ℝ)*(X 0 0+X 2 0)) ≤ ((-1 : ℝ)*(X 0 2+X 2 2)) ∧ ((-1 : ℝ)*(X 0 2+X 2 2)) ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 0) ∧ ((-1 : ℝ)*pair X 1 0) ≤ ((-1 : ℝ)*pair X 1 2) ∧ ((-1 : ℝ)*pair X 1 2) ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (76461/100000 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (76461/100000 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((-1 : ℝ)*(X 0 1+X 1 1)) ∧ ((-1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((-1 : ℝ)*pair X 2 1) ∧ ((-1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base3 : ((1 : ℝ)*N 1+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 1]
  have base15 : ((1 : ℝ)*X 1 0+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 0).2]
  have base22 : ((-1 : ℝ)*X 2 1+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 1).1]
  have base33 : ((-1 : ℝ)*N 1+(-1 : ℝ)*N 2+(1 : ℝ)*P 0) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 0,f.sum]
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
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
  have s0_pow0 : (1 : ℝ) ^ (131/32 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^131 ≤ (1 : ℝ)^32 := by
      have hnat : (1 : ℕ)^131*1^32 ≤ 1^32*1^131 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 131 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 131 32 (by norm_num) hpowers
    exact h
  have s0_corner0a : (2 : ℝ) ≤ (2368994434359861/2000000000000000 : ℝ) ^ (131/32 : ℝ) := by
    have hpowers : (2 : ℝ)^32 ≤ (2368994434359861/2000000000000000 : ℝ)^131 := by
      have hnat : (2 : ℕ)^32*2000000000000000^131 ≤ 2368994434359861^131*1^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 2368994434359861 2000000000000000 32 131 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2368994434359861/2000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 131 32 (by norm_num) hpowers
    exact h
  have s0_corner0b : (3 : ℝ) ≤ (13078221948759057/10000000000000000 : ℝ) ^ (131/32 : ℝ) := by
    have hpowers : (3 : ℝ)^32 ≤ (13078221948759057/10000000000000000 : ℝ)^131 := by
      have hnat : (3 : ℕ)^32*10000000000000000^131 ≤ 13078221948759057^131*1^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 13078221948759057 10000000000000000 32 131 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (13078221948759057/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 131 32 (by norm_num) hpowers
    exact h
  have major_s0_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(368994434359861/2000000000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(154156222119969/1250000000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (131/32 : ℝ)) (rho := (1 : ℝ)) (alpha := (368994434359861/2000000000000000 : ℝ)) (beta := (154156222119969/1250000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow0,s0_corner0a]) (by linarith only [s0_pow0,s0_corner0b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, false], ![true, false, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (1 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order0.2.2])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(368994434359861/2000000000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(154156222119969/1250000000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow1 : (1 : ℝ) ^ (131/32 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^131 ≤ (1 : ℝ)^32 := by
      have hnat : (1 : ℕ)^131*1^32 ≤ 1^32*1^131 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 131 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 131 32 (by norm_num) hpowers
    exact h
  have s0_corner1a : (2 : ℝ) ≤ (2368994434359861/2000000000000000 : ℝ) ^ (131/32 : ℝ) := by
    have hpowers : (2 : ℝ)^32 ≤ (2368994434359861/2000000000000000 : ℝ)^131 := by
      have hnat : (2 : ℕ)^32*2000000000000000^131 ≤ 2368994434359861^131*1^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 2368994434359861 2000000000000000 32 131 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2368994434359861/2000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 131 32 (by norm_num) hpowers
    exact h
  have s0_corner1b : (3 : ℝ) ≤ (13078221948759057/10000000000000000 : ℝ) ^ (131/32 : ℝ) := by
    have hpowers : (3 : ℝ)^32 ≤ (13078221948759057/10000000000000000 : ℝ)^131 := by
      have hnat : (3 : ℕ)^32*10000000000000000^131 ≤ 13078221948759057^131*1^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 13078221948759057 10000000000000000 32 131 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (13078221948759057/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 131 32 (by norm_num) hpowers
    exact h
  have major_s0_1 : P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1))+(368994434359861/2000000000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2))+(154156222119969/1250000000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 2 0)) := by
    have hh := chart_majorant (a := (131/32 : ℝ)) (rho := (1 : ℝ)) (alpha := (368994434359861/2000000000000000 : ℝ)) (beta := (154156222119969/1250000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow1,s0_corner1a]) (by linarith only [s0_pow1,s0_corner1b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, false], ![true, false, true]] hX 1 (by
        change ((-1 : ℝ)*pair X 1 2) ≤ (1 : ℝ)*((-1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order1.2.2])
    change lpNorm p (pair X 1) ≤ ((-1 : ℝ)*pair X 1 1)+(368994434359861/2000000000000000 : ℝ)*((-1 : ℝ)*pair X 1 2)+(154156222119969/1250000000000000 : ℝ)*((-1 : ℝ)*pair X 1 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow2 : (1 : ℝ) ^ (131/32 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^131 ≤ (1 : ℝ)^32 := by
      have hnat : (1 : ℕ)^131*1^32 ≤ 1^32*1^131 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 131 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 131 32 (by norm_num) hpowers
    exact h
  have s0_corner2a : (2 : ℝ) ≤ (2368994434359861/2000000000000000 : ℝ) ^ (131/32 : ℝ) := by
    have hpowers : (2 : ℝ)^32 ≤ (2368994434359861/2000000000000000 : ℝ)^131 := by
      have hnat : (2 : ℕ)^32*2000000000000000^131 ≤ 2368994434359861^131*1^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 2368994434359861 2000000000000000 32 131 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2368994434359861/2000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 131 32 (by norm_num) hpowers
    exact h
  have s0_corner2b : (3 : ℝ) ≤ (13078221948759057/10000000000000000 : ℝ) ^ (131/32 : ℝ) := by
    have hpowers : (3 : ℝ)^32 ≤ (13078221948759057/10000000000000000 : ℝ)^131 := by
      have hnat : (3 : ℕ)^32*10000000000000000^131 ≤ 13078221948759057^131*1^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 13078221948759057 10000000000000000 32 131 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (13078221948759057/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 131 32 (by norm_num) hpowers
    exact h
  have major_s0_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(368994434359861/2000000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(154156222119969/1250000000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (131/32 : ℝ)) (rho := (1 : ℝ)) (alpha := (368994434359861/2000000000000000 : ℝ)) (beta := (154156222119969/1250000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow2,s0_corner2a]) (by linarith only [s0_pow2,s0_corner2b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, false], ![true, false, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (1 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order2.2.2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(368994434359861/2000000000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(154156222119969/1250000000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s0_0 : ((-404964711/2000000000 : ℝ)*X 0 0+(-7531473683/10000000000 : ℝ)*X 0 1+(2849890981/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c303069_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_1 : ((1472334407/2500000000 : ℝ)*X 1 0+(34232013/125000000 : ℝ)*X 1 1+(847429083/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c303069_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_7 : ((-723847061/5000000000 : ℝ)*X 0 0+(-1682638353/2000000000 : ℝ)*X 0 1+(2081108479/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c303069_s0_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_8 : ((2813788467/5000000000 : ℝ)*X 1 0+(2691971983/10000000000 : ℝ)*X 1 1+(570297463/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c303069_s0_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_9 : ((421830281/1000000000 : ℝ)*X 2 0+(-2533567579/10000000000 : ℝ)*X 2 1+(-6063950671/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c303069_s0_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_13 : ((-2420833843/10000000000 : ℝ)*X 0 0+(-7478753371/10000000000 : ℝ)*X 0 1+(2550986453/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c303069_s0_13 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_14 : ((2961244299/5000000000 : ℝ)*X 1 0+(2475924407/10000000000 : ℝ)*X 1 1+(4423792643/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c303069_s0_14 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_15 : ((230431721/625000000 : ℝ)*X 2 0+(-1560350071/5000000000 : ℝ)*X 2 1+(-3033756459/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c303069_s0_15 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_19 : ((2961244299/5000000000 : ℝ)*X 0 0+(-993386941/2500000000 : ℝ)*X 0 1+(2992522989/10000000000 : ℝ)*X 0 2+(2961244299/5000000000 : ℝ)*X 1 0+(-993386941/2500000000 : ℝ)*X 1 1+(2992522989/10000000000 : ℝ)*X 1 2+(2961244299/5000000000 : ℝ)*X 2 0+(-993386941/2500000000 : ℝ)*X 2 1+(2992522989/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c303069_s0_19 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_20 : ((-1169689939/10000000000 : ℝ)*X 0 0+(-525824483/625000000 : ℝ)*X 0 1+(579127117/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c303069_s0_20 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_21 : ((3549861297/5000000000 : ℝ)*X 1 0+(2132216417/10000000000 : ℝ)*X 1 1+(831096003/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c303069_s0_21 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_22 : ((793665291/2500000000 : ℝ)*X 2 0+(-3372030279/10000000000 : ℝ)*X 2 1+(-3143623461/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c303069_s0_22 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s0_0 : (0 : ℝ) ≤ ((22143/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(22143/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (29772073500960409813503/5000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2495776515279/1000000000000 : ℝ)*(base3) + (791559192091/1000000000000 : ℝ)*(base40) + (2973665185139/1000000000000 : ℝ)*(base49) + (2018355961997/1000000000000 : ℝ)*(base50) + (483887/200000000000 : ℝ)*(base60) + (3754147034283/1000000000000 : ℝ)*(major_s0_0) + (3754147034283/1000000000000 : ℝ)*(major_s0_1) + (3754147034283/1000000000000 : ℝ)*(major_s0_2) + (8575799/1000000000000 : ℝ)*(sp_s0_0) + (156638364739/31250000000 : ℝ)*(sp_s0_7) + (3754146041877/500000000000 : ℝ)*(sp_s0_8) + (200498259981/40000000000 : ℝ)*(sp_s0_9) + (59068949/1000000000000 : ℝ)*(sp_s0_15) + (79321027/1000000000000 : ℝ)*(sp_s0_20) + (2495776515279/1000000000000 : ℝ)*(f.failure) + (200500622739/40000000000 : ℝ)*(f.sum) + (3409084429395499/10000000000000000000000000000 : ℝ)*base63 + (481819245272227/1250000000000000000000000000 : ℝ)*base64 + (226387504485337/2000000000000000000000000000 : ℝ)*base67 + (1243980678914663/2000000000000000000000000000 : ℝ)*base69 + (4944774393395499/10000000000000000000000000000 : ℝ)*base71 + (63308279897227/1250000000000000000000000000 : ℝ)*base73 + (511617503852773/1250000000000000000000000000 : ℝ)*base75 + (614515127285337/2000000000000000000000000000 : ℝ)*base76 + (7357124118395499/10000000000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base80 + (1/1000000000000 : ℝ)*base84 + (1641/5000000000000000 : ℝ)*base86 + (1641/5000000000000000 : ℝ)*base88 + (1641/5000000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s0_1 : (0 : ℝ) ≤ ((-1309/20000 : ℝ)*X 0 1+(1 : ℝ)*X 0 2+(-1309/20000 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (81131459697258017994291/5000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1040251812599/1000000000000 : ℝ)*(base3) + (11512197/1000000000000 : ℝ)*(base39) + (136800844401/200000000000 : ℝ)*(base40) + (592794785979/1000000000000 : ℝ)*(base49) + (2495749637497/1000000000000 : ℝ)*(major_s0_0) + (2495749637497/1000000000000 : ℝ)*(major_s0_1) + (2495749637497/1000000000000 : ℝ)*(major_s0_2) + (100590591/500000000000 : ℝ)*(sp_s0_0) + (227934299/1000000000000 : ℝ)*(sp_s0_9) + (3332105318009/1000000000000 : ℝ)*(sp_s0_13) + (2186270876229/500000000000 : ℝ)*(sp_s0_14) + (833019641223/250000000000 : ℝ)*(sp_s0_15) + (309467777219/500000000000 : ℝ)*(sp_s0_19) + (4139833/250000000000 : ℝ)*(sp_s0_21) + (1659187367037/1000000000000 : ℝ)*(f.failure) + (3332306499191/1000000000000 : ℝ)*(f.sum) + (3651274099481159/10000000000000000000000000000 : ℝ)*base62 + (155201439747407/1250000000000000000000000000 : ℝ)*base65 + (337777357507917/2000000000000000000000000000 : ℝ)*base66 + (136091805892083/2000000000000000000000000000 : ℝ)*base68 + (33115990481159/10000000000000000000000000000 : ℝ)*base70 + (350426887377593/1250000000000000000000000000 : ℝ)*base73 + (595920123127593/1250000000000000000000000000 : ℝ)*base74 + (218508680707917/2000000000000000000000000000 : ℝ)*base77 + (3689161075481159/10000000000000000000000000000 : ℝ)*base79 + (277/5000000000000000 : ℝ)*base87 + (277/5000000000000000 : ℝ)*base89 + (277/5000000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s0_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(1583/4000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(1583/4000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (791305773481822414011/125000000000000000000000000 : ℝ) := by norm_num
    linear_combination (564717038303/200000000000 : ℝ)*(base3) + (1635981/500000000000 : ℝ)*(base22) + (775695960707/500000000000 : ℝ)*(base40) + (183867843533/50000000000 : ℝ)*(base49) + (109638953397/62500000000 : ℝ)*(base50) + (1061810904217/250000000000 : ℝ)*(major_s0_0) + (1061810904217/250000000000 : ℝ)*(major_s0_1) + (1061810904217/250000000000 : ℝ)*(major_s0_2) + (34343/200000000000 : ℝ)*(sp_s0_1) + (7096857/50000000000 : ℝ)*(sp_s0_7) + (2250961/500000000000 : ℝ)*(sp_s0_19) + (5670753493007/1000000000000 : ℝ)*(sp_s0_20) + (2123620112487/250000000000 : ℝ)*(sp_s0_21) + (1134178431637/200000000000 : ℝ)*(sp_s0_22) + (2823589693437/1000000000000 : ℝ)*(f.failure) + (5670895430147/1000000000000 : ℝ)*(f.sum) + (387493859654999/2500000000000000000000000000 : ℝ)*base62 + (96896148134273/312500000000000000000000000 : ℝ)*base64 + (219889109866163/500000000000000000000000000 : ℝ)*base67 + (136868143966163/500000000000000000000000000 : ℝ)*base68 + (728321189095001/2500000000000000000000000000 : ℝ)*base71 + (125333612959477/312500000000000000000000000 : ℝ)*base72 + (947186240727/312500000000000000000000000 : ℝ)*base75 + (36813718416163/500000000000000000000000000 : ℝ)*base76 + (202361904999/2500000000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base83 + (323/5000000000000000 : ℝ)*base86 + (323/5000000000000000 : ℝ)*base88 + (323/5000000000000000 : ℝ)*base90 + hcertificate_margin
  have s1_pow0 : (22143/100000 : ℝ) ^ (131/32 : ℝ) ≤ (104359445448203101/50000000000000000000 : ℝ) := by
    have hpowers : (22143/100000 : ℝ)^131 ≤ (104359445448203101/50000000000000000000 : ℝ)^32 := by
      have hnat : (22143 : ℕ)^131*50000000000000000000^32 ≤ 104359445448203101^32*100000^131 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        22143 100000 104359445448203101 50000000000000000000 131 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (22143/100000 : ℝ)) (X := (104359445448203101/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 131 32 (by norm_num) hpowers
    exact h
  have s1_corner0a : (50104359445448203101/50000000000000000000 : ℝ) ≤ (500254723030503/500000000000000 : ℝ) ^ (131/32 : ℝ) := by
    have hpowers : (50104359445448203101/50000000000000000000 : ℝ)^32 ≤ (500254723030503/500000000000000 : ℝ)^131 := by
      have hnat : (50104359445448203101 : ℕ)^32*500000000000000^131 ≤ 500254723030503^131*50000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50104359445448203101 50000000000000000000 500254723030503 500000000000000 32 131 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (500254723030503/500000000000000 : ℝ)) (X := (50104359445448203101/50000000000000000000 : ℝ)) (by norm_num) 131 32 (by norm_num) hpowers
    exact h
  have s1_corner0b : (25104359445448203101/25000000000000000000 : ℝ) ≤ (5005090454277141/5000000000000000 : ℝ) ^ (131/32 : ℝ) := by
    have hpowers : (25104359445448203101/25000000000000000000 : ℝ)^32 ≤ (5005090454277141/5000000000000000 : ℝ)^131 := by
      have hnat : (25104359445448203101 : ℕ)^32*5000000000000000^131 ≤ 5005090454277141^131*25000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25104359445448203101 25000000000000000000 5005090454277141 5000000000000000 32 131 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5005090454277141/5000000000000000 : ℝ)) (X := (25104359445448203101/25000000000000000000 : ℝ)) (by norm_num) 131 32 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(254723030503/110715000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(847741324037/369050000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (131/32 : ℝ)) (rho := (22143/100000 : ℝ)) (alpha := (254723030503/110715000000000 : ℝ)) (beta := (847741324037/369050000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, false], ![true, false, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (22143/100000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(254723030503/110715000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(847741324037/369050000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (1309/20000 : ℝ) ^ (131/32 : ℝ) ≤ (1421117977175689/100000000000000000000 : ℝ) := by
    have hpowers : (1309/20000 : ℝ)^131 ≤ (1421117977175689/100000000000000000000 : ℝ)^32 := by
      have hnat : (1309 : ℕ)^131*100000000000000000000^32 ≤ 1421117977175689^32*20000^131 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1309 20000 1421117977175689 100000000000000000000 131 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1309/20000 : ℝ)) (X := (1421117977175689/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 131 32 (by norm_num) hpowers
    exact h
  have s1_corner1a : (100001421117977175689/100000000000000000000 : ℝ) ≤ (10000034714145857/10000000000000000 : ℝ) ^ (131/32 : ℝ) := by
    have hpowers : (100001421117977175689/100000000000000000000 : ℝ)^32 ≤ (10000034714145857/10000000000000000 : ℝ)^131 := by
      have hnat : (100001421117977175689 : ℕ)^32*10000000000000000^131 ≤ 10000034714145857^131*100000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100001421117977175689 100000000000000000000 10000034714145857 10000000000000000 32 131 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000034714145857/10000000000000000 : ℝ)) (X := (100001421117977175689/100000000000000000000 : ℝ)) (by norm_num) 131 32 (by norm_num) hpowers
    exact h
  have s1_corner1b : (50001421117977175689/50000000000000000000 : ℝ) ≤ (100000694279189/100000000000000 : ℝ) ^ (131/32 : ℝ) := by
    have hpowers : (50001421117977175689/50000000000000000000 : ℝ)^32 ≤ (100000694279189/100000000000000 : ℝ)^131 := by
      have hnat : (50001421117977175689 : ℕ)^32*100000000000000^131 ≤ 100000694279189^131*50000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50001421117977175689 50000000000000000000 100000694279189 100000000000000 32 131 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (100000694279189/100000000000000 : ℝ)) (X := (50001421117977175689/50000000000000000000 : ℝ)) (by norm_num) 131 32 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1))+(34714145857/654500000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2))+(34713773043/654500000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 2 0)) := by
    have hh := chart_majorant (a := (131/32 : ℝ)) (rho := (1309/20000 : ℝ)) (alpha := (34714145857/654500000000000 : ℝ)) (beta := (34713773043/654500000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, false], ![true, false, true]] hX 1 (by
        change ((-1 : ℝ)*pair X 1 2) ≤ (1309/20000 : ℝ)*((-1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((-1 : ℝ)*pair X 1 1)+(34714145857/654500000000000 : ℝ)*((-1 : ℝ)*pair X 1 2)+(34713773043/654500000000000 : ℝ)*((-1 : ℝ)*pair X 1 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (1583/4000 : ℝ) ^ (131/32 : ℝ) ≤ (2248753776611721487/100000000000000000000 : ℝ) := by
    have hpowers : (1583/4000 : ℝ)^131 ≤ (2248753776611721487/100000000000000000000 : ℝ)^32 := by
      have hnat : (1583 : ℕ)^131*100000000000000000000^32 ≤ 2248753776611721487^32*4000^131 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1583 4000 2248753776611721487 100000000000000000000 131 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1583/4000 : ℝ)) (X := (2248753776611721487/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 131 32 (by norm_num) hpowers
    exact h
  have s1_corner2a : (102248753776611721487/100000000000000000000 : ℝ) ≤ (5027235338151671/5000000000000000 : ℝ) ^ (131/32 : ℝ) := by
    have hpowers : (102248753776611721487/100000000000000000000 : ℝ)^32 ≤ (5027235338151671/5000000000000000 : ℝ)^131 := by
      have hnat : (102248753776611721487 : ℕ)^32*5000000000000000^131 ≤ 5027235338151671^131*100000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        102248753776611721487 100000000000000000000 5027235338151671 5000000000000000 32 131 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5027235338151671/5000000000000000 : ℝ)) (X := (102248753776611721487/100000000000000000000 : ℝ)) (by norm_num) 131 32 (by norm_num) hpowers
    exact h
  have s1_corner2b : (52248753776611721487/50000000000000000000 : ℝ) ≤ (2527010849558227/2500000000000000 : ℝ) ^ (131/32 : ℝ) := by
    have hpowers : (52248753776611721487/50000000000000000000 : ℝ)^32 ≤ (2527010849558227/2500000000000000 : ℝ)^131 := by
      have hnat : (52248753776611721487 : ℕ)^32*2500000000000000^131 ≤ 2527010849558227^131*50000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        52248753776611721487 50000000000000000000 2527010849558227 2500000000000000 32 131 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2527010849558227/2500000000000000 : ℝ)) (X := (52248753776611721487/50000000000000000000 : ℝ)) (by norm_num) 131 32 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(27235338151671/1978750000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(26786360964783/1978750000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (131/32 : ℝ)) (rho := (1583/4000 : ℝ)) (alpha := (27235338151671/1978750000000000 : ℝ)) (beta := (26786360964783/1978750000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, false], ![true, false, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (1583/4000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(27235338151671/1978750000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(26786360964783/1978750000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-16923739/50000000 : ℝ)*X 0 0+(-2762226337/5000000000 : ℝ)*X 0 1+(4055096229/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c303069_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_1 : ((2630435919/5000000000 : ℝ)*X 1 0+(3485092833/10000000000 : ℝ)*X 1 1+(4247250447/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c303069_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((1026569673/2500000000 : ℝ)*X 2 0+(-4007657237/10000000000 : ℝ)*X 2 1+(-4919526127/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c303069_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_6 : ((241529593/500000000 : ℝ)*X 0 0+(-430519381/1000000000 : ℝ)*X 0 1+(3899873267/10000000000 : ℝ)*X 0 2+(241529593/500000000 : ℝ)*X 1 0+(-430519381/1000000000 : ℝ)*X 1 1+(3899873267/10000000000 : ℝ)*X 1 2+(241529593/500000000 : ℝ)*X 2 0+(-430519381/1000000000 : ℝ)*X 2 1+(3899873267/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c303069_s1_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have hsep : (-15063/2500 : ℝ) < ((-7521/5000 : ℝ)*P 0+(-7521/5000 : ℝ)*P 1+(-7521/5000 : ℝ)*P 2+(1 : ℝ)*T) := by
    have hcertificate_margin : (-15063/2500 : ℝ) < (-206513993772669566371184421637413/34760265925000000000000000000000 : ℝ) := by norm_num
    linear_combination (339/2500000000 : ℝ)*(base15) + (11037/200000000000 : ℝ)*(base22) + (46619/1000000000000 : ℝ)*(base33) + (32997/1000000000000 : ℝ)*(base39) + (276557651049/1000000000000 : ℝ)*(base40) + (259472086919/500000000000 : ℝ)*(base49) + (3888450191/12500000000 : ℝ)*(base50) + (24737/1000000000000 : ℝ)*(base59) + (1504199953381/1000000000000 : ℝ)*(major_s1_0) + (7521/5000 : ℝ)*(major_s1_1) + (7521/5000 : ℝ)*(major_s1_2) + (247545567087/125000000000 : ℝ)*(sp_s1_0) + (495091088619/250000000000 : ℝ)*(sp_s1_1) + (1980364434891/1000000000000 : ℝ)*(sp_s1_2) + (1 : ℝ)*(sp_s1_6) + (247545567087/125000000000 : ℝ)*(f.sum) + (4884916951571/12950918750000000000000000 : ℝ)*base63 + (330863114977/989375000000000000000000 : ℝ)*base65 + (879969834207/1636250000000000000000000 : ℝ)*base66 + (1593643822037/1978750000000000000000000 : ℝ)*base69 + (25175271831441143/175261845000000000000000000000 : ℝ)*base71 + (130872606021563/369050000000000000000000000 : ℝ)*base72 + (2140385218313/3272500000000000000000000 : ℝ)*base75 + (124197284132833/221430000000000000000000000 : ℝ)*base76 + (19148014534258171/21958475000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base82 + (1/1000000000000 : ℝ)*base84 + hcertificate_margin
  linarith only [hsep,f.failure]

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
namespace HlawkaSchatten.DiagonalCutoff4
theorem coarse_distinct_p003_b029 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ))
    (c : Fin 88) (hlo : 69 ≤ c.val) (hhi : c.val < 70)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (7521/5000 : ℝ) (91389/50000 : ℝ) (76461/100000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  have hc : c=69 := by omega
  rcases hc with rfl
  · exact collision_c303069 p hpa (by linarith only [hpb]) X hX

end HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ))
    (c : Fin 88) (hlo : 69 ≤ c.val) (hhi : c.val < 70)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (7521/5000 : ℝ) (91389/50000 : ℝ) (76461/100000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  exact HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p003_b029 p hpa hpb c hlo hhi hn63 hn87 X hX

#print axioms solution
