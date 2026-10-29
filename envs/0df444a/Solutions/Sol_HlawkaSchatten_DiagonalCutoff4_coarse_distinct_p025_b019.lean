-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p025_b019
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T02:02:16.443564+00:00
-- url     : https://prove2.me/submissions/b5c33a96-ea02-4add-a0d1-e6776aab34db

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
theorem collision_support_c325039_s0_0 (p : ℝ) (hpa : (85/16 : ℝ) ≤ p) (hpb : p ≤ (87/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-571105389/5000000000 : ℝ)*x 0 + (-3088325079/5000000000 : ℝ)*x 1 + (224972877/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (571105389/5000000000 : ℝ)^87 ≤ (1751246943053/25000000000000 : ℝ)^71 := by
    have hnat : (571105389 : ℕ)^87*25000000000000^71 ≤ 1751246943053^71*5000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      571105389 5000000000 1751246943053 25000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3088325079/5000000000 : ℝ)^87 ≤ (554113525611/1000000000000 : ℝ)^71 := by
    have hnat : (3088325079 : ℕ)^87*1000000000000^71 ≤ 554113525611^71*5000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3088325079 5000000000 554113525611 1000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (224972877/500000000 : ℝ)^87 ≤ (18791829829937/50000000000000 : ℝ)^71 := by
    have hnat : (224972877 : ℕ)^87*50000000000000^71 ≤ 18791829829937^71*500000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      224972877 500000000 18791829829937 50000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (87/16 : ℝ)) 87 71 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-571105389/5000000000 : ℝ), (-3088325079/5000000000 : ℝ), (224972877/500000000 : ℝ)] ![(1751246943053/25000000000000 : ℝ), (554113525611/1000000000000 : ℝ), (18791829829937/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-571105389/5000000000 : ℝ)|^87 ≤ (1751246943053/25000000000000 : ℝ)^71
        have hw : |(-571105389/5000000000 : ℝ)|=(571105389/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3088325079/5000000000 : ℝ)|^87 ≤ (554113525611/1000000000000 : ℝ)^71
        have hw : |(-3088325079/5000000000 : ℝ)|=(3088325079/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(224972877/500000000 : ℝ)|^87 ≤ (18791829829937/50000000000000 : ℝ)^71
        have hw : |(224972877/500000000 : ℝ)|=(224972877/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c325039_s0_1 (p : ℝ) (hpa : (85/16 : ℝ) ≤ p) (hpb : p ≤ (87/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4701588993/10000000000 : ℝ)*x 0 + (186281477/500000000 : ℝ)*x 1 + (1897848113/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4701588993/10000000000 : ℝ)^87 ≤ (39662885195207/100000000000000 : ℝ)^71 := by
    have hnat : (4701588993 : ℕ)^87*100000000000000^71 ≤ 39662885195207^71*10000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4701588993 10000000000 39662885195207 100000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (186281477/500000000 : ℝ)^87 ≤ (932005830903/3125000000000 : ℝ)^71 := by
    have hnat : (186281477 : ℕ)^87*3125000000000^71 ≤ 932005830903^71*500000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      186281477 500000000 932005830903 3125000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1897848113/5000000000 : ℝ)^87 ≤ (3814116024603/12500000000000 : ℝ)^71 := by
    have hnat : (1897848113 : ℕ)^87*12500000000000^71 ≤ 3814116024603^71*5000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1897848113 5000000000 3814116024603 12500000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (87/16 : ℝ)) 87 71 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4701588993/10000000000 : ℝ), (186281477/500000000 : ℝ), (1897848113/5000000000 : ℝ)] ![(39662885195207/100000000000000 : ℝ), (932005830903/3125000000000 : ℝ), (3814116024603/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4701588993/10000000000 : ℝ)|^87 ≤ (39662885195207/100000000000000 : ℝ)^71
        have hw : |(4701588993/10000000000 : ℝ)|=(4701588993/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(186281477/500000000 : ℝ)|^87 ≤ (932005830903/3125000000000 : ℝ)^71
        have hw : |(186281477/500000000 : ℝ)|=(186281477/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1897848113/5000000000 : ℝ)|^87 ≤ (3814116024603/12500000000000 : ℝ)^71
        have hw : |(1897848113/5000000000 : ℝ)|=(1897848113/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c325039_s0_7 (p : ℝ) (hpa : (85/16 : ℝ) ≤ p) (hpb : p ≤ (87/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-262385959/10000000000 : ℝ)*x 0 + (-7863857559/10000000000 : ℝ)*x 1 + (3157546729/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (262385959/10000000000 : ℝ)^87 ≤ (1155168966077/100000000000000 : ℝ)^71 := by
    have hnat : (262385959 : ℕ)^87*100000000000000^71 ≤ 1155168966077^71*10000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      262385959 10000000000 1155168966077 100000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (7863857559/10000000000 : ℝ)^87 ≤ (74493247741919/100000000000000 : ℝ)^71 := by
    have hnat : (7863857559 : ℕ)^87*100000000000000^71 ≤ 74493247741919^71*10000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7863857559 10000000000 74493247741919 100000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3157546729/10000000000 : ℝ)^87 ≤ (12175791637309/50000000000000 : ℝ)^71 := by
    have hnat : (3157546729 : ℕ)^87*50000000000000^71 ≤ 12175791637309^71*10000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3157546729 10000000000 12175791637309 50000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (87/16 : ℝ)) 87 71 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-262385959/10000000000 : ℝ), (-7863857559/10000000000 : ℝ), (3157546729/10000000000 : ℝ)] ![(1155168966077/100000000000000 : ℝ), (74493247741919/100000000000000 : ℝ), (12175791637309/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-262385959/10000000000 : ℝ)|^87 ≤ (1155168966077/100000000000000 : ℝ)^71
        have hw : |(-262385959/10000000000 : ℝ)|=(262385959/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-7863857559/10000000000 : ℝ)|^87 ≤ (74493247741919/100000000000000 : ℝ)^71
        have hw : |(-7863857559/10000000000 : ℝ)|=(7863857559/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3157546729/10000000000 : ℝ)|^87 ≤ (12175791637309/50000000000000 : ℝ)^71
        have hw : |(3157546729/10000000000 : ℝ)|=(3157546729/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c325039_s0_8 (p : ℝ) (hpa : (85/16 : ℝ) ≤ p) (hpb : p ≤ (87/16 : ℝ)) (x : Fin 3 → ℝ) :
    (48036471/156250000 : ℝ)*x 0 + (868110293/2000000000 : ℝ)*x 1 + (4779397171/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (48036471/156250000 : ℝ)^87 ≤ (23567563694427/100000000000000 : ℝ)^71 := by
    have hnat : (48036471 : ℕ)^87*100000000000000^71 ≤ 23567563694427^71*156250000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      48036471 156250000 23567563694427 100000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (868110293/2000000000 : ℝ)^87 ≤ (7192748668371/20000000000000 : ℝ)^71 := by
    have hnat : (868110293 : ℕ)^87*20000000000000^71 ≤ 7192748668371^71*2000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      868110293 2000000000 7192748668371 20000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4779397171/10000000000 : ℝ)^87 ≤ (202343464757/500000000000 : ℝ)^71 := by
    have hnat : (4779397171 : ℕ)^87*500000000000^71 ≤ 202343464757^71*10000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4779397171 10000000000 202343464757 500000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (87/16 : ℝ)) 87 71 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(48036471/156250000 : ℝ), (868110293/2000000000 : ℝ), (4779397171/10000000000 : ℝ)] ![(23567563694427/100000000000000 : ℝ), (7192748668371/20000000000000 : ℝ), (202343464757/500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(48036471/156250000 : ℝ)|^87 ≤ (23567563694427/100000000000000 : ℝ)^71
        have hw : |(48036471/156250000 : ℝ)|=(48036471/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(868110293/2000000000 : ℝ)|^87 ≤ (7192748668371/20000000000000 : ℝ)^71
        have hw : |(868110293/2000000000 : ℝ)|=(868110293/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4779397171/10000000000 : ℝ)|^87 ≤ (202343464757/500000000000 : ℝ)^71
        have hw : |(4779397171/10000000000 : ℝ)|=(4779397171/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c325039_s0_9 (p : ℝ) (hpa : (85/16 : ℝ) ≤ p) (hpb : p ≤ (87/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4808616393/10000000000 : ℝ)*x 0 + (-2636411243/10000000000 : ℝ)*x 1 + (-4705696993/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4808616393/10000000000 : ℝ)^87 ≤ (40772064046667/100000000000000 : ℝ)^71 := by
    have hnat : (4808616393 : ℕ)^87*100000000000000^71 ≤ 40772064046667^71*10000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4808616393 10000000000 40772064046667 100000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2636411243/10000000000 : ℝ)^87 ≤ (305040337177/1562500000000 : ℝ)^71 := by
    have hnat : (2636411243 : ℕ)^87*1562500000000^71 ≤ 305040337177^71*10000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2636411243 10000000000 305040337177 1562500000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4705696993/10000000000 : ℝ)^87 ≤ (39705354360517/100000000000000 : ℝ)^71 := by
    have hnat : (4705696993 : ℕ)^87*100000000000000^71 ≤ 39705354360517^71*10000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4705696993 10000000000 39705354360517 100000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (87/16 : ℝ)) 87 71 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4808616393/10000000000 : ℝ), (-2636411243/10000000000 : ℝ), (-4705696993/10000000000 : ℝ)] ![(40772064046667/100000000000000 : ℝ), (305040337177/1562500000000 : ℝ), (39705354360517/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4808616393/10000000000 : ℝ)|^87 ≤ (40772064046667/100000000000000 : ℝ)^71
        have hw : |(4808616393/10000000000 : ℝ)|=(4808616393/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2636411243/10000000000 : ℝ)|^87 ≤ (305040337177/1562500000000 : ℝ)^71
        have hw : |(-2636411243/10000000000 : ℝ)|=(2636411243/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-4705696993/10000000000 : ℝ)|^87 ≤ (39705354360517/100000000000000 : ℝ)^71
        have hw : |(-4705696993/10000000000 : ℝ)|=(4705696993/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c325039_s0_13 (p : ℝ) (hpa : (85/16 : ℝ) ≤ p) (hpb : p ≤ (87/16 : ℝ)) (x : Fin 3 → ℝ) :
    (6548762767/10000000000 : ℝ)*x 0 + (750551/5000000000 : ℝ)*x 1 + (4779397171/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6548762767/10000000000 : ℝ)^87 ≤ (14882310703453/25000000000000 : ℝ)^71 := by
    have hnat : (6548762767 : ℕ)^87*25000000000000^71 ≤ 14882310703453^71*10000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6548762767 10000000000 14882310703453 25000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (750551/5000000000 : ℝ)^87 ≤ (258027609/12500000000000 : ℝ)^71 := by
    have hnat : (750551 : ℕ)^87*12500000000000^71 ≤ 258027609^71*5000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      750551 5000000000 258027609 12500000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4779397171/10000000000 : ℝ)^87 ≤ (202343464757/500000000000 : ℝ)^71 := by
    have hnat : (4779397171 : ℕ)^87*500000000000^71 ≤ 202343464757^71*10000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4779397171 10000000000 202343464757 500000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (87/16 : ℝ)) 87 71 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6548762767/10000000000 : ℝ), (750551/5000000000 : ℝ), (4779397171/10000000000 : ℝ)] ![(14882310703453/25000000000000 : ℝ), (258027609/12500000000000 : ℝ), (202343464757/500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6548762767/10000000000 : ℝ)|^87 ≤ (14882310703453/25000000000000 : ℝ)^71
        have hw : |(6548762767/10000000000 : ℝ)|=(6548762767/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(750551/5000000000 : ℝ)|^87 ≤ (258027609/12500000000000 : ℝ)^71
        have hw : |(750551/5000000000 : ℝ)|=(750551/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4779397171/10000000000 : ℝ)|^87 ≤ (202343464757/500000000000 : ℝ)^71
        have hw : |(4779397171/10000000000 : ℝ)|=(4779397171/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c325039_s0_14 (p : ℝ) (hpa : (85/16 : ℝ) ≤ p) (hpb : p ≤ (87/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-3690291/250000000 : ℝ)*x 0 + (-5498502439/10000000000 : ℝ)*x 1 + (5807167587/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3690291/250000000 : ℝ)^87 ≤ (570857965969/100000000000000 : ℝ)^71 := by
    have hnat : (3690291 : ℕ)^87*100000000000000^71 ≤ 570857965969^71*250000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3690291 250000000 570857965969 100000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5498502439/10000000000 : ℝ)^87 ≤ (4805161112799/10000000000000 : ℝ)^71 := by
    have hnat : (5498502439 : ℕ)^87*10000000000000^71 ≤ 4805161112799^71*10000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5498502439 10000000000 4805161112799 10000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5807167587/10000000000 : ℝ)^87 ≤ (51377530895531/100000000000000 : ℝ)^71 := by
    have hnat : (5807167587 : ℕ)^87*100000000000000^71 ≤ 51377530895531^71*10000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5807167587 10000000000 51377530895531 100000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (87/16 : ℝ)) 87 71 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-3690291/250000000 : ℝ), (-5498502439/10000000000 : ℝ), (5807167587/10000000000 : ℝ)] ![(570857965969/100000000000000 : ℝ), (4805161112799/10000000000000 : ℝ), (51377530895531/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-3690291/250000000 : ℝ)|^87 ≤ (570857965969/100000000000000 : ℝ)^71
        have hw : |(-3690291/250000000 : ℝ)|=(3690291/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-5498502439/10000000000 : ℝ)|^87 ≤ (4805161112799/10000000000000 : ℝ)^71
        have hw : |(-5498502439/10000000000 : ℝ)|=(5498502439/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5807167587/10000000000 : ℝ)|^87 ≤ (51377530895531/100000000000000 : ℝ)^71
        have hw : |(5807167587/10000000000 : ℝ)|=(5807167587/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c325039_s0_15 (p : ℝ) (hpa : (85/16 : ℝ) ≤ p) (hpb : p ≤ (87/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3425969933/10000000000 : ℝ)*x 0 + (2066242429/5000000000 : ℝ)*x 1 + (4659198363/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3425969933/10000000000 : ℝ)^87 ≤ (13456001938971/50000000000000 : ℝ)^71 := by
    have hnat : (3425969933 : ℕ)^87*50000000000000^71 ≤ 13456001938971^71*10000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3425969933 10000000000 13456001938971 50000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2066242429/5000000000 : ℝ)^87 ≤ (4232857840281/12500000000000 : ℝ)^71 := by
    have hnat : (2066242429 : ℕ)^87*12500000000000^71 ≤ 4232857840281^71*5000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2066242429 5000000000 4232857840281 12500000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4659198363/10000000000 : ℝ)^87 ≤ (19612566690603/50000000000000 : ℝ)^71 := by
    have hnat : (4659198363 : ℕ)^87*50000000000000^71 ≤ 19612566690603^71*10000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4659198363 10000000000 19612566690603 50000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (87/16 : ℝ)) 87 71 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3425969933/10000000000 : ℝ), (2066242429/5000000000 : ℝ), (4659198363/10000000000 : ℝ)] ![(13456001938971/50000000000000 : ℝ), (4232857840281/12500000000000 : ℝ), (19612566690603/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3425969933/10000000000 : ℝ)|^87 ≤ (13456001938971/50000000000000 : ℝ)^71
        have hw : |(3425969933/10000000000 : ℝ)|=(3425969933/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2066242429/5000000000 : ℝ)|^87 ≤ (4232857840281/12500000000000 : ℝ)^71
        have hw : |(2066242429/5000000000 : ℝ)|=(2066242429/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4659198363/10000000000 : ℝ)|^87 ≤ (19612566690603/50000000000000 : ℝ)^71
        have hw : |(4659198363/10000000000 : ℝ)|=(4659198363/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c325039_s0_16 (p : ℝ) (hpa : (85/16 : ℝ) ≤ p) (hpb : p ≤ (87/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1221933827/2000000000 : ℝ)*x 0 + (-1340118747/5000000000 : ℝ)*x 1 + (-1634189077/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1221933827/2000000000 : ℝ)^87 ≤ (27337974312467/50000000000000 : ℝ)^71 := by
    have hnat : (1221933827 : ℕ)^87*50000000000000^71 ≤ 27337974312467^71*2000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1221933827 2000000000 27337974312467 50000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1340118747/5000000000 : ℝ)^87 ≤ (19920990044883/100000000000000 : ℝ)^71 := by
    have hnat : (1340118747 : ℕ)^87*100000000000000^71 ≤ 19920990044883^71*5000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1340118747 5000000000 19920990044883 100000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1634189077/5000000000 : ℝ)^87 ≤ (6350765329387/25000000000000 : ℝ)^71 := by
    have hnat : (1634189077 : ℕ)^87*25000000000000^71 ≤ 6350765329387^71*5000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1634189077 5000000000 6350765329387 25000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (87/16 : ℝ)) 87 71 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1221933827/2000000000 : ℝ), (-1340118747/5000000000 : ℝ), (-1634189077/5000000000 : ℝ)] ![(27337974312467/50000000000000 : ℝ), (19920990044883/100000000000000 : ℝ), (6350765329387/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1221933827/2000000000 : ℝ)|^87 ≤ (27337974312467/50000000000000 : ℝ)^71
        have hw : |(1221933827/2000000000 : ℝ)|=(1221933827/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1340118747/5000000000 : ℝ)|^87 ≤ (19920990044883/100000000000000 : ℝ)^71
        have hw : |(-1340118747/5000000000 : ℝ)|=(1340118747/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1634189077/5000000000 : ℝ)|^87 ≤ (6350765329387/25000000000000 : ℝ)^71
        have hw : |(-1634189077/5000000000 : ℝ)|=(1634189077/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c325039_s0_20 (p : ℝ) (hpa : (85/16 : ℝ) ≤ p) (hpb : p ≤ (87/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4589237779/5000000000 : ℝ)*x 0 + (-204627/5000000000 : ℝ)*x 1 + (1523616329/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4589237779/5000000000 : ℝ)^87 ≤ (11253583425967/12500000000000 : ℝ)^71 := by
    have hnat : (4589237779 : ℕ)^87*12500000000000^71 ≤ 11253583425967^71*5000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4589237779 5000000000 11253583425967 12500000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (204627/5000000000 : ℝ)^87 ≤ (419900383/100000000000000 : ℝ)^71 := by
    have hnat : (204627 : ℕ)^87*100000000000000^71 ≤ 419900383^71*5000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      204627 5000000000 419900383 100000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1523616329/10000000000 : ℝ)^87 ≤ (1994182535147/20000000000000 : ℝ)^71 := by
    have hnat : (1523616329 : ℕ)^87*20000000000000^71 ≤ 1994182535147^71*10000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1523616329 10000000000 1994182535147 20000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (87/16 : ℝ)) 87 71 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4589237779/5000000000 : ℝ), (-204627/5000000000 : ℝ), (1523616329/10000000000 : ℝ)] ![(11253583425967/12500000000000 : ℝ), (419900383/100000000000000 : ℝ), (1994182535147/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4589237779/5000000000 : ℝ)|^87 ≤ (11253583425967/12500000000000 : ℝ)^71
        have hw : |(4589237779/5000000000 : ℝ)|=(4589237779/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-204627/5000000000 : ℝ)|^87 ≤ (419900383/100000000000000 : ℝ)^71
        have hw : |(-204627/5000000000 : ℝ)|=(204627/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1523616329/10000000000 : ℝ)|^87 ≤ (1994182535147/20000000000000 : ℝ)^71
        have hw : |(1523616329/10000000000 : ℝ)|=(1523616329/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c325039_s0_21 (p : ℝ) (hpa : (85/16 : ℝ) ≤ p) (hpb : p ≤ (87/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-662616703/10000000000 : ℝ)*x 0 + (-1969953109/2500000000 : ℝ)*x 1 + (1438473969/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (662616703/10000000000 : ℝ)^87 ≤ (898610263849/25000000000000 : ℝ)^71 := by
    have hnat : (662616703 : ℕ)^87*25000000000000^71 ≤ 898610263849^71*10000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      662616703 10000000000 898610263849 25000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1969953109/2500000000 : ℝ)^87 ≤ (9334810972117/12500000000000 : ℝ)^71 := by
    have hnat : (1969953109 : ℕ)^87*12500000000000^71 ≤ 9334810972117^71*2500000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1969953109 2500000000 9334810972117 12500000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1438473969/5000000000 : ℝ)^87 ≤ (5431767788039/25000000000000 : ℝ)^71 := by
    have hnat : (1438473969 : ℕ)^87*25000000000000^71 ≤ 5431767788039^71*5000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1438473969 5000000000 5431767788039 25000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (87/16 : ℝ)) 87 71 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-662616703/10000000000 : ℝ), (-1969953109/2500000000 : ℝ), (1438473969/5000000000 : ℝ)] ![(898610263849/25000000000000 : ℝ), (9334810972117/12500000000000 : ℝ), (5431767788039/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-662616703/10000000000 : ℝ)|^87 ≤ (898610263849/25000000000000 : ℝ)^71
        have hw : |(-662616703/10000000000 : ℝ)|=(662616703/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1969953109/2500000000 : ℝ)|^87 ≤ (9334810972117/12500000000000 : ℝ)^71
        have hw : |(-1969953109/2500000000 : ℝ)|=(1969953109/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1438473969/5000000000 : ℝ)|^87 ≤ (5431767788039/25000000000000 : ℝ)^71
        have hw : |(1438473969/5000000000 : ℝ)|=(1438473969/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c325039_s0_22 (p : ℝ) (hpa : (85/16 : ℝ) ≤ p) (hpb : p ≤ (87/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3093076647/5000000000 : ℝ)*x 0 + (3224539409/10000000000 : ℝ)*x 1 + (526740031/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3093076647/5000000000 : ℝ)^87 ≤ (55515836334367/100000000000000 : ℝ)^71 := by
    have hnat : (3093076647 : ℕ)^87*100000000000000^71 ≤ 55515836334367^71*5000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3093076647 5000000000 55515836334367 100000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3224539409/10000000000 : ℝ)^87 ≤ (99944715411/400000000000 : ℝ)^71 := by
    have hnat : (3224539409 : ℕ)^87*400000000000^71 ≤ 99944715411^71*10000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3224539409 10000000000 99944715411 400000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (526740031/2000000000 : ℝ)^87 ≤ (1949798479841/10000000000000 : ℝ)^71 := by
    have hnat : (526740031 : ℕ)^87*10000000000000^71 ≤ 1949798479841^71*2000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      526740031 2000000000 1949798479841 10000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (87/16 : ℝ)) 87 71 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3093076647/5000000000 : ℝ), (3224539409/10000000000 : ℝ), (526740031/2000000000 : ℝ)] ![(55515836334367/100000000000000 : ℝ), (99944715411/400000000000 : ℝ), (1949798479841/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3093076647/5000000000 : ℝ)|^87 ≤ (55515836334367/100000000000000 : ℝ)^71
        have hw : |(3093076647/5000000000 : ℝ)|=(3093076647/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3224539409/10000000000 : ℝ)|^87 ≤ (99944715411/400000000000 : ℝ)^71
        have hw : |(3224539409/10000000000 : ℝ)|=(3224539409/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(526740031/2000000000 : ℝ)|^87 ≤ (1949798479841/10000000000000 : ℝ)^71
        have hw : |(526740031/2000000000 : ℝ)|=(526740031/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c325039_s0_23 (p : ℝ) (hpa : (85/16 : ℝ) ≤ p) (hpb : p ≤ (87/16 : ℝ)) (x : Fin 3 → ℝ) :
    (602270727/2500000000 : ℝ)*x 0 + (-738087357/1250000000 : ℝ)*x 1 + (-375196961/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (602270727/2500000000 : ℝ)^87 ≤ (3496074890039/20000000000000 : ℝ)^71 := by
    have hnat : (602270727 : ℕ)^87*20000000000000^71 ≤ 3496074890039^71*2500000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      602270727 2500000000 3496074890039 20000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (738087357/1250000000 : ℝ)^87 ≤ (10487372142341/20000000000000 : ℝ)^71 := by
    have hnat : (738087357 : ℕ)^87*20000000000000^71 ≤ 10487372142341^71*1250000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      738087357 1250000000 10487372142341 20000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (375196961/1000000000 : ℝ)^87 ≤ (30082764824077/100000000000000 : ℝ)^71 := by
    have hnat : (375196961 : ℕ)^87*100000000000000^71 ≤ 30082764824077^71*1000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      375196961 1000000000 30082764824077 100000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (87/16 : ℝ)) 87 71 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(602270727/2500000000 : ℝ), (-738087357/1250000000 : ℝ), (-375196961/1000000000 : ℝ)] ![(3496074890039/20000000000000 : ℝ), (10487372142341/20000000000000 : ℝ), (30082764824077/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(602270727/2500000000 : ℝ)|^87 ≤ (3496074890039/20000000000000 : ℝ)^71
        have hw : |(602270727/2500000000 : ℝ)|=(602270727/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-738087357/1250000000 : ℝ)|^87 ≤ (10487372142341/20000000000000 : ℝ)^71
        have hw : |(-738087357/1250000000 : ℝ)|=(738087357/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-375196961/1000000000 : ℝ)|^87 ≤ (30082764824077/100000000000000 : ℝ)^71
        have hw : |(-375196961/1000000000 : ℝ)|=(375196961/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c325039_s0_27 (p : ℝ) (hpa : (85/16 : ℝ) ≤ p) (hpb : p ≤ (87/16 : ℝ)) (x : Fin 3 → ℝ) :
    (132480671/156250000 : ℝ)*x 0 + (1087/10000000000 : ℝ)*x 1 + (2501715491/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (132480671/156250000 : ℝ)^87 ≤ (20423119460449/25000000000000 : ℝ)^71 := by
    have hnat : (132480671 : ℕ)^87*25000000000000^71 ≤ 20423119460449^71*156250000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      132480671 156250000 20423119460449 25000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1087/10000000000 : ℝ)^87 ≤ (146521/50000000000000 : ℝ)^71 := by
    have hnat : (1087 : ℕ)^87*50000000000000^71 ≤ 146521^71*10000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1087 10000000000 146521 50000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2501715491/10000000000 : ℝ)^87 ≤ (18307521853643/100000000000000 : ℝ)^71 := by
    have hnat : (2501715491 : ℕ)^87*100000000000000^71 ≤ 18307521853643^71*10000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2501715491 10000000000 18307521853643 100000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (87/16 : ℝ)) 87 71 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(132480671/156250000 : ℝ), (1087/10000000000 : ℝ), (2501715491/10000000000 : ℝ)] ![(20423119460449/25000000000000 : ℝ), (146521/50000000000000 : ℝ), (18307521853643/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(132480671/156250000 : ℝ)|^87 ≤ (20423119460449/25000000000000 : ℝ)^71
        have hw : |(132480671/156250000 : ℝ)|=(132480671/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1087/10000000000 : ℝ)|^87 ≤ (146521/50000000000000 : ℝ)^71
        have hw : |(1087/10000000000 : ℝ)|=(1087/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2501715491/10000000000 : ℝ)|^87 ≤ (18307521853643/100000000000000 : ℝ)^71
        have hw : |(2501715491/10000000000 : ℝ)|=(2501715491/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c325039_s1_0 (p : ℝ) (hpa : (85/16 : ℝ) ≤ p) (hpb : p ≤ (87/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-420612833/2000000000 : ℝ)*x 0 + (-1026351061/2000000000 : ℝ)*x 1 + (966989809/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (420612833/2000000000 : ℝ)^87 ≤ (1849975265571/12500000000000 : ℝ)^71 := by
    have hnat : (420612833 : ℕ)^87*12500000000000^71 ≤ 1849975265571^71*2000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      420612833 2000000000 1849975265571 12500000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1026351061/2000000000 : ℝ)^87 ≤ (44154376589861/100000000000000 : ℝ)^71 := by
    have hnat : (1026351061 : ℕ)^87*100000000000000^71 ≤ 44154376589861^71*2000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1026351061 2000000000 44154376589861 100000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (966989809/2000000000 : ℝ)^87 ≤ (10261455316507/25000000000000 : ℝ)^71 := by
    have hnat : (966989809 : ℕ)^87*25000000000000^71 ≤ 10261455316507^71*2000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      966989809 2000000000 10261455316507 25000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (87/16 : ℝ)) 87 71 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-420612833/2000000000 : ℝ), (-1026351061/2000000000 : ℝ), (966989809/2000000000 : ℝ)] ![(1849975265571/12500000000000 : ℝ), (44154376589861/100000000000000 : ℝ), (10261455316507/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-420612833/2000000000 : ℝ)|^87 ≤ (1849975265571/12500000000000 : ℝ)^71
        have hw : |(-420612833/2000000000 : ℝ)|=(420612833/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1026351061/2000000000 : ℝ)|^87 ≤ (44154376589861/100000000000000 : ℝ)^71
        have hw : |(-1026351061/2000000000 : ℝ)|=(1026351061/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(966989809/2000000000 : ℝ)|^87 ≤ (10261455316507/25000000000000 : ℝ)^71
        have hw : |(966989809/2000000000 : ℝ)|=(966989809/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c325039_s1_1 (p : ℝ) (hpa : (85/16 : ℝ) ≤ p) (hpb : p ≤ (87/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2311576247/5000000000 : ℝ)*x 0 + (1876112453/5000000000 : ℝ)*x 1 + (962814191/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2311576247/5000000000 : ℝ)^87 ≤ (7770721319939/20000000000000 : ℝ)^71 := by
    have hnat : (2311576247 : ℕ)^87*20000000000000^71 ≤ 7770721319939^71*5000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2311576247 5000000000 7770721319939 20000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1876112453/5000000000 : ℝ)^87 ≤ (30085273050163/100000000000000 : ℝ)^71 := by
    have hnat : (1876112453 : ℕ)^87*100000000000000^71 ≤ 30085273050163^71*5000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1876112453 5000000000 30085273050163 100000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (962814191/2500000000 : ℝ)^87 ≤ (7765280083833/25000000000000 : ℝ)^71 := by
    have hnat : (962814191 : ℕ)^87*25000000000000^71 ≤ 7765280083833^71*2500000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      962814191 2500000000 7765280083833 25000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (87/16 : ℝ)) 87 71 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2311576247/5000000000 : ℝ), (1876112453/5000000000 : ℝ), (962814191/2500000000 : ℝ)] ![(7770721319939/20000000000000 : ℝ), (30085273050163/100000000000000 : ℝ), (7765280083833/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2311576247/5000000000 : ℝ)|^87 ≤ (7770721319939/20000000000000 : ℝ)^71
        have hw : |(2311576247/5000000000 : ℝ)|=(2311576247/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1876112453/5000000000 : ℝ)|^87 ≤ (30085273050163/100000000000000 : ℝ)^71
        have hw : |(1876112453/5000000000 : ℝ)|=(1876112453/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(962814191/2500000000 : ℝ)|^87 ≤ (7765280083833/25000000000000 : ℝ)^71
        have hw : |(962814191/2500000000 : ℝ)|=(962814191/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c325039_s1_2 (p : ℝ) (hpa : (85/16 : ℝ) ≤ p) (hpb : p ≤ (87/16 : ℝ)) (x : Fin 3 → ℝ) :
    (139811721/312500000 : ℝ)*x 0 + (-239231953/625000000 : ℝ)*x 1 + (-1965367987/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (139811721/312500000 : ℝ)^87 ≤ (37323006096547/100000000000000 : ℝ)^71 := by
    have hnat : (139811721 : ℕ)^87*100000000000000^71 ≤ 37323006096547^71*312500000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      139811721 312500000 37323006096547 100000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (239231953/625000000 : ℝ)^87 ≤ (30828587648967/100000000000000 : ℝ)^71 := by
    have hnat : (239231953 : ℕ)^87*100000000000000^71 ≤ 30828587648967^71*625000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      239231953 625000000 30828587648967 100000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1965367987/5000000000 : ℝ)^87 ≤ (6369681245269/20000000000000 : ℝ)^71 := by
    have hnat : (1965367987 : ℕ)^87*20000000000000^71 ≤ 6369681245269^71*5000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1965367987 5000000000 6369681245269 20000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (87/16 : ℝ)) 87 71 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(139811721/312500000 : ℝ), (-239231953/625000000 : ℝ), (-1965367987/5000000000 : ℝ)] ![(37323006096547/100000000000000 : ℝ), (30828587648967/100000000000000 : ℝ), (6369681245269/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(139811721/312500000 : ℝ)|^87 ≤ (37323006096547/100000000000000 : ℝ)^71
        have hw : |(139811721/312500000 : ℝ)|=(139811721/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-239231953/625000000 : ℝ)|^87 ≤ (30828587648967/100000000000000 : ℝ)^71
        have hw : |(-239231953/625000000 : ℝ)|=(239231953/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1965367987/5000000000 : ℝ)|^87 ≤ (6369681245269/20000000000000 : ℝ)^71
        have hw : |(-1965367987/5000000000 : ℝ)|=(1965367987/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c325039_s1_6 (p : ℝ) (hpa : (85/16 : ℝ) ≤ p) (hpb : p ≤ (87/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3435174543/5000000000 : ℝ)*x 0 + (-2374058213/10000000000 : ℝ)*x 1 + (531182447/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3435174543/5000000000 : ℝ)^87 ≤ (31565424763519/50000000000000 : ℝ)^71 := by
    have hnat : (3435174543 : ℕ)^87*50000000000000^71 ≤ 31565424763519^71*5000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3435174543 5000000000 31565424763519 50000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2374058213/10000000000 : ℝ)^87 ≤ (17169475300221/100000000000000 : ℝ)^71 := by
    have hnat : (2374058213 : ℕ)^87*100000000000000^71 ≤ 17169475300221^71*10000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2374058213 10000000000 17169475300221 100000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (531182447/2000000000 : ℝ)^87 ≤ (19699675160037/100000000000000 : ℝ)^71 := by
    have hnat : (531182447 : ℕ)^87*100000000000000^71 ≤ 19699675160037^71*2000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      531182447 2000000000 19699675160037 100000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (87/16 : ℝ)) 87 71 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3435174543/5000000000 : ℝ), (-2374058213/10000000000 : ℝ), (531182447/2000000000 : ℝ)] ![(31565424763519/50000000000000 : ℝ), (17169475300221/100000000000000 : ℝ), (19699675160037/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3435174543/5000000000 : ℝ)|^87 ≤ (31565424763519/50000000000000 : ℝ)^71
        have hw : |(3435174543/5000000000 : ℝ)|=(3435174543/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2374058213/10000000000 : ℝ)|^87 ≤ (17169475300221/100000000000000 : ℝ)^71
        have hw : |(-2374058213/10000000000 : ℝ)|=(2374058213/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(531182447/2000000000 : ℝ)|^87 ≤ (19699675160037/100000000000000 : ℝ)^71
        have hw : |(531182447/2000000000 : ℝ)|=(531182447/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c325039 (p : ℝ) (hpa : (85/16 : ℝ) ≤ p) (hpb : p ≤ (87/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (200939/100000 : ℝ) (33069/20000 : ℝ) (81317/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, false], ![true, true, true]]) : False := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (81317/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (81317/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (81317/100000 : ℝ)*P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (81317/100000 : ℝ)*P 1 ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 2+X 2 2)) ∧ ((-1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 2) ∧ ((-1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (81317/100000 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (81317/100000 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base3 : ((1 : ℝ)*N 1+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 1]
  have base7 : ((1 : ℝ)*T) ≤ (33069/20000 : ℝ) := by
    linarith only [f.Tcap]
  have base13 : ((1 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 2).2]
  have base17 : ((1 : ℝ)*X 1 1+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 1).2]
  have base19 : ((1 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 2).2]
  have base22 : ((-1 : ℝ)*X 2 1+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 1).1]
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
  have s0_pow0 : (1 : ℝ) ^ (85/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^85 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^85*1^16 ≤ 1^16*1^85 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 85 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 85 16 (by norm_num) hpowers
    exact h
  have s0_corner0a : (2 : ℝ) ≤ (11393691857257931/10000000000000000 : ℝ) ^ (85/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (11393691857257931/10000000000000000 : ℝ)^85 := by
      have hnat : (2 : ℕ)^16*10000000000000000^85 ≤ 11393691857257931^85*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 11393691857257931 10000000000000000 16 85 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11393691857257931/10000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 85 16 (by norm_num) hpowers
    exact h
  have s0_corner0b : (3 : ℝ) ≤ (6148668287254881/5000000000000000 : ℝ) ^ (85/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (6148668287254881/5000000000000000 : ℝ)^85 := by
      have hnat : (3 : ℕ)^16*5000000000000000^85 ≤ 6148668287254881^85*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 6148668287254881 5000000000000000 16 85 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (6148668287254881/5000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 85 16 (by norm_num) hpowers
    exact h
  have major_s0_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(1393691857257931/10000000000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(903644717251831/10000000000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (85/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (1393691857257931/10000000000000000 : ℝ)) (beta := (903644717251831/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow0,s0_corner0a]) (by linarith only [s0_pow0,s0_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, false], ![true, true, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (1 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order0.2.2])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(1393691857257931/10000000000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(903644717251831/10000000000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow1 : (1 : ℝ) ^ (85/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^85 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^85*1^16 ≤ 1^16*1^85 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 85 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 85 16 (by norm_num) hpowers
    exact h
  have s0_corner1a : (2 : ℝ) ≤ (11393691857257931/10000000000000000 : ℝ) ^ (85/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (11393691857257931/10000000000000000 : ℝ)^85 := by
      have hnat : (2 : ℕ)^16*10000000000000000^85 ≤ 11393691857257931^85*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 11393691857257931 10000000000000000 16 85 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11393691857257931/10000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 85 16 (by norm_num) hpowers
    exact h
  have s0_corner1b : (3 : ℝ) ≤ (6148668287254881/5000000000000000 : ℝ) ^ (85/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (6148668287254881/5000000000000000 : ℝ)^85 := by
      have hnat : (3 : ℕ)^16*5000000000000000^85 ≤ 6148668287254881^85*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 6148668287254881 5000000000000000 16 85 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (6148668287254881/5000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 85 16 (by norm_num) hpowers
    exact h
  have major_s0_1 : P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1))+(1393691857257931/10000000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(903644717251831/10000000000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (85/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (1393691857257931/10000000000000000 : ℝ)) (beta := (903644717251831/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow1,s0_corner1a]) (by linarith only [s0_pow1,s0_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, false], ![true, true, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (1 : ℝ)*((-1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order1.2.2])
    change lpNorm p (pair X 1) ≤ ((-1 : ℝ)*pair X 1 1)+(1393691857257931/10000000000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(903644717251831/10000000000000000 : ℝ)*((-1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow2 : (1 : ℝ) ^ (85/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^85 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^85*1^16 ≤ 1^16*1^85 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 85 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 85 16 (by norm_num) hpowers
    exact h
  have s0_corner2a : (2 : ℝ) ≤ (11393691857257931/10000000000000000 : ℝ) ^ (85/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (11393691857257931/10000000000000000 : ℝ)^85 := by
      have hnat : (2 : ℕ)^16*10000000000000000^85 ≤ 11393691857257931^85*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 11393691857257931 10000000000000000 16 85 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11393691857257931/10000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 85 16 (by norm_num) hpowers
    exact h
  have s0_corner2b : (3 : ℝ) ≤ (6148668287254881/5000000000000000 : ℝ) ^ (85/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (6148668287254881/5000000000000000 : ℝ)^85 := by
      have hnat : (3 : ℕ)^16*5000000000000000^85 ≤ 6148668287254881^85*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 6148668287254881 5000000000000000 16 85 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (6148668287254881/5000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 85 16 (by norm_num) hpowers
    exact h
  have major_s0_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(1393691857257931/10000000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(903644717251831/10000000000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (85/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (1393691857257931/10000000000000000 : ℝ)) (beta := (903644717251831/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow2,s0_corner2a]) (by linarith only [s0_pow2,s0_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, false], ![true, true, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (1 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order2.2.2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(1393691857257931/10000000000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(903644717251831/10000000000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s0_0 : ((-571105389/5000000000 : ℝ)*X 0 0+(-3088325079/5000000000 : ℝ)*X 0 1+(224972877/500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c325039_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_1 : ((4701588993/10000000000 : ℝ)*X 1 0+(186281477/500000000 : ℝ)*X 1 1+(1897848113/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c325039_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_7 : ((-262385959/10000000000 : ℝ)*X 0 0+(-7863857559/10000000000 : ℝ)*X 0 1+(3157546729/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c325039_s0_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_8 : ((48036471/156250000 : ℝ)*X 1 0+(868110293/2000000000 : ℝ)*X 1 1+(4779397171/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c325039_s0_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_9 : ((4808616393/10000000000 : ℝ)*X 2 0+(-2636411243/10000000000 : ℝ)*X 2 1+(-4705696993/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c325039_s0_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_13 : ((6548762767/10000000000 : ℝ)*X 0 0+(750551/5000000000 : ℝ)*X 0 1+(4779397171/10000000000 : ℝ)*X 0 2+(6548762767/10000000000 : ℝ)*X 1 0+(750551/5000000000 : ℝ)*X 1 1+(4779397171/10000000000 : ℝ)*X 1 2+(6548762767/10000000000 : ℝ)*X 2 0+(750551/5000000000 : ℝ)*X 2 1+(4779397171/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c325039_s0_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_14 : ((-3690291/250000000 : ℝ)*X 0 0+(-5498502439/10000000000 : ℝ)*X 0 1+(5807167587/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c325039_s0_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_15 : ((3425969933/10000000000 : ℝ)*X 1 0+(2066242429/5000000000 : ℝ)*X 1 1+(4659198363/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c325039_s0_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_16 : ((1221933827/2000000000 : ℝ)*X 2 0+(-1340118747/5000000000 : ℝ)*X 2 1+(-1634189077/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c325039_s0_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_20 : ((4589237779/5000000000 : ℝ)*X 0 0+(-204627/5000000000 : ℝ)*X 0 1+(1523616329/10000000000 : ℝ)*X 0 2+(4589237779/5000000000 : ℝ)*X 1 0+(-204627/5000000000 : ℝ)*X 1 1+(1523616329/10000000000 : ℝ)*X 1 2+(4589237779/5000000000 : ℝ)*X 2 0+(-204627/5000000000 : ℝ)*X 2 1+(1523616329/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c325039_s0_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_21 : ((-662616703/10000000000 : ℝ)*X 0 0+(-1969953109/2500000000 : ℝ)*X 0 1+(1438473969/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c325039_s0_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_22 : ((3093076647/5000000000 : ℝ)*X 1 0+(3224539409/10000000000 : ℝ)*X 1 1+(526740031/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c325039_s0_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_23 : ((602270727/2500000000 : ℝ)*X 2 0+(-738087357/1250000000 : ℝ)*X 2 1+(-375196961/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c325039_s0_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_27 : ((132480671/156250000 : ℝ)*X 0 0+(1087/10000000000 : ℝ)*X 0 1+(2501715491/10000000000 : ℝ)*X 0 2+(132480671/156250000 : ℝ)*X 1 0+(1087/10000000000 : ℝ)*X 1 1+(2501715491/10000000000 : ℝ)*X 1 2+(132480671/156250000 : ℝ)*X 2 0+(1087/10000000000 : ℝ)*X 2 1+(2501715491/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c325039_s0_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s0_0 : (0 : ℝ) ≤ ((12327/25000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(12327/25000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (20163329424958610596521/1250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1174302880027/1000000000000 : ℝ)*(base3) + (282023482749/250000000000 : ℝ)*(base7) + (8027907/1000000000000 : ℝ)*(base40) + (286823508823/500000000000 : ℝ)*(base49) + (899753664703/500000000000 : ℝ)*(major_s0_0) + (899753664703/500000000000 : ℝ)*(major_s0_1) + (899753664703/500000000000 : ℝ)*(major_s0_2) + (104084552069/50000000000 : ℝ)*(sp_s0_7) + (3255929708897/1000000000000 : ℝ)*(sp_s0_8) + (2081692186511/1000000000000 : ℝ)*(sp_s0_9) + (424670056413/500000000000 : ℝ)*(sp_s0_13) + (10104303/500000000000 : ℝ)*(sp_s0_14) + (16884223/200000000000 : ℝ)*(sp_s0_15) + (9531737/500000000000 : ℝ)*(sp_s0_23) + (895549061857/1000000000000 : ℝ)*(f.failure) + (1040855624993/500000000000 : ℝ)*(f.sum) + (850237891009493/2500000000000000000000000000 : ℝ)*base63 + (143187212178807/5000000000000000000000000000 : ℝ)*base64 + (4574053319178807/5000000000000000000000000000 : ℝ)*base67 + (3445803959009493/5000000000000000000000000000 : ℝ)*base69 + (354188817415343/2500000000000000000000000000 : ℝ)*base71 + (4145598997821193/5000000000000000000000000000 : ℝ)*base73 + (4215522583009493/5000000000000000000000000000 : ℝ)*base75 + (3481616705990507/5000000000000000000000000000 : ℝ)*base76 + (4111671317/10000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base82 + (1/1000000000000 : ℝ)*base84 + (116277/100000000000000000 : ℝ)*base86 + (116277/100000000000000000 : ℝ)*base88 + (116277/100000000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s0_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-20771/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(-20771/50000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (14700306565253226984201/5000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (623920296723/1000000000000 : ℝ)*(base7) + (493387/500000000000 : ℝ)*(base13) + (183475651907/200000000000 : ℝ)*(base40) + (485797/125000000000 : ℝ)*(base53) + (2709162732433/1000000000000 : ℝ)*(major_s0_0) + (2709162732433/1000000000000 : ℝ)*(major_s0_1) + (2709158846057/1000000000000 : ℝ)*(major_s0_2) + (19108889/1000000000000 : ℝ)*(sp_s0_0) + (5086249/1000000000000 : ℝ)*(sp_s0_1) + (29110746133/7812500000 : ℝ)*(sp_s0_14) + (3726190514437/1000000000000 : ℝ)*(sp_s0_15) + (1863099743531/500000000000 : ℝ)*(sp_s0_16) + (1972157803017/1000000000000 : ℝ)*(sp_s0_20) + (6909973/500000000000 : ℝ)*(sp_s0_27) + (8426570789/6250000000 : ℝ)*(f.failure) + (1863099743531/500000000000 : ℝ)*(f.sum) + (670129551649581/1000000000000000000000000000 : ℝ)*base62 + (1250041755619633/10000000000000000000000000000 : ℝ)*base64 + (6496344759334823/10000000000000000000000000000 : ℝ)*base66 + (1891011316671933/10000000000000000000000000000 : ℝ)*base68 + (483201066055649/1000000000000000000000000000 : ℝ)*base71 + (2975544451665177/10000000000000000000000000000 : ℝ)*base72 + (3560320059823877/10000000000000000000000000000 : ℝ)*base74 + (152891464176123/10000000000000000000000000000 : ℝ)*base77 + (5013204531/10000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base81 + (123/312500000000000 : ℝ)*base87 + (123/312500000000000 : ℝ)*base89 + (123/312500000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s0_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(63909/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(63909/100000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (16431693278065012356129/2500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (22366992539/100000000000 : ℝ)*(base3) + (1247562753389/1000000000000 : ℝ)*(base7) + (353728875147/1000000000000 : ℝ)*(base40) + (2041403/500000000000 : ℝ)*(base43) + (691553/250000000000 : ℝ)*(base49) + (39522751563/20000000000 : ℝ)*(major_s0_0) + (123508343459/62500000000 : ℝ)*(major_s0_1) + (39522751563/20000000000 : ℝ)*(major_s0_2) + (4473559/1000000000000 : ℝ)*(sp_s0_16) + (2503541/62500000000 : ℝ)*(sp_s0_20) + (2281223186709/1000000000000 : ℝ)*(sp_s0_21) + (1252448597453/500000000000 : ℝ)*(sp_s0_22) + (2281218713151/1000000000000 : ℝ)*(sp_s0_23) + (1003652127849/500000000000 : ℝ)*(sp_s0_27) + (245862871089/250000000000 : ℝ)*(f.failure) + (570306817379/250000000000 : ℝ)*(f.sum) + (2593050041190457/5000000000000000000000000000 : ℝ)*base63 + (143525999698147/200000000000000000000000000 : ℝ)*base64 + (167107406376571/625000000000000000000000000 : ℝ)*base67 + (124337537916153/200000000000000000000000000 : ℝ)*base69 + (28078025569003/100000000000000000000000000 : ℝ)*base71 + (18559578147/200000000000000000000000000 : ℝ)*base72 + (292313053910829/625000000000000000000000000 : ℝ)*base75 + (34985870396153/200000000000000000000000000 : ℝ)*base77 + (319659133441107/5000000000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base80 + (2571/25000000000000000 : ℝ)*base87 + (2571/25000000000000000 : ℝ)*base89 + (2571/25000000000000000 : ℝ)*base91 + (1/1000000000000 : ℝ)*base92 + hcertificate_margin
  have s1_pow0 : (12327/25000 : ℝ) ^ (85/16 : ℝ) ≤ (2336811170945397227/100000000000000000000 : ℝ) := by
    have hpowers : (12327/25000 : ℝ)^85 ≤ (2336811170945397227/100000000000000000000 : ℝ)^16 := by
      have hnat : (12327 : ℕ)^85*100000000000000000000^16 ≤ 2336811170945397227^16*25000^85 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12327 25000 2336811170945397227 100000000000000000000 85 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (12327/25000 : ℝ)) (X := (2336811170945397227/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 85 16 (by norm_num) hpowers
    exact h
  have s1_corner0a : (102336811170945397227/100000000000000000000 : ℝ) ≤ (251089390564339/250000000000000 : ℝ) ^ (85/16 : ℝ) := by
    have hpowers : (102336811170945397227/100000000000000000000 : ℝ)^16 ≤ (251089390564339/250000000000000 : ℝ)^85 := by
      have hnat : (102336811170945397227 : ℕ)^16*250000000000000^85 ≤ 251089390564339^85*100000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        102336811170945397227 100000000000000000000 251089390564339 250000000000000 16 85 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (251089390564339/250000000000000 : ℝ)) (X := (102336811170945397227/100000000000000000000 : ℝ)) (by norm_num) 85 16 (by norm_num) hpowers
    exact h
  have s1_corner0b : (52336811170945397227/50000000000000000000 : ℝ) ≤ (10086350859655733/10000000000000000 : ℝ) ^ (85/16 : ℝ) := by
    have hpowers : (52336811170945397227/50000000000000000000 : ℝ)^16 ≤ (10086350859655733/10000000000000000 : ℝ)^85 := by
      have hnat : (52336811170945397227 : ℕ)^16*10000000000000000^85 ≤ 10086350859655733^85*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        52336811170945397227 50000000000000000000 10086350859655733 10000000000000000 16 85 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10086350859655733/10000000000000000 : ℝ)) (X := (52336811170945397227/50000000000000000000 : ℝ)) (by norm_num) 85 16 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(51875741159/5870000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(42775237082173/4930800000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (85/16 : ℝ)) (rho := (12327/25000 : ℝ)) (alpha := (51875741159/5870000000000 : ℝ)) (beta := (42775237082173/4930800000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, false], ![true, true, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (12327/25000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(51875741159/5870000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(42775237082173/4930800000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (20771/50000 : ℝ) ^ (85/16 : ℝ) ≤ (470093584462101107/50000000000000000000 : ℝ) := by
    have hpowers : (20771/50000 : ℝ)^85 ≤ (470093584462101107/50000000000000000000 : ℝ)^16 := by
      have hnat : (20771 : ℕ)^85*50000000000000000000^16 ≤ 470093584462101107^16*50000^85 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20771 50000 470093584462101107 50000000000000000000 85 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (20771/50000 : ℝ)) (X := (470093584462101107/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 85 16 (by norm_num) hpowers
    exact h
  have s1_corner1a : (50470093584462101107/50000000000000000000 : ℝ) ≤ (2003526097325013/2000000000000000 : ℝ) ^ (85/16 : ℝ) := by
    have hpowers : (50470093584462101107/50000000000000000000 : ℝ)^16 ≤ (2003526097325013/2000000000000000 : ℝ)^85 := by
      have hnat : (50470093584462101107 : ℕ)^16*2000000000000000^85 ≤ 2003526097325013^85*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50470093584462101107 50000000000000000000 2003526097325013 2000000000000000 16 85 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2003526097325013/2000000000000000 : ℝ)) (X := (50470093584462101107/50000000000000000000 : ℝ)) (by norm_num) 85 16 (by norm_num) hpowers
    exact h
  have s1_corner1b : (25470093584462101107/25000000000000000000 : ℝ) ≤ (5017564084396009/5000000000000000 : ℝ) ^ (85/16 : ℝ) := by
    have hpowers : (25470093584462101107/25000000000000000000 : ℝ)^16 ≤ (5017564084396009/5000000000000000 : ℝ)^85 := by
      have hnat : (25470093584462101107 : ℕ)^16*5000000000000000^85 ≤ 5017564084396009^85*25000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25470093584462101107 25000000000000000000 5017564084396009 5000000000000000 16 85 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5017564084396009/5000000000000000 : ℝ)) (X := (25470093584462101107/25000000000000000000 : ℝ)) (by norm_num) 85 16 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1))+(3526097325013/830840000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(17497682166953/4154200000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (85/16 : ℝ)) (rho := (20771/50000 : ℝ)) (alpha := (3526097325013/830840000000000 : ℝ)) (beta := (17497682166953/4154200000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, false], ![true, true, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (20771/50000 : ℝ)*((-1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((-1 : ℝ)*pair X 1 1)+(3526097325013/830840000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(17497682166953/4154200000000000 : ℝ)*((-1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (63909/100000 : ℝ) ^ (85/16 : ℝ) ≤ (9269327833004506843/100000000000000000000 : ℝ) := by
    have hpowers : (63909/100000 : ℝ)^85 ≤ (9269327833004506843/100000000000000000000 : ℝ)^16 := by
      have hnat : (63909 : ℕ)^85*100000000000000000000^16 ≤ 9269327833004506843^16*100000^85 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        63909 100000 9269327833004506843 100000000000000000000 85 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (63909/100000 : ℝ)) (X := (9269327833004506843/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 85 16 (by norm_num) hpowers
    exact h
  have s1_corner2a : (109269327833004506843/100000000000000000000 : ℝ) ≤ (5084131064959339/5000000000000000 : ℝ) ^ (85/16 : ℝ) := by
    have hpowers : (109269327833004506843/100000000000000000000 : ℝ)^16 ≤ (5084131064959339/5000000000000000 : ℝ)^85 := by
      have hnat : (109269327833004506843 : ℕ)^16*5000000000000000^85 ≤ 5084131064959339^85*100000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        109269327833004506843 100000000000000000000 5084131064959339 5000000000000000 16 85 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5084131064959339/5000000000000000 : ℝ)) (X := (109269327833004506843/100000000000000000000 : ℝ)) (by norm_num) 85 16 (by norm_num) hpowers
    exact h
  have s1_corner2b : (59269327833004506843/50000000000000000000 : ℝ) ≤ (2065061804557839/2000000000000000 : ℝ) ^ (85/16 : ℝ) := by
    have hpowers : (59269327833004506843/50000000000000000000 : ℝ)^16 ≤ (2065061804557839/2000000000000000 : ℝ)^85 := by
      have hnat : (59269327833004506843 : ℕ)^16*2000000000000000^85 ≤ 2065061804557839^85*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        59269327833004506843 50000000000000000000 2065061804557839 2000000000000000 16 85 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2065061804557839/2000000000000000 : ℝ)) (X := (59269327833004506843/50000000000000000000 : ℝ)) (by norm_num) 85 16 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(84131064959339/3195450000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(157046892870517/6390900000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (85/16 : ℝ)) (rho := (63909/100000 : ℝ)) (alpha := (84131064959339/3195450000000000 : ℝ)) (beta := (157046892870517/6390900000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, false], ![true, true, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (63909/100000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(84131064959339/3195450000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(157046892870517/6390900000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-420612833/2000000000 : ℝ)*X 0 0+(-1026351061/2000000000 : ℝ)*X 0 1+(966989809/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c325039_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_1 : ((2311576247/5000000000 : ℝ)*X 1 0+(1876112453/5000000000 : ℝ)*X 1 1+(962814191/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c325039_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((139811721/312500000 : ℝ)*X 2 0+(-239231953/625000000 : ℝ)*X 2 1+(-1965367987/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c325039_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_6 : ((3435174543/5000000000 : ℝ)*X 0 0+(-2374058213/10000000000 : ℝ)*X 0 1+(531182447/2000000000 : ℝ)*X 0 2+(3435174543/5000000000 : ℝ)*X 1 0+(-2374058213/10000000000 : ℝ)*X 1 1+(531182447/2000000000 : ℝ)*X 1 2+(3435174543/5000000000 : ℝ)*X 2 0+(-2374058213/10000000000 : ℝ)*X 2 1+(531182447/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c325039_s1_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have hsep : (-452817/50000 : ℝ) < ((-200939/100000 : ℝ)*P 0+(-200939/100000 : ℝ)*P 1+(-200939/100000 : ℝ)*P 2+(1 : ℝ)*T) := by
    have hcertificate_margin : (-452817/50000 : ℝ) < (-352058289793241726987295341/39450000000000000000000000 : ℝ) := by norm_num
    linear_combination (1371/1000000000000 : ℝ)*(base17) + (2901/250000000000 : ℝ)*(base19) + (5207/500000000000 : ℝ)*(base22) + (615588830169/1000000000000 : ℝ)*(base40) + (491/1000000000000 : ℝ)*(base43) + (148536227737/500000000000 : ℝ)*(base49) + (49013029667/250000000000 : ℝ)*(base59) + (200939/100000 : ℝ)*(major_s1_0) + (2009389999509/1000000000000 : ℝ)*(major_s1_1) + (2009390005503/1000000000000 : ℝ)*(major_s1_2) + (185920093173/62500000000 : ℝ)*(sp_s1_0) + (743680369571/250000000000 : ℝ)*(sp_s1_1) + (2974721474851/1000000000000 : ℝ)*(sp_s1_2) + (1 : ℝ)*(sp_s1_6) + (743680371439/250000000000 : ℝ)*(f.sum) + (948186641717958523/29498974200000000000000000000000 : ℝ)*base62 + (262276268110739/710100000000000000000000000 : ℝ)*base65 + (1086056376618723/4154200000000000000000000000 : ℝ)*base67 + (51064262015867/355050000000000000000000000 : ℝ)*base68 + (49923091420972513/416828700000000000000000000000 : ℝ)*base71 + (244257829607/1926093750000000000000000 : ℝ)*base73 + (88676690043769/830840000000000000000000000 : ℝ)*base75 + (59379955239/366875000000000000000000 : ℝ)*base76 + (9747455263513026019/51208823400000000000000000000000 : ℝ)*base78 + (5503/1000000000000 : ℝ)*base81 + (5503/1000000000000 : ℝ)*base83 + (5503/1000000000000 : ℝ)*base90 + hcertificate_margin
  linarith only [hsep,f.failure]

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem collision_support_c325040_s0_0 (p : ℝ) (hpa : (85/16 : ℝ) ≤ p) (hpb : p ≤ (87/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-2908958317/10000000000 : ℝ)*x 0 + (-463621473/1000000000 : ℝ)*x 1 + (-4636215193/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2908958317/10000000000 : ℝ)^87 ≤ (22023665915683/100000000000000 : ℝ)^71 := by
    have hnat : (2908958317 : ℕ)^87*100000000000000^71 ≤ 22023665915683^71*10000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2908958317 10000000000 22023665915683 100000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (463621473/1000000000 : ℝ)^87 ≤ (9747041162563/25000000000000 : ℝ)^71 := by
    have hnat : (463621473 : ℕ)^87*25000000000000^71 ≤ 9747041162563^71*1000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      463621473 1000000000 9747041162563 25000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4636215193/10000000000 : ℝ)^87 ≤ (38988169421271/100000000000000 : ℝ)^71 := by
    have hnat : (4636215193 : ℕ)^87*100000000000000^71 ≤ 38988169421271^71*10000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4636215193 10000000000 38988169421271 100000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (87/16 : ℝ)) 87 71 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2908958317/10000000000 : ℝ), (-463621473/1000000000 : ℝ), (-4636215193/10000000000 : ℝ)] ![(22023665915683/100000000000000 : ℝ), (9747041162563/25000000000000 : ℝ), (38988169421271/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2908958317/10000000000 : ℝ)|^87 ≤ (22023665915683/100000000000000 : ℝ)^71
        have hw : |(-2908958317/10000000000 : ℝ)|=(2908958317/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-463621473/1000000000 : ℝ)|^87 ≤ (9747041162563/25000000000000 : ℝ)^71
        have hw : |(-463621473/1000000000 : ℝ)|=(463621473/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-4636215193/10000000000 : ℝ)|^87 ≤ (38988169421271/100000000000000 : ℝ)^71
        have hw : |(-4636215193/10000000000 : ℝ)|=(4636215193/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c325040_s0_1 (p : ℝ) (hpa : (85/16 : ℝ) ≤ p) (hpb : p ≤ (87/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2908958317/10000000000 : ℝ)*x 0 + (463621473/1000000000 : ℝ)*x 1 + (-4636215193/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2908958317/10000000000 : ℝ)^87 ≤ (22023665915683/100000000000000 : ℝ)^71 := by
    have hnat : (2908958317 : ℕ)^87*100000000000000^71 ≤ 22023665915683^71*10000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2908958317 10000000000 22023665915683 100000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (463621473/1000000000 : ℝ)^87 ≤ (9747041162563/25000000000000 : ℝ)^71 := by
    have hnat : (463621473 : ℕ)^87*25000000000000^71 ≤ 9747041162563^71*1000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      463621473 1000000000 9747041162563 25000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4636215193/10000000000 : ℝ)^87 ≤ (38988169421271/100000000000000 : ℝ)^71 := by
    have hnat : (4636215193 : ℕ)^87*100000000000000^71 ≤ 38988169421271^71*10000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4636215193 10000000000 38988169421271 100000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (87/16 : ℝ)) 87 71 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2908958317/10000000000 : ℝ), (463621473/1000000000 : ℝ), (-4636215193/10000000000 : ℝ)] ![(22023665915683/100000000000000 : ℝ), (9747041162563/25000000000000 : ℝ), (38988169421271/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2908958317/10000000000 : ℝ)|^87 ≤ (22023665915683/100000000000000 : ℝ)^71
        have hw : |(2908958317/10000000000 : ℝ)|=(2908958317/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(463621473/1000000000 : ℝ)|^87 ≤ (9747041162563/25000000000000 : ℝ)^71
        have hw : |(463621473/1000000000 : ℝ)|=(463621473/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-4636215193/10000000000 : ℝ)|^87 ≤ (38988169421271/100000000000000 : ℝ)^71
        have hw : |(-4636215193/10000000000 : ℝ)|=(4636215193/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c325040_s0_2 (p : ℝ) (hpa : (85/16 : ℝ) ≤ p) (hpb : p ≤ (87/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1440824371/2500000000 : ℝ)*x 0 + (-635680683/2000000000 : ℝ)*x 1 + (3178403733/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1440824371/2500000000 : ℝ)^87 ≤ (12725585065703/25000000000000 : ℝ)^71 := by
    have hnat : (1440824371 : ℕ)^87*25000000000000^71 ≤ 12725585065703^71*2500000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1440824371 2500000000 12725585065703 25000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (635680683/2000000000 : ℝ)^87 ≤ (24548828356703/100000000000000 : ℝ)^71 := by
    have hnat : (635680683 : ℕ)^87*100000000000000^71 ≤ 24548828356703^71*2000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      635680683 2000000000 24548828356703 100000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3178403733/10000000000 : ℝ)^87 ≤ (2454883136631/10000000000000 : ℝ)^71 := by
    have hnat : (3178403733 : ℕ)^87*10000000000000^71 ≤ 2454883136631^71*10000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3178403733 10000000000 2454883136631 10000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (87/16 : ℝ)) 87 71 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1440824371/2500000000 : ℝ), (-635680683/2000000000 : ℝ), (3178403733/10000000000 : ℝ)] ![(12725585065703/25000000000000 : ℝ), (24548828356703/100000000000000 : ℝ), (2454883136631/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1440824371/2500000000 : ℝ)|^87 ≤ (12725585065703/25000000000000 : ℝ)^71
        have hw : |(1440824371/2500000000 : ℝ)|=(1440824371/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-635680683/2000000000 : ℝ)|^87 ≤ (24548828356703/100000000000000 : ℝ)^71
        have hw : |(-635680683/2000000000 : ℝ)|=(635680683/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3178403733/10000000000 : ℝ)|^87 ≤ (2454883136631/10000000000000 : ℝ)^71
        have hw : |(3178403733/10000000000 : ℝ)|=(3178403733/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c325040_s0_6 (p : ℝ) (hpa : (85/16 : ℝ) ≤ p) (hpb : p ≤ (87/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1440824371/2500000000 : ℝ)*x 0 + (-635680683/2000000000 : ℝ)*x 1 + (-3178403733/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1440824371/2500000000 : ℝ)^87 ≤ (12725585065703/25000000000000 : ℝ)^71 := by
    have hnat : (1440824371 : ℕ)^87*25000000000000^71 ≤ 12725585065703^71*2500000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1440824371 2500000000 12725585065703 25000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (635680683/2000000000 : ℝ)^87 ≤ (24548828356703/100000000000000 : ℝ)^71 := by
    have hnat : (635680683 : ℕ)^87*100000000000000^71 ≤ 24548828356703^71*2000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      635680683 2000000000 24548828356703 100000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3178403733/10000000000 : ℝ)^87 ≤ (2454883136631/10000000000000 : ℝ)^71 := by
    have hnat : (3178403733 : ℕ)^87*10000000000000^71 ≤ 2454883136631^71*10000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3178403733 10000000000 2454883136631 10000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (87/16 : ℝ)) 87 71 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1440824371/2500000000 : ℝ), (-635680683/2000000000 : ℝ), (-3178403733/10000000000 : ℝ)] ![(12725585065703/25000000000000 : ℝ), (24548828356703/100000000000000 : ℝ), (2454883136631/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1440824371/2500000000 : ℝ)|^87 ≤ (12725585065703/25000000000000 : ℝ)^71
        have hw : |(1440824371/2500000000 : ℝ)|=(1440824371/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-635680683/2000000000 : ℝ)|^87 ≤ (24548828356703/100000000000000 : ℝ)^71
        have hw : |(-635680683/2000000000 : ℝ)|=(635680683/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3178403733/10000000000 : ℝ)|^87 ≤ (2454883136631/10000000000000 : ℝ)^71
        have hw : |(-3178403733/10000000000 : ℝ)|=(3178403733/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c325040 (p : ℝ) (hpa : (85/16 : ℝ) ≤ p) (hpb : p ≤ (87/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (200939/100000 : ℝ) (33069/20000 : ℝ) (81317/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![false, false, false]]) : False := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (81317/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (81317/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (81317/100000 : ℝ)*P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (81317/100000 : ℝ)*P 1 ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (81317/100000 : ℝ)*P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (81317/100000 : ℝ)*P 2 ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((-1 : ℝ)*(X 0 1+X 1 1)) ∧ ((-1 : ℝ)*(X 0 1+X 1 1)) ≤ ((-1 : ℝ)*(X 0 0+X 1 0)) ∧ ((-1 : ℝ)*(X 0 0+X 1 0)) ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((-1 : ℝ)*pair X 2 1) ∧ ((-1 : ℝ)*pair X 2 1) ≤ ((-1 : ℝ)*pair X 2 0) ∧ ((-1 : ℝ)*pair X 2 0) ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base5 : ((1 : ℝ)*N 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 2]
  have base10 : ((-1 : ℝ)*X 0 1+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 1).1]
  have base15 : ((1 : ℝ)*X 1 0+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 0).2]
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base49 : ((-1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.1]
  have base50 : ((-1 : ℝ)*X 0 0+(1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 0+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
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
  have s0_pow0 : (1 : ℝ) ^ (85/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^85 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^85*1^16 ≤ 1^16*1^85 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 85 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 85 16 (by norm_num) hpowers
    exact h
  have s0_corner0a : (2 : ℝ) ≤ (11393691857257931/10000000000000000 : ℝ) ^ (85/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (11393691857257931/10000000000000000 : ℝ)^85 := by
      have hnat : (2 : ℕ)^16*10000000000000000^85 ≤ 11393691857257931^85*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 11393691857257931 10000000000000000 16 85 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11393691857257931/10000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 85 16 (by norm_num) hpowers
    exact h
  have s0_corner0b : (3 : ℝ) ≤ (6148668287254881/5000000000000000 : ℝ) ^ (85/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (6148668287254881/5000000000000000 : ℝ)^85 := by
      have hnat : (3 : ℕ)^16*5000000000000000^85 ≤ 6148668287254881^85*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 6148668287254881 5000000000000000 16 85 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (6148668287254881/5000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 85 16 (by norm_num) hpowers
    exact h
  have major_s0_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(1393691857257931/10000000000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(903644717251831/10000000000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (85/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (1393691857257931/10000000000000000 : ℝ)) (beta := (903644717251831/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow0,s0_corner0a]) (by linarith only [s0_pow0,s0_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![false, false, false]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (1 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order0.2.2])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(1393691857257931/10000000000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(903644717251831/10000000000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow1 : (1 : ℝ) ^ (85/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^85 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^85*1^16 ≤ 1^16*1^85 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 85 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 85 16 (by norm_num) hpowers
    exact h
  have s0_corner1a : (2 : ℝ) ≤ (11393691857257931/10000000000000000 : ℝ) ^ (85/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (11393691857257931/10000000000000000 : ℝ)^85 := by
      have hnat : (2 : ℕ)^16*10000000000000000^85 ≤ 11393691857257931^85*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 11393691857257931 10000000000000000 16 85 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11393691857257931/10000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 85 16 (by norm_num) hpowers
    exact h
  have s0_corner1b : (3 : ℝ) ≤ (6148668287254881/5000000000000000 : ℝ) ^ (85/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (6148668287254881/5000000000000000 : ℝ)^85 := by
      have hnat : (3 : ℕ)^16*5000000000000000^85 ≤ 6148668287254881^85*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 6148668287254881 5000000000000000 16 85 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (6148668287254881/5000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 85 16 (by norm_num) hpowers
    exact h
  have major_s0_1 : P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1))+(1393691857257931/10000000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(903644717251831/10000000000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (85/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (1393691857257931/10000000000000000 : ℝ)) (beta := (903644717251831/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow1,s0_corner1a]) (by linarith only [s0_pow1,s0_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![false, false, false]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (1 : ℝ)*((-1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order1.2.2])
    change lpNorm p (pair X 1) ≤ ((-1 : ℝ)*pair X 1 1)+(1393691857257931/10000000000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(903644717251831/10000000000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow2 : (1 : ℝ) ^ (85/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^85 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^85*1^16 ≤ 1^16*1^85 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 85 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 85 16 (by norm_num) hpowers
    exact h
  have s0_corner2a : (2 : ℝ) ≤ (11393691857257931/10000000000000000 : ℝ) ^ (85/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (11393691857257931/10000000000000000 : ℝ)^85 := by
      have hnat : (2 : ℕ)^16*10000000000000000^85 ≤ 11393691857257931^85*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 11393691857257931 10000000000000000 16 85 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11393691857257931/10000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 85 16 (by norm_num) hpowers
    exact h
  have s0_corner2b : (3 : ℝ) ≤ (6148668287254881/5000000000000000 : ℝ) ^ (85/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (6148668287254881/5000000000000000 : ℝ)^85 := by
      have hnat : (3 : ℕ)^16*5000000000000000^85 ≤ 6148668287254881^85*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 6148668287254881 5000000000000000 16 85 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (6148668287254881/5000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 85 16 (by norm_num) hpowers
    exact h
  have major_s0_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(1393691857257931/10000000000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 1 0))+(903644717251831/10000000000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (85/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (1393691857257931/10000000000000000 : ℝ)) (beta := (903644717251831/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow2,s0_corner2a]) (by linarith only [s0_pow2,s0_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![false, false, false]] hX 2 (by
        change ((-1 : ℝ)*pair X 2 0) ≤ (1 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order2.2.2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(1393691857257931/10000000000000000 : ℝ)*((-1 : ℝ)*pair X 2 0)+(903644717251831/10000000000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s0_0 : ((-2908958317/10000000000 : ℝ)*X 0 0+(-463621473/1000000000 : ℝ)*X 0 1+(-4636215193/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c325040_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_1 : ((2908958317/10000000000 : ℝ)*X 1 0+(463621473/1000000000 : ℝ)*X 1 1+(-4636215193/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c325040_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_2 : ((1440824371/2500000000 : ℝ)*X 2 0+(-635680683/2000000000 : ℝ)*X 2 1+(3178403733/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c325040_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_6 : ((1440824371/2500000000 : ℝ)*X 0 0+(-635680683/2000000000 : ℝ)*X 0 1+(-3178403733/10000000000 : ℝ)*X 0 2+(1440824371/2500000000 : ℝ)*X 1 0+(-635680683/2000000000 : ℝ)*X 1 1+(-3178403733/10000000000 : ℝ)*X 1 2+(1440824371/2500000000 : ℝ)*X 2 0+(-635680683/2000000000 : ℝ)*X 2 1+(-3178403733/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c325040_s0_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have hsep : (-452817/50000 : ℝ) < ((-200939/100000 : ℝ)*P 0+(-200939/100000 : ℝ)*P 1+(-200939/100000 : ℝ)*P 2+(1 : ℝ)*T) := by
    have hcertificate_margin : (-452817/50000 : ℝ) < (-11146662481797936300519/1250000000000000000000 : ℝ) := by norm_num
    linear_combination (799632882969/1000000000000 : ℝ)*(base5) + (100393/250000000000 : ℝ)*(base10) + (2943/20000000000 : ℝ)*(base15) + (213194839727/250000000000 : ℝ)*(base39) + (233370103891/500000000000 : ℝ)*(base40) + (386039485011/1000000000000 : ℝ)*(base49) + (215929/1000000000000 : ℝ)*(base50) + (149838788637/200000000000 : ℝ)*(base60) + (200939/100000 : ℝ)*(major_s0_0) + (200939/100000 : ℝ)*(major_s0_1) + (200939/100000 : ℝ)*(major_s0_2) + (594488585381/200000000000 : ℝ)*(sp_s0_0) + (2972443181327/1000000000000 : ℝ)*(sp_s0_1) + (1886038105723/500000000000 : ℝ)*(sp_s0_2) + (200367117031/1000000000000 : ℝ)*(sp_s0_6) + (2972443328477/1000000000000 : ℝ)*(f.sum) + (7026968881/10000000000000000000000 : ℝ)*base63 + (93892863/400000000000000000000 : ℝ)*base64 + (1392218739/5000000000000000000000 : ℝ)*base67 + (2274431247/10000000000000000000000 : ℝ)*base69 + (881201369/2000000000000000000000 : ℝ)*base70 + (518432269/2500000000000000000000 : ℝ)*base72 + (717160111/5000000000000000000000 : ℝ)*base75 + (155504209/2000000000000000000000 : ℝ)*base77 + (274413003/2000000000000000000000 : ℝ)*base78 + hcertificate_margin
  linarith only [hsep,f.failure]

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
namespace HlawkaSchatten.DiagonalCutoff4
theorem coarse_distinct_p025_b019 (p : ℝ) (hpa : (85/16 : ℝ) ≤ p) (hpb : p ≤ (87/16 : ℝ))
    (c : Fin 88) (hlo : 39 ≤ c.val) (hhi : c.val < 41)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (200939/100000 : ℝ) (33069/20000 : ℝ) (81317/100000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  have hc : c=39 ∨ c=40 := by omega
  rcases hc with rfl|rfl
  · exact collision_c325039 p hpa (by linarith only [hpb]) X hX
  · exact collision_c325040 p hpa (by linarith only [hpb]) X hX

end HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p : ℝ) (hpa : (85/16 : ℝ) ≤ p) (hpb : p ≤ (87/16 : ℝ))
    (c : Fin 88) (hlo : 39 ≤ c.val) (hhi : c.val < 41)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (200939/100000 : ℝ) (33069/20000 : ℝ) (81317/100000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  exact HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p025_b019 p hpa hpb c hlo hhi hn63 hn87 X hX

#print axioms solution
