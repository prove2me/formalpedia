-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p025_b024
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T02:02:48.237155+00:00
-- url     : https://prove2.me/submissions/b9745299-3a40-4eff-a48d-42243f6b0bc8

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
theorem collision_support_c325048_s0_0 (p : ℝ) (hpa : (85/16 : ℝ) ≤ p) (hpb : p ≤ (87/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-2426730047/10000000000 : ℝ)*x 0 + (151670623/625000000 : ℝ)*x 1 + (-7011621133/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2426730047/10000000000 : ℝ)^87 ≤ (1763740777667/10000000000000 : ℝ)^71 := by
    have hnat : (2426730047 : ℕ)^87*10000000000000^71 ≤ 1763740777667^71*10000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2426730047 10000000000 1763740777667 10000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (151670623/625000000 : ℝ)^87 ≤ (1763740707311/10000000000000 : ℝ)^71 := by
    have hnat : (151670623 : ℕ)^87*10000000000000^71 ≤ 1763740707311^71*625000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      151670623 625000000 1763740707311 10000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (7011621133/10000000000 : ℝ)^87 ≤ (64725185135953/100000000000000 : ℝ)^71 := by
    have hnat : (7011621133 : ℕ)^87*100000000000000^71 ≤ 64725185135953^71*10000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7011621133 10000000000 64725185135953 100000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (87/16 : ℝ)) 87 71 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2426730047/10000000000 : ℝ), (151670623/625000000 : ℝ), (-7011621133/10000000000 : ℝ)] ![(1763740777667/10000000000000 : ℝ), (1763740707311/10000000000000 : ℝ), (64725185135953/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2426730047/10000000000 : ℝ)|^87 ≤ (1763740777667/10000000000000 : ℝ)^71
        have hw : |(-2426730047/10000000000 : ℝ)|=(2426730047/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(151670623/625000000 : ℝ)|^87 ≤ (1763740707311/10000000000000 : ℝ)^71
        have hw : |(151670623/625000000 : ℝ)|=(151670623/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-7011621133/10000000000 : ℝ)|^87 ≤ (64725185135953/100000000000000 : ℝ)^71
        have hw : |(-7011621133/10000000000 : ℝ)|=(7011621133/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c325048_s0_1 (p : ℝ) (hpa : (85/16 : ℝ) ≤ p) (hpb : p ≤ (87/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3204667183/10000000000 : ℝ)*x 0 + (-1602333539/5000000000 : ℝ)*x 1 + (-5717278863/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3204667183/10000000000 : ℝ)^87 ≤ (24797624129493/100000000000000 : ℝ)^71 := by
    have hnat : (3204667183 : ℕ)^87*100000000000000^71 ≤ 24797624129493^71*10000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3204667183 10000000000 24797624129493 100000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1602333539/5000000000 : ℝ)^87 ≤ (2479762313391/10000000000000 : ℝ)^71 := by
    have hnat : (1602333539 : ℕ)^87*10000000000000^71 ≤ 2479762313391^71*5000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1602333539 5000000000 2479762313391 10000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5717278863/10000000000 : ℝ)^87 ≤ (25202376359397/50000000000000 : ℝ)^71 := by
    have hnat : (5717278863 : ℕ)^87*50000000000000^71 ≤ 25202376359397^71*10000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5717278863 10000000000 25202376359397 50000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (87/16 : ℝ)) 87 71 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3204667183/10000000000 : ℝ), (-1602333539/5000000000 : ℝ), (-5717278863/10000000000 : ℝ)] ![(24797624129493/100000000000000 : ℝ), (2479762313391/10000000000000 : ℝ), (25202376359397/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3204667183/10000000000 : ℝ)|^87 ≤ (24797624129493/100000000000000 : ℝ)^71
        have hw : |(3204667183/10000000000 : ℝ)|=(3204667183/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1602333539/5000000000 : ℝ)|^87 ≤ (2479762313391/10000000000000 : ℝ)^71
        have hw : |(-1602333539/5000000000 : ℝ)|=(1602333539/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-5717278863/10000000000 : ℝ)|^87 ≤ (25202376359397/50000000000000 : ℝ)^71
        have hw : |(-5717278863/10000000000 : ℝ)|=(5717278863/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c325048_s0_7 (p : ℝ) (hpa : (85/16 : ℝ) ≤ p) (hpb : p ≤ (87/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-1542269221/10000000000 : ℝ)*x 0 + (96026147/1000000000 : ℝ)*x 1 + (-8691909569/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1542269221/10000000000 : ℝ)^87 ≤ (506034794781/5000000000000 : ℝ)^71 := by
    have hnat : (1542269221 : ℕ)^87*5000000000000^71 ≤ 506034794781^71*10000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1542269221 10000000000 506034794781 5000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (96026147/1000000000 : ℝ)^87 ≤ (1415822587911/25000000000000 : ℝ)^71 := by
    have hnat : (96026147 : ℕ)^87*25000000000000^71 ≤ 1415822587911^71*1000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      96026147 1000000000 1415822587911 25000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (8691909569/10000000000 : ℝ)^87 ≤ (10527001717319/12500000000000 : ℝ)^71 := by
    have hnat : (8691909569 : ℕ)^87*12500000000000^71 ≤ 10527001717319^71*10000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8691909569 10000000000 10527001717319 12500000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (87/16 : ℝ)) 87 71 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1542269221/10000000000 : ℝ), (96026147/1000000000 : ℝ), (-8691909569/10000000000 : ℝ)] ![(506034794781/5000000000000 : ℝ), (1415822587911/25000000000000 : ℝ), (10527001717319/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1542269221/10000000000 : ℝ)|^87 ≤ (506034794781/5000000000000 : ℝ)^71
        have hw : |(-1542269221/10000000000 : ℝ)|=(1542269221/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(96026147/1000000000 : ℝ)|^87 ≤ (1415822587911/25000000000000 : ℝ)^71
        have hw : |(96026147/1000000000 : ℝ)|=(96026147/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-8691909569/10000000000 : ℝ)|^87 ≤ (10527001717319/12500000000000 : ℝ)^71
        have hw : |(-8691909569/10000000000 : ℝ)|=(8691909569/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c325048_s0_8 (p : ℝ) (hpa : (85/16 : ℝ) ≤ p) (hpb : p ≤ (87/16 : ℝ)) (x : Fin 3 → ℝ) :
    (694880953/2500000000 : ℝ)*x 0 + (-181201637/1000000000 : ℝ)*x 1 + (-7198059119/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (694880953/2500000000 : ℝ)^87 ≤ (5207244408797/25000000000000 : ℝ)^71 := by
    have hnat : (694880953 : ℕ)^87*25000000000000^71 ≤ 5207244408797^71*2500000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      694880953 2500000000 5207244408797 25000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (181201637/1000000000 : ℝ)^87 ≤ (6165345043991/50000000000000 : ℝ)^71 := by
    have hnat : (181201637 : ℕ)^87*50000000000000^71 ≤ 6165345043991^71*1000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      181201637 1000000000 6165345043991 50000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (7198059119/10000000000 : ℝ)^87 ≤ (66840332261829/100000000000000 : ℝ)^71 := by
    have hnat : (7198059119 : ℕ)^87*100000000000000^71 ≤ 66840332261829^71*10000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7198059119 10000000000 66840332261829 100000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (87/16 : ℝ)) 87 71 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(694880953/2500000000 : ℝ), (-181201637/1000000000 : ℝ), (-7198059119/10000000000 : ℝ)] ![(5207244408797/25000000000000 : ℝ), (6165345043991/50000000000000 : ℝ), (66840332261829/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(694880953/2500000000 : ℝ)|^87 ≤ (5207244408797/25000000000000 : ℝ)^71
        have hw : |(694880953/2500000000 : ℝ)|=(694880953/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-181201637/1000000000 : ℝ)|^87 ≤ (6165345043991/50000000000000 : ℝ)^71
        have hw : |(-181201637/1000000000 : ℝ)|=(181201637/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-7198059119/10000000000 : ℝ)|^87 ≤ (66840332261829/100000000000000 : ℝ)^71
        have hw : |(-7198059119/10000000000 : ℝ)|=(7198059119/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c325048_s0_9 (p : ℝ) (hpa : (85/16 : ℝ) ≤ p) (hpb : p ≤ (87/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3698368327/10000000000 : ℝ)*x 0 + (7483750243/10000000000 : ℝ)*x 1 + (1201723/125000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3698368327/10000000000 : ℝ)^87 ≤ (14778499547137/50000000000000 : ℝ)^71 := by
    have hnat : (3698368327 : ℕ)^87*50000000000000^71 ≤ 14778499547137^71*10000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3698368327 10000000000 14778499547137 50000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (7483750243/10000000000 : ℝ)^87 ≤ (70105453050287/100000000000000 : ℝ)^71 := by
    have hnat : (7483750243 : ℕ)^87*100000000000000^71 ≤ 70105453050287^71*10000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7483750243 10000000000 70105453050287 100000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1201723/125000000 : ℝ)^87 ≤ (42193480937/12500000000000 : ℝ)^71 := by
    have hnat : (1201723 : ℕ)^87*12500000000000^71 ≤ 42193480937^71*125000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1201723 125000000 42193480937 12500000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (87/16 : ℝ)) 87 71 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3698368327/10000000000 : ℝ), (7483750243/10000000000 : ℝ), (1201723/125000000 : ℝ)] ![(14778499547137/50000000000000 : ℝ), (70105453050287/100000000000000 : ℝ), (42193480937/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3698368327/10000000000 : ℝ)|^87 ≤ (14778499547137/50000000000000 : ℝ)^71
        have hw : |(3698368327/10000000000 : ℝ)|=(3698368327/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(7483750243/10000000000 : ℝ)|^87 ≤ (70105453050287/100000000000000 : ℝ)^71
        have hw : |(7483750243/10000000000 : ℝ)|=(7483750243/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1201723/125000000 : ℝ)|^87 ≤ (42193480937/12500000000000 : ℝ)^71
        have hw : |(1201723/125000000 : ℝ)|=(1201723/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c325048_s0_13 (p : ℝ) (hpa : (85/16 : ℝ) ≤ p) (hpb : p ≤ (87/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3638167961/10000000000 : ℝ)*x 0 + (7483750243/10000000000 : ℝ)*x 1 + (-6845683/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3638167961/10000000000 : ℝ)^87 ≤ (3621068636697/12500000000000 : ℝ)^71 := by
    have hnat : (3638167961 : ℕ)^87*12500000000000^71 ≤ 3621068636697^71*10000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3638167961 10000000000 3621068636697 12500000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (7483750243/10000000000 : ℝ)^87 ≤ (70105453050287/100000000000000 : ℝ)^71 := by
    have hnat : (7483750243 : ℕ)^87*100000000000000^71 ≤ 70105453050287^71*10000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7483750243 10000000000 70105453050287 100000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6845683/312500000 : ℝ)^87 ≤ (46299892367/5000000000000 : ℝ)^71 := by
    have hnat : (6845683 : ℕ)^87*5000000000000^71 ≤ 46299892367^71*312500000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6845683 312500000 46299892367 5000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (87/16 : ℝ)) 87 71 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3638167961/10000000000 : ℝ), (7483750243/10000000000 : ℝ), (-6845683/312500000 : ℝ)] ![(3621068636697/12500000000000 : ℝ), (70105453050287/100000000000000 : ℝ), (46299892367/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3638167961/10000000000 : ℝ)|^87 ≤ (3621068636697/12500000000000 : ℝ)^71
        have hw : |(3638167961/10000000000 : ℝ)|=(3638167961/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(7483750243/10000000000 : ℝ)|^87 ≤ (70105453050287/100000000000000 : ℝ)^71
        have hw : |(7483750243/10000000000 : ℝ)|=(7483750243/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-6845683/312500000 : ℝ)|^87 ≤ (46299892367/5000000000000 : ℝ)^71
        have hw : |(-6845683/312500000 : ℝ)|=(6845683/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c325048_s0_14 (p : ℝ) (hpa : (85/16 : ℝ) ≤ p) (hpb : p ≤ (87/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-39570747/400000000 : ℝ)*x 0 + (1535263337/10000000000 : ℝ)*x 1 + (-4339466873/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (39570747/400000000 : ℝ)^87 ≤ (5873624825893/100000000000000 : ℝ)^71 := by
    have hnat : (39570747 : ℕ)^87*100000000000000^71 ≤ 5873624825893^71*400000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      39570747 400000000 5873624825893 100000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1535263337/10000000000 : ℝ)^87 ≤ (10064390317441/100000000000000 : ℝ)^71 := by
    have hnat : (1535263337 : ℕ)^87*100000000000000^71 ≤ 10064390317441^71*10000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1535263337 10000000000 10064390317441 100000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4339466873/5000000000 : ℝ)^87 ≤ (84061984839477/100000000000000 : ℝ)^71 := by
    have hnat : (4339466873 : ℕ)^87*100000000000000^71 ≤ 84061984839477^71*5000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4339466873 5000000000 84061984839477 100000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (87/16 : ℝ)) 87 71 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-39570747/400000000 : ℝ), (1535263337/10000000000 : ℝ), (-4339466873/5000000000 : ℝ)] ![(5873624825893/100000000000000 : ℝ), (10064390317441/100000000000000 : ℝ), (84061984839477/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-39570747/400000000 : ℝ)|^87 ≤ (5873624825893/100000000000000 : ℝ)^71
        have hw : |(-39570747/400000000 : ℝ)|=(39570747/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1535263337/10000000000 : ℝ)|^87 ≤ (10064390317441/100000000000000 : ℝ)^71
        have hw : |(1535263337/10000000000 : ℝ)|=(1535263337/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-4339466873/5000000000 : ℝ)|^87 ≤ (84061984839477/100000000000000 : ℝ)^71
        have hw : |(-4339466873/5000000000 : ℝ)|=(4339466873/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c325048_s0_15 (p : ℝ) (hpa : (85/16 : ℝ) ≤ p) (hpb : p ≤ (87/16 : ℝ)) (x : Fin 3 → ℝ) :
    (27698823/156250000 : ℝ)*x 0 + (-2788977083/10000000000 : ℝ)*x 1 + (-7219143749/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (27698823/156250000 : ℝ)^87 ≤ (7502414133/62500000000 : ℝ)^71 := by
    have hnat : (27698823 : ℕ)^87*62500000000^71 ≤ 7502414133^71*156250000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      27698823 156250000 7502414133 62500000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2788977083/10000000000 : ℝ)^87 ≤ (10457907518163/50000000000000 : ℝ)^71 := by
    have hnat : (2788977083 : ℕ)^87*50000000000000^71 ≤ 10457907518163^71*10000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2788977083 10000000000 10457907518163 50000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (7219143749/10000000000 : ℝ)^87 ≤ (67080322339793/100000000000000 : ℝ)^71 := by
    have hnat : (7219143749 : ℕ)^87*100000000000000^71 ≤ 67080322339793^71*10000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7219143749 10000000000 67080322339793 100000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (87/16 : ℝ)) 87 71 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(27698823/156250000 : ℝ), (-2788977083/10000000000 : ℝ), (-7219143749/10000000000 : ℝ)] ![(7502414133/62500000000 : ℝ), (10457907518163/50000000000000 : ℝ), (67080322339793/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(27698823/156250000 : ℝ)|^87 ≤ (7502414133/62500000000 : ℝ)^71
        have hw : |(27698823/156250000 : ℝ)|=(27698823/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2788977083/10000000000 : ℝ)|^87 ≤ (10457907518163/50000000000000 : ℝ)^71
        have hw : |(-2788977083/10000000000 : ℝ)|=(2788977083/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-7219143749/10000000000 : ℝ)|^87 ≤ (67080322339793/100000000000000 : ℝ)^71
        have hw : |(-7219143749/10000000000 : ℝ)|=(7219143749/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c325048_s0_16 (p : ℝ) (hpa : (85/16 : ℝ) ≤ p) (hpb : p ≤ (87/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3747834203/5000000000 : ℝ)*x 0 + (183750161/500000000 : ℝ)*x 1 + (23399171/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3747834203/5000000000 : ℝ)^87 ≤ (70242282830989/100000000000000 : ℝ)^71 := by
    have hnat : (3747834203 : ℕ)^87*100000000000000^71 ≤ 70242282830989^71*5000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3747834203 5000000000 70242282830989 100000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (183750161/500000000 : ℝ)^87 ≤ (14664175105137/50000000000000 : ℝ)^71 := by
    have hnat : (183750161 : ℕ)^87*50000000000000^71 ≤ 14664175105137^71*500000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      183750161 500000000 14664175105137 50000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (23399171/2000000000 : ℝ)^87 ≤ (429366948829/100000000000000 : ℝ)^71 := by
    have hnat : (23399171 : ℕ)^87*100000000000000^71 ≤ 429366948829^71*2000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      23399171 2000000000 429366948829 100000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (87/16 : ℝ)) 87 71 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3747834203/5000000000 : ℝ), (183750161/500000000 : ℝ), (23399171/2000000000 : ℝ)] ![(70242282830989/100000000000000 : ℝ), (14664175105137/50000000000000 : ℝ), (429366948829/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3747834203/5000000000 : ℝ)|^87 ≤ (70242282830989/100000000000000 : ℝ)^71
        have hw : |(3747834203/5000000000 : ℝ)|=(3747834203/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(183750161/500000000 : ℝ)|^87 ≤ (14664175105137/50000000000000 : ℝ)^71
        have hw : |(183750161/500000000 : ℝ)|=(183750161/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(23399171/2000000000 : ℝ)|^87 ≤ (429366948829/100000000000000 : ℝ)^71
        have hw : |(23399171/2000000000 : ℝ)|=(23399171/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c325048_s0_19 (p : ℝ) (hpa : (85/16 : ℝ) ≤ p) (hpb : p ≤ (87/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3733775189/5000000000 : ℝ)*x 0 + (183750161/500000000 : ℝ)*x 1 + (-184862137/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3733775189/5000000000 : ℝ)^87 ≤ (34959772367613/50000000000000 : ℝ)^71 := by
    have hnat : (3733775189 : ℕ)^87*50000000000000^71 ≤ 34959772367613^71*5000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3733775189 5000000000 34959772367613 50000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (183750161/500000000 : ℝ)^87 ≤ (14664175105137/50000000000000 : ℝ)^71 := by
    have hnat : (183750161 : ℕ)^87*50000000000000^71 ≤ 14664175105137^71*500000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      183750161 500000000 14664175105137 50000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (184862137/10000000000 : ℝ)^87 ≤ (376052518651/50000000000000 : ℝ)^71 := by
    have hnat : (184862137 : ℕ)^87*50000000000000^71 ≤ 376052518651^71*10000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      184862137 10000000000 376052518651 50000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (87/16 : ℝ)) 87 71 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3733775189/5000000000 : ℝ), (183750161/500000000 : ℝ), (-184862137/10000000000 : ℝ)] ![(34959772367613/50000000000000 : ℝ), (14664175105137/50000000000000 : ℝ), (376052518651/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3733775189/5000000000 : ℝ)|^87 ≤ (34959772367613/50000000000000 : ℝ)^71
        have hw : |(3733775189/5000000000 : ℝ)|=(3733775189/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(183750161/500000000 : ℝ)|^87 ≤ (14664175105137/50000000000000 : ℝ)^71
        have hw : |(183750161/500000000 : ℝ)|=(183750161/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-184862137/10000000000 : ℝ)|^87 ≤ (376052518651/50000000000000 : ℝ)^71
        have hw : |(-184862137/10000000000 : ℝ)|=(184862137/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c325048_s0_20 (p : ℝ) (hpa : (85/16 : ℝ) ≤ p) (hpb : p ≤ (87/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-69945391/200000000 : ℝ)*x 0 + (1498573023/10000000000 : ℝ)*x 1 + (-1706450577/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (69945391/200000000 : ℝ)^87 ≤ (13799949627529/50000000000000 : ℝ)^71 := by
    have hnat : (69945391 : ℕ)^87*50000000000000^71 ≤ 13799949627529^71*200000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      69945391 200000000 13799949627529 50000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1498573023/10000000000 : ℝ)^87 ≤ (9770463930721/100000000000000 : ℝ)^71 := by
    have hnat : (1498573023 : ℕ)^87*100000000000000^71 ≤ 9770463930721^71*10000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1498573023 10000000000 9770463930721 100000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1706450577/2500000000 : ℝ)^87 ≤ (7828704599499/12500000000000 : ℝ)^71 := by
    have hnat : (1706450577 : ℕ)^87*12500000000000^71 ≤ 7828704599499^71*2500000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1706450577 2500000000 7828704599499 12500000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (87/16 : ℝ)) 87 71 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-69945391/200000000 : ℝ), (1498573023/10000000000 : ℝ), (-1706450577/2500000000 : ℝ)] ![(13799949627529/50000000000000 : ℝ), (9770463930721/100000000000000 : ℝ), (7828704599499/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-69945391/200000000 : ℝ)|^87 ≤ (13799949627529/50000000000000 : ℝ)^71
        have hw : |(-69945391/200000000 : ℝ)|=(69945391/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1498573023/10000000000 : ℝ)|^87 ≤ (9770463930721/100000000000000 : ℝ)^71
        have hw : |(1498573023/10000000000 : ℝ)|=(1498573023/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1706450577/2500000000 : ℝ)|^87 ≤ (7828704599499/12500000000000 : ℝ)^71
        have hw : |(-1706450577/2500000000 : ℝ)|=(1706450577/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c325048_s0_21 (p : ℝ) (hpa : (85/16 : ℝ) ≤ p) (hpb : p ≤ (87/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2274031187/10000000000 : ℝ)*x 0 + (-2136364443/5000000000 : ℝ)*x 1 + (-5534401923/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2274031187/10000000000 : ℝ)^87 ≤ (1628730128367/10000000000000 : ℝ)^71 := by
    have hnat : (2274031187 : ℕ)^87*10000000000000^71 ≤ 1628730128367^71*10000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2274031187 10000000000 1628730128367 10000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2136364443/5000000000 : ℝ)^87 ≤ (35276379348777/100000000000000 : ℝ)^71 := by
    have hnat : (2136364443 : ℕ)^87*100000000000000^71 ≤ 35276379348777^71*5000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2136364443 5000000000 35276379348777 100000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5534401923/10000000000 : ℝ)^87 ≤ (24218159680063/50000000000000 : ℝ)^71 := by
    have hnat : (5534401923 : ℕ)^87*50000000000000^71 ≤ 24218159680063^71*10000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5534401923 10000000000 24218159680063 50000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (87/16 : ℝ)) 87 71 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2274031187/10000000000 : ℝ), (-2136364443/5000000000 : ℝ), (-5534401923/10000000000 : ℝ)] ![(1628730128367/10000000000000 : ℝ), (35276379348777/100000000000000 : ℝ), (24218159680063/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2274031187/10000000000 : ℝ)|^87 ≤ (1628730128367/10000000000000 : ℝ)^71
        have hw : |(2274031187/10000000000 : ℝ)|=(2274031187/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2136364443/5000000000 : ℝ)|^87 ≤ (35276379348777/100000000000000 : ℝ)^71
        have hw : |(-2136364443/5000000000 : ℝ)|=(2136364443/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-5534401923/10000000000 : ℝ)|^87 ≤ (24218159680063/50000000000000 : ℝ)^71
        have hw : |(-5534401923/10000000000 : ℝ)|=(5534401923/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c325048_s0_22 (p : ℝ) (hpa : (85/16 : ℝ) ≤ p) (hpb : p ≤ (87/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5671186141/10000000000 : ℝ)*x 0 + (1417796497/2500000000 : ℝ)*x 1 + (58972873/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5671186141/10000000000 : ℝ)^87 ≤ (24953633935493/50000000000000 : ℝ)^71 := by
    have hnat : (5671186141 : ℕ)^87*50000000000000^71 ≤ 24953633935493^71*10000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5671186141 10000000000 24953633935493 50000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1417796497/2500000000 : ℝ)^87 ≤ (9981453244229/20000000000000 : ℝ)^71 := by
    have hnat : (1417796497 : ℕ)^87*20000000000000^71 ≤ 9981453244229^71*2500000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1417796497 2500000000 9981453244229 20000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (58972873/10000000000 : ℝ)^87 ≤ (23183237359/12500000000000 : ℝ)^71 := by
    have hnat : (58972873 : ℕ)^87*12500000000000^71 ≤ 23183237359^71*10000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      58972873 10000000000 23183237359 12500000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (87/16 : ℝ)) 87 71 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5671186141/10000000000 : ℝ), (1417796497/2500000000 : ℝ), (58972873/10000000000 : ℝ)] ![(24953633935493/50000000000000 : ℝ), (9981453244229/20000000000000 : ℝ), (23183237359/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5671186141/10000000000 : ℝ)|^87 ≤ (24953633935493/50000000000000 : ℝ)^71
        have hw : |(5671186141/10000000000 : ℝ)|=(5671186141/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1417796497/2500000000 : ℝ)|^87 ≤ (9981453244229/20000000000000 : ℝ)^71
        have hw : |(1417796497/2500000000 : ℝ)|=(1417796497/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(58972873/10000000000 : ℝ)|^87 ≤ (23183237359/12500000000000 : ℝ)^71
        have hw : |(58972873/10000000000 : ℝ)|=(58972873/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c325048_s1_0 (p : ℝ) (hpa : (85/16 : ℝ) ≤ p) (hpb : p ≤ (87/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-2957908027/10000000000 : ℝ)*x 0 + (2957634581/10000000000 : ℝ)*x 1 + (-307166411/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2957908027/10000000000 : ℝ)^87 ≤ (22478635378989/100000000000000 : ℝ)^71 := by
    have hnat : (2957908027 : ℕ)^87*100000000000000^71 ≤ 22478635378989^71*10000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2957908027 10000000000 22478635378989 100000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2957634581/10000000000 : ℝ)^87 ≤ (280951113219/1250000000000 : ℝ)^71 := by
    have hnat : (2957634581 : ℕ)^87*1250000000000^71 ≤ 280951113219^71*10000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2957634581 10000000000 280951113219 1250000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (307166411/500000000 : ℝ)^87 ≤ (13761318886719/25000000000000 : ℝ)^71 := by
    have hnat : (307166411 : ℕ)^87*25000000000000^71 ≤ 13761318886719^71*500000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      307166411 500000000 13761318886719 25000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (87/16 : ℝ)) 87 71 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2957908027/10000000000 : ℝ), (2957634581/10000000000 : ℝ), (-307166411/500000000 : ℝ)] ![(22478635378989/100000000000000 : ℝ), (280951113219/1250000000000 : ℝ), (13761318886719/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2957908027/10000000000 : ℝ)|^87 ≤ (22478635378989/100000000000000 : ℝ)^71
        have hw : |(-2957908027/10000000000 : ℝ)|=(2957908027/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2957634581/10000000000 : ℝ)|^87 ≤ (280951113219/1250000000000 : ℝ)^71
        have hw : |(2957634581/10000000000 : ℝ)|=(2957634581/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-307166411/500000000 : ℝ)|^87 ≤ (13761318886719/25000000000000 : ℝ)^71
        have hw : |(-307166411/500000000 : ℝ)|=(307166411/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c325048_s1_1 (p : ℝ) (hpa : (85/16 : ℝ) ≤ p) (hpb : p ≤ (87/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1792895047/5000000000 : ℝ)*x 0 + (-3585458603/10000000000 : ℝ)*x 1 + (-5030244637/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1792895047/5000000000 : ℝ)^87 ≤ (7114585938583/25000000000000 : ℝ)^71 := by
    have hnat : (1792895047 : ℕ)^87*25000000000000^71 ≤ 7114585938583^71*5000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1792895047 5000000000 7114585938583 25000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3585458603/10000000000 : ℝ)^87 ≤ (5691024013449/20000000000000 : ℝ)^71 := by
    have hnat : (3585458603 : ℕ)^87*20000000000000^71 ≤ 5691024013449^71*10000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3585458603 10000000000 5691024013449 20000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5030244637/10000000000 : ℝ)^87 ≤ (43086536164443/100000000000000 : ℝ)^71 := by
    have hnat : (5030244637 : ℕ)^87*100000000000000^71 ≤ 43086536164443^71*10000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5030244637 10000000000 43086536164443 100000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (87/16 : ℝ)) 87 71 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1792895047/5000000000 : ℝ), (-3585458603/10000000000 : ℝ), (-5030244637/10000000000 : ℝ)] ![(7114585938583/25000000000000 : ℝ), (5691024013449/20000000000000 : ℝ), (43086536164443/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1792895047/5000000000 : ℝ)|^87 ≤ (7114585938583/25000000000000 : ℝ)^71
        have hw : |(1792895047/5000000000 : ℝ)|=(1792895047/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3585458603/10000000000 : ℝ)|^87 ≤ (5691024013449/20000000000000 : ℝ)^71
        have hw : |(-3585458603/10000000000 : ℝ)|=(3585458603/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-5030244637/10000000000 : ℝ)|^87 ≤ (43086536164443/100000000000000 : ℝ)^71
        have hw : |(-5030244637/10000000000 : ℝ)|=(5030244637/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c325048_s1_2 (p : ℝ) (hpa : (85/16 : ℝ) ≤ p) (hpb : p ≤ (87/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5213046807/10000000000 : ℝ)*x 0 + (5213505827/10000000000 : ℝ)*x 1 + (761702157/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5213046807/10000000000 : ℝ)^87 ≤ (9002593071309/20000000000000 : ℝ)^71 := by
    have hnat : (5213046807 : ℕ)^87*20000000000000^71 ≤ 9002593071309^71*10000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5213046807 10000000000 9002593071309 20000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5213505827/10000000000 : ℝ)^87 ≤ (11254455518451/25000000000000 : ℝ)^71 := by
    have hnat : (5213505827 : ℕ)^87*25000000000000^71 ≤ 11254455518451^71*10000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5213505827 10000000000 11254455518451 25000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (761702157/5000000000 : ℝ)^87 ≤ (9969212554167/100000000000000 : ℝ)^71 := by
    have hnat : (761702157 : ℕ)^87*100000000000000^71 ≤ 9969212554167^71*5000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      761702157 5000000000 9969212554167 100000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (87/16 : ℝ)) 87 71 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5213046807/10000000000 : ℝ), (5213505827/10000000000 : ℝ), (761702157/5000000000 : ℝ)] ![(9002593071309/20000000000000 : ℝ), (11254455518451/25000000000000 : ℝ), (9969212554167/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5213046807/10000000000 : ℝ)|^87 ≤ (9002593071309/20000000000000 : ℝ)^71
        have hw : |(5213046807/10000000000 : ℝ)|=(5213046807/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5213505827/10000000000 : ℝ)|^87 ≤ (11254455518451/25000000000000 : ℝ)^71
        have hw : |(5213505827/10000000000 : ℝ)|=(5213505827/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(761702157/5000000000 : ℝ)|^87 ≤ (9969212554167/100000000000000 : ℝ)^71
        have hw : |(761702157/5000000000 : ℝ)|=(761702157/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c325048_s1_6 (p : ℝ) (hpa : (85/16 : ℝ) ≤ p) (hpb : p ≤ (87/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4965028749/10000000000 : ℝ)*x 0 + (4965465931/10000000000 : ℝ)*x 1 + (-214812789/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4965028749/10000000000 : ℝ)^87 ≤ (21201524972483/50000000000000 : ℝ)^71 := by
    have hnat : (4965028749 : ℕ)^87*50000000000000^71 ≤ 21201524972483^71*10000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4965028749 10000000000 21201524972483 50000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4965465931/10000000000 : ℝ)^87 ≤ (21203812534187/50000000000000 : ℝ)^71 := by
    have hnat : (4965465931 : ℕ)^87*50000000000000^71 ≤ 21203812534187^71*10000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4965465931 10000000000 21203812534187 50000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (214812789/1000000000 : ℝ)^87 ≤ (303786499393/2000000000000 : ℝ)^71 := by
    have hnat : (214812789 : ℕ)^87*2000000000000^71 ≤ 303786499393^71*1000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      214812789 1000000000 303786499393 2000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (87/16 : ℝ)) 87 71 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4965028749/10000000000 : ℝ), (4965465931/10000000000 : ℝ), (-214812789/1000000000 : ℝ)] ![(21201524972483/50000000000000 : ℝ), (21203812534187/50000000000000 : ℝ), (303786499393/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4965028749/10000000000 : ℝ)|^87 ≤ (21201524972483/50000000000000 : ℝ)^71
        have hw : |(4965028749/10000000000 : ℝ)|=(4965028749/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4965465931/10000000000 : ℝ)|^87 ≤ (21203812534187/50000000000000 : ℝ)^71
        have hw : |(4965465931/10000000000 : ℝ)|=(4965465931/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-214812789/1000000000 : ℝ)|^87 ≤ (303786499393/2000000000000 : ℝ)^71
        have hw : |(-214812789/1000000000 : ℝ)|=(214812789/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c325048 (p : ℝ) (hpa : (85/16 : ℝ) ≤ p) (hpb : p ≤ (87/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (200939/100000 : ℝ) (33069/20000 : ℝ) (81317/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![false, false, false]]) : False := by
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
  have main1 : (81317/100000 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (81317/100000 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 2+X 2 2)) ∧ ((-1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 2) ∧ ((-1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
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
  have base7 : ((1 : ℝ)*T) ≤ (33069/20000 : ℝ) := by
    linarith only [f.Tcap]
  have base8 : ((-1 : ℝ)*X 0 0+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 0).1]
  have base12 : ((-1 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 2).1]
  have base15 : ((1 : ℝ)*X 1 0+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 0).2]
  have base16 : ((-1 : ℝ)*X 1 1+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 1).1]
  have base21 : ((1 : ℝ)*X 2 0+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 0).2]
  have base33 : ((-1 : ℝ)*N 1+(-1 : ℝ)*N 2+(1 : ℝ)*P 0) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 0,f.sum]
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base50 : ((-1 : ℝ)*X 0 0+(-1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 0+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.2.1]
  have base59 : ((1 : ℝ)*X 0 1+(1 : ℝ)*X 1 1) ≤ (0 : ℝ) := by
    linarith only [order2.1]
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
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![false, false, false]] hX 0 (by
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
  have major_s0_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(1393691857257931/10000000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(903644717251831/10000000000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (85/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (1393691857257931/10000000000000000 : ℝ)) (beta := (903644717251831/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow1,s0_corner1a]) (by linarith only [s0_pow1,s0_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![false, false, false]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (1 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order1.2.2])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(1393691857257931/10000000000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(903644717251831/10000000000000000 : ℝ)*((-1 : ℝ)*pair X 1 2) at hh
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
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![false, false, false]] hX 2 (by
        change ((-1 : ℝ)*pair X 2 0) ≤ (1 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order2.2.2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(1393691857257931/10000000000000000 : ℝ)*((-1 : ℝ)*pair X 2 0)+(903644717251831/10000000000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s0_0 : ((-2426730047/10000000000 : ℝ)*X 0 0+(151670623/625000000 : ℝ)*X 0 1+(-7011621133/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c325048_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_1 : ((3204667183/10000000000 : ℝ)*X 1 0+(-1602333539/5000000000 : ℝ)*X 1 1+(-5717278863/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c325048_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_7 : ((-1542269221/10000000000 : ℝ)*X 0 0+(96026147/1000000000 : ℝ)*X 0 1+(-8691909569/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c325048_s0_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_8 : ((694880953/2500000000 : ℝ)*X 1 0+(-181201637/1000000000 : ℝ)*X 1 1+(-7198059119/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c325048_s0_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_9 : ((3698368327/10000000000 : ℝ)*X 2 0+(7483750243/10000000000 : ℝ)*X 2 1+(1201723/125000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c325048_s0_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_13 : ((3638167961/10000000000 : ℝ)*X 0 0+(7483750243/10000000000 : ℝ)*X 0 1+(-6845683/312500000 : ℝ)*X 0 2+(3638167961/10000000000 : ℝ)*X 1 0+(7483750243/10000000000 : ℝ)*X 1 1+(-6845683/312500000 : ℝ)*X 1 2+(3638167961/10000000000 : ℝ)*X 2 0+(7483750243/10000000000 : ℝ)*X 2 1+(-6845683/312500000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c325048_s0_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_14 : ((-39570747/400000000 : ℝ)*X 0 0+(1535263337/10000000000 : ℝ)*X 0 1+(-4339466873/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c325048_s0_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_15 : ((27698823/156250000 : ℝ)*X 1 0+(-2788977083/10000000000 : ℝ)*X 1 1+(-7219143749/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c325048_s0_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_16 : ((3747834203/5000000000 : ℝ)*X 2 0+(183750161/500000000 : ℝ)*X 2 1+(23399171/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c325048_s0_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_19 : ((3733775189/5000000000 : ℝ)*X 0 0+(183750161/500000000 : ℝ)*X 0 1+(-184862137/10000000000 : ℝ)*X 0 2+(3733775189/5000000000 : ℝ)*X 1 0+(183750161/500000000 : ℝ)*X 1 1+(-184862137/10000000000 : ℝ)*X 1 2+(3733775189/5000000000 : ℝ)*X 2 0+(183750161/500000000 : ℝ)*X 2 1+(-184862137/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c325048_s0_19 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_20 : ((-69945391/200000000 : ℝ)*X 0 0+(1498573023/10000000000 : ℝ)*X 0 1+(-1706450577/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c325048_s0_20 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_21 : ((2274031187/10000000000 : ℝ)*X 1 0+(-2136364443/5000000000 : ℝ)*X 1 1+(-5534401923/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c325048_s0_21 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_22 : ((5671186141/10000000000 : ℝ)*X 2 0+(1417796497/2500000000 : ℝ)*X 2 1+(58972873/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c325048_s0_22 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s0_0 : (0 : ℝ) ≤ ((62767/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(62767/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (312480294796242596829/25000000000000000000000000 : ℝ) := by norm_num
    linear_combination (431055695599/500000000000 : ℝ)*(base5) + (917271921271/1000000000000 : ℝ)*(base7) + (1815046881/200000000000 : ℝ)*(base39) + (383986732479/500000000000 : ℝ)*(base59) + (967992545837/500000000000 : ℝ)*(major_s0_0) + (967992545837/500000000000 : ℝ)*(major_s0_1) + (967992545837/500000000000 : ℝ)*(major_s0_2) + (2236443/500000000000 : ℝ)*(sp_s0_0) + (6396021/1000000000000 : ℝ)*(sp_s0_1) + (240286077851/100000000000 : ℝ)*(sp_s0_7) + (300367017863/125000000000 : ℝ)*(sp_s0_8) + (3265053930123/1000000000000 : ℝ)*(sp_s0_9) + (25465739717/25000000000 : ℝ)*(sp_s0_13) + (77287529/1000000000000 : ℝ)*(sp_s0_14) + (963469058607/1000000000000 : ℝ)*(f.failure) + (96117701557/40000000000 : ℝ)*(f.sum) + (147818947/10000000000000000000000 : ℝ)*base63 + (3005210629822453/5000000000000000000000000000 : ℝ)*base65 + (2654871068677547/5000000000000000000000000000 : ℝ)*base66 + (1654770165216753/5000000000000000000000000000 : ℝ)*base69 + (14936036486057/50000000000000000000000000 : ℝ)*base71 + (3617908170822453/5000000000000000000000000000 : ℝ)*base72 + (1422086798783247/5000000000000000000000000000 : ℝ)*base75 + (878275084783247/5000000000000000000000000000 : ℝ)*base77 + (34734553/125000000000000000000 : ℝ)*base78 + (31973/100000000000000000 : ℝ)*base87 + (31973/100000000000000000 : ℝ)*base89 + (31973/100000000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s0_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(62711/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(62711/100000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (3427519538080199501523/625000000000000000000000000 : ℝ) := by norm_num
    linear_combination (28580640723/125000000000 : ℝ)*(base5) + (924502646507/1000000000000 : ℝ)*(base7) + (947/25000000000 : ℝ)*(base39) + (151845314987/1000000000000 : ℝ)*(base59) + (240995616811/125000000000 : ℝ)*(major_s0_0) + (240995616811/125000000000 : ℝ)*(major_s0_1) + (240995616811/125000000000 : ℝ)*(major_s0_2) + (1156237/500000000000 : ℝ)*(sp_s0_0) + (4082863/1000000000000 : ℝ)*(sp_s0_1) + (9785459/500000000000 : ℝ)*(sp_s0_8) + (1193454187757/500000000000 : ℝ)*(sp_s0_14) + (1193443517103/500000000000 : ℝ)*(sp_s0_15) + (2615555813771/1000000000000 : ℝ)*(sp_s0_16) + (66213409603/40000000000 : ℝ)*(sp_s0_19) + (119934714919/125000000000 : ℝ)*(f.failure) + (2386910687987/1000000000000 : ℝ)*(f.sum) + (1244465939/5000000000000000000000 : ℝ)*base63 + (402446267119059/1250000000000000000000000000 : ℝ)*base65 + (610188930994059/1250000000000000000000000000 : ℝ)*base67 + (363799892446959/1250000000000000000000000000 : ℝ)*base69 + (4496777490471/12500000000000000000000000 : ℝ)*base71 + (371527263369059/1250000000000000000000000000 : ℝ)*base72 + (381821294678041/1250000000000000000000000000 : ℝ)*base75 + (187825451678041/1250000000000000000000000000 : ℝ)*base77 + (68637893/1000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base81 + (8941/12500000000000000 : ℝ)*base87 + (8941/12500000000000000 : ℝ)*base89 + (8941/12500000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s0_2 : (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(-13899/100000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(-13899/100000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (44179356643857291/10000000000000000000000 : ℝ) := by norm_num
    linear_combination (496456368973/500000000000 : ℝ)*(base5) + (9665255309/250000000000 : ℝ)*(base7) + (3782603/1000000000000 : ℝ)*(base8) + (892763/1000000000000 : ℝ)*(base15) + (1175639/250000000000 : ℝ)*(base16) + (11358999011/500000000000 : ℝ)*(base39) + (1315696864993/1000000000000 : ℝ)*(base59) + (1917463857041/1000000000000 : ℝ)*(major_s0_0) + (1917463857041/1000000000000 : ℝ)*(major_s0_1) + (1917463857041/1000000000000 : ℝ)*(major_s0_2) + (19463/125000000000 : ℝ)*(sp_s0_9) + (2859362720259/1000000000000 : ℝ)*(sp_s0_20) + (357420113443/125000000000 : ℝ)*(sp_s0_21) + (770455817021/200000000000 : ℝ)*(sp_s0_22) + (954251716711/1000000000000 : ℝ)*(f.failure) + (1429683251431/500000000000 : ℝ)*(f.sum) + (60623731/200000000000000000000 : ℝ)*base62 + (8452715936492071/10000000000000000000000000000 : ℝ)*base64 + (6620814792507929/10000000000000000000000000000 : ℝ)*base67 + (8106759975442171/10000000000000000000000000000 : ℝ)*base68 + (4315582519501/100000000000000000000000000 : ℝ)*base71 + (8958550091492071/10000000000000000000000000000 : ℝ)*base73 + (7950331765557829/10000000000000000000000000000 : ℝ)*base74 + (8356159564557829/10000000000000000000000000000 : ℝ)*base76 + (180016159/400000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base83 + (1/1000000000000 : ℝ)*base85 + (91629/100000000000000000 : ℝ)*base87 + (91629/100000000000000000 : ℝ)*base89 + (91629/100000000000000000 : ℝ)*base91 + (1/1000000000000 : ℝ)*base92 + hcertificate_margin
  have s1_pow0 : (62767/100000 : ℝ) ^ (85/16 : ℝ) ≤ (8422633669688623767/100000000000000000000 : ℝ) := by
    have hpowers : (62767/100000 : ℝ)^85 ≤ (8422633669688623767/100000000000000000000 : ℝ)^16 := by
      have hnat : (62767 : ℕ)^85*100000000000000000000^16 ≤ 8422633669688623767^16*100000^85 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        62767 100000 8422633669688623767 100000000000000000000 85 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (62767/100000 : ℝ)) (X := (8422633669688623767/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 85 16 (by norm_num) hpowers
    exact h
  have s1_corner0a : (108422633669688623767/100000000000000000000 : ℝ) ≤ (10153384072557081/10000000000000000 : ℝ) ^ (85/16 : ℝ) := by
    have hpowers : (108422633669688623767/100000000000000000000 : ℝ)^16 ≤ (10153384072557081/10000000000000000 : ℝ)^85 := by
      have hnat : (108422633669688623767 : ℕ)^16*10000000000000000^85 ≤ 10153384072557081^85*100000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        108422633669688623767 100000000000000000000 10153384072557081 10000000000000000 16 85 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10153384072557081/10000000000000000 : ℝ)) (X := (108422633669688623767/100000000000000000000 : ℝ)) (by norm_num) 85 16 (by norm_num) hpowers
    exact h
  have s1_corner0b : (58422633669688623767/50000000000000000000 : ℝ) ≤ (10297381438437593/10000000000000000 : ℝ) ^ (85/16 : ℝ) := by
    have hpowers : (58422633669688623767/50000000000000000000 : ℝ)^16 ≤ (10297381438437593/10000000000000000 : ℝ)^85 := by
      have hnat : (58422633669688623767 : ℕ)^16*10000000000000000^85 ≤ 10297381438437593^85*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        58422633669688623767 50000000000000000000 10297381438437593 10000000000000000 16 85 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10297381438437593/10000000000000000 : ℝ)) (X := (58422633669688623767/50000000000000000000 : ℝ)) (by norm_num) 85 16 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(153384072557081/6276700000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(2249958841883/98073437500000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (85/16 : ℝ)) (rho := (62767/100000 : ℝ)) (alpha := (153384072557081/6276700000000000 : ℝ)) (beta := (2249958841883/98073437500000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![false, false, false]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (62767/100000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(153384072557081/6276700000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(2249958841883/98073437500000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (62711/100000 : ℝ) ^ (85/16 : ℝ) ≤ (838278920079548211/10000000000000000000 : ℝ) := by
    have hpowers : (62711/100000 : ℝ)^85 ≤ (838278920079548211/10000000000000000000 : ℝ)^16 := by
      have hnat : (62711 : ℕ)^85*10000000000000000000^16 ≤ 838278920079548211^16*100000^85 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        62711 100000 838278920079548211 10000000000000000000 85 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (62711/100000 : ℝ)) (X := (838278920079548211/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 85 16 (by norm_num) hpowers
    exact h
  have s1_corner1a : (10838278920079548211/10000000000000000000 : ℝ) ≤ (10152681607461531/10000000000000000 : ℝ) ^ (85/16 : ℝ) := by
    have hpowers : (10838278920079548211/10000000000000000000 : ℝ)^16 ≤ (10152681607461531/10000000000000000 : ℝ)^85 := by
      have hnat : (10838278920079548211 : ℕ)^16*10000000000000000^85 ≤ 10152681607461531^85*10000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10838278920079548211 10000000000000000000 10152681607461531 10000000000000000 16 85 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10152681607461531/10000000000000000 : ℝ)) (X := (10838278920079548211/10000000000000000000 : ℝ)) (by norm_num) 85 16 (by norm_num) hpowers
    exact h
  have s1_corner1b : (5838278920079548211/5000000000000000000 : ℝ) ≤ (2059211824629347/2000000000000000 : ℝ) ^ (85/16 : ℝ) := by
    have hpowers : (5838278920079548211/5000000000000000000 : ℝ)^16 ≤ (2059211824629347/2000000000000000 : ℝ)^85 := by
      have hnat : (5838278920079548211 : ℕ)^16*2000000000000000^85 ≤ 2059211824629347^85*5000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5838278920079548211 5000000000000000000 2059211824629347 2000000000000000 16 85 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2059211824629347/2000000000000000 : ℝ)) (X := (5838278920079548211/5000000000000000000 : ℝ)) (by norm_num) 85 16 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(152681607461531/6271100000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(35844378921301/1567775000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (85/16 : ℝ)) (rho := (62711/100000 : ℝ)) (alpha := (152681607461531/6271100000000000 : ℝ)) (beta := (35844378921301/1567775000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![false, false, false]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (62711/100000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(152681607461531/6271100000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(35844378921301/1567775000000000 : ℝ)*((-1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (13899/100000 : ℝ) ^ (85/16 : ℝ) ≤ (2799626756767113/100000000000000000000 : ℝ) := by
    have hpowers : (13899/100000 : ℝ)^85 ≤ (2799626756767113/100000000000000000000 : ℝ)^16 := by
      have hnat : (13899 : ℕ)^85*100000000000000000000^16 ≤ 2799626756767113^16*100000^85 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        13899 100000 2799626756767113 100000000000000000000 85 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (13899/100000 : ℝ)) (X := (2799626756767113/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 85 16 (by norm_num) hpowers
    exact h
  have s1_corner2a : (100002799626756767113/100000000000000000000 : ℝ) ≤ (10000052698257781/10000000000000000 : ℝ) ^ (85/16 : ℝ) := by
    have hpowers : (100002799626756767113/100000000000000000000 : ℝ)^16 ≤ (10000052698257781/10000000000000000 : ℝ)^85 := by
      have hnat : (100002799626756767113 : ℕ)^16*10000000000000000^85 ≤ 10000052698257781^85*100000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100002799626756767113 100000000000000000000 10000052698257781 10000000000000000 16 85 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000052698257781/10000000000000000 : ℝ)) (X := (100002799626756767113/100000000000000000000 : ℝ)) (by norm_num) 85 16 (by norm_num) hpowers
    exact h
  have s1_corner2b : (50002799626756767113/50000000000000000000 : ℝ) ≤ (10000105395317969/10000000000000000 : ℝ) ^ (85/16 : ℝ) := by
    have hpowers : (50002799626756767113/50000000000000000000 : ℝ)^16 ≤ (10000105395317969/10000000000000000 : ℝ)^85 := by
      have hnat : (50002799626756767113 : ℕ)^16*10000000000000000^85 ≤ 10000105395317969^85*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50002799626756767113 50000000000000000000 10000105395317969 10000000000000000 16 85 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000105395317969/10000000000000000 : ℝ)) (X := (50002799626756767113/50000000000000000000 : ℝ)) (by norm_num) 85 16 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(17566085927/463300000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 1 0))+(13174265047/347475000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (85/16 : ℝ)) (rho := (13899/100000 : ℝ)) (alpha := (17566085927/463300000000000 : ℝ)) (beta := (13174265047/347475000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![false, false, false]] hX 2 (by
        change ((-1 : ℝ)*pair X 2 0) ≤ (13899/100000 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(17566085927/463300000000000 : ℝ)*((-1 : ℝ)*pair X 2 0)+(13174265047/347475000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-2957908027/10000000000 : ℝ)*X 0 0+(2957634581/10000000000 : ℝ)*X 0 1+(-307166411/500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c325048_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_1 : ((1792895047/5000000000 : ℝ)*X 1 0+(-3585458603/10000000000 : ℝ)*X 1 1+(-5030244637/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c325048_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((5213046807/10000000000 : ℝ)*X 2 0+(5213505827/10000000000 : ℝ)*X 2 1+(761702157/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c325048_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_6 : ((4965028749/10000000000 : ℝ)*X 0 0+(4965465931/10000000000 : ℝ)*X 0 1+(-214812789/1000000000 : ℝ)*X 0 2+(4965028749/10000000000 : ℝ)*X 1 0+(4965465931/10000000000 : ℝ)*X 1 1+(-214812789/1000000000 : ℝ)*X 1 2+(4965028749/10000000000 : ℝ)*X 2 0+(4965465931/10000000000 : ℝ)*X 2 1+(-214812789/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c325048_s1_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have hsep : (-452817/50000 : ℝ) < ((-200939/100000 : ℝ)*P 0+(-200939/100000 : ℝ)*P 1+(-200939/100000 : ℝ)*P 2+(1 : ℝ)*T) := by
    have hcertificate_margin : (-452817/50000 : ℝ) < (-1024413036343123762022030827527888671/113977050839506250000000000000000000 : ℝ) := by norm_num
    linear_combination (1051/125000000000 : ℝ)*(base12) + (3637/500000000000 : ℝ)*(base16) + (143/50000000000 : ℝ)*(base21) + (803/250000000000 : ℝ)*(base33) + (241436035779/1000000000000 : ℝ)*(base39) + (333/125000000000 : ℝ)*(base50) + (66574526787/62500000000 : ℝ)*(base59) + (438521541949/1000000000000 : ℝ)*(base60) + (502347499197/250000000000 : ℝ)*(major_s1_0) + (200939/100000 : ℝ)*(major_s1_1) + (200939/100000 : ℝ)*(major_s1_2) + (1497981429773/500000000000 : ℝ)*(sp_s1_0) + (748990714367/250000000000 : ℝ)*(sp_s1_1) + (1497981430941/500000000000 : ℝ)*(sp_s1_2) + (1 : ℝ)*(sp_s1_6) + (1497981433977/500000000000 : ℝ)*(f.sum) + (456162082162924127/1452700315000000000000000000000 : ℝ)*base62 + (4974961790587/69495000000000000000000000 : ℝ)*base64 + (3789926479833/15677750000000000000000000 : ℝ)*base67 + (5913056098617/5791250000000000000000000 : ℝ)*base68 + (6443218757400407327/21809963325000000000000000000000 : ℝ)*base70 + (55038290616897/784587500000000000000000000 : ℝ)*base73 + (98681349874157/313555000000000000000000000 : ℝ)*base74 + (32178389994361/196146875000000000000000000 : ℝ)*base76 + (10562058762355336693/49202266712500000000000000000000 : ℝ)*base78 + hcertificate_margin
  linarith only [hsep,f.failure]

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
namespace HlawkaSchatten.DiagonalCutoff4
theorem coarse_distinct_p025_b024 (p : ℝ) (hpa : (85/16 : ℝ) ≤ p) (hpb : p ≤ (87/16 : ℝ))
    (c : Fin 88) (hlo : 48 ≤ c.val) (hhi : c.val < 49)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (200939/100000 : ℝ) (33069/20000 : ℝ) (81317/100000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  have hc : c=48 := by omega
  rcases hc with rfl
  · exact collision_c325048 p hpa (by linarith only [hpb]) X hX

end HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p : ℝ) (hpa : (85/16 : ℝ) ≤ p) (hpb : p ≤ (87/16 : ℝ))
    (c : Fin 88) (hlo : 48 ≤ c.val) (hhi : c.val < 49)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (200939/100000 : ℝ) (33069/20000 : ℝ) (81317/100000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  exact HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p025_b024 p hpa hpb c hlo hhi hn63 hn87 X hX

#print axioms solution
