-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p007_b033
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:12:19.096987+00:00
-- url     : https://prove2.me/submissions/c0ef5785-8456-4771-880b-6d199c535cf8

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
theorem collision_support_c307070_s0_0 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-522194237/2500000000 : ℝ)*x 0 + (-4342142449/10000000000 : ℝ)*x 1 + (-6198929619/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (522194237/2500000000 : ℝ)^17 ≤ (12901139942941/100000000000000 : ℝ)^13 := by
    have hnat : (522194237 : ℕ)^17*100000000000000^13 ≤ 12901139942941^13*2500000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      522194237 2500000000 12901139942941 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4342142449/10000000000 : ℝ)^17 ≤ (8397855621227/25000000000000 : ℝ)^13 := by
    have hnat : (4342142449 : ℕ)^17*25000000000000^13 ≤ 8397855621227^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4342142449 10000000000 8397855621227 25000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6198929619/10000000000 : ℝ)^17 ≤ (53507437560453/100000000000000 : ℝ)^13 := by
    have hnat : (6198929619 : ℕ)^17*100000000000000^13 ≤ 53507437560453^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6198929619 10000000000 53507437560453 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-522194237/2500000000 : ℝ), (-4342142449/10000000000 : ℝ), (-6198929619/10000000000 : ℝ)] ![(12901139942941/100000000000000 : ℝ), (8397855621227/25000000000000 : ℝ), (53507437560453/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-522194237/2500000000 : ℝ)|^17 ≤ (12901139942941/100000000000000 : ℝ)^13
        have hw : |(-522194237/2500000000 : ℝ)|=(522194237/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-4342142449/10000000000 : ℝ)|^17 ≤ (8397855621227/25000000000000 : ℝ)^13
        have hw : |(-4342142449/10000000000 : ℝ)|=(4342142449/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-6198929619/10000000000 : ℝ)|^17 ≤ (53507437560453/100000000000000 : ℝ)^13
        have hw : |(-6198929619/10000000000 : ℝ)|=(6198929619/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307070_s0_1 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (3099464803/5000000000 : ℝ)*x 0 + (2171071227/5000000000 : ℝ)*x 1 + (-1631857/7812500 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3099464803/5000000000 : ℝ)^17 ≤ (26753718706857/50000000000000 : ℝ)^13 := by
    have hnat : (3099464803 : ℕ)^17*50000000000000^13 ≤ 26753718706857^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3099464803 5000000000 26753718706857 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2171071227/5000000000 : ℝ)^17 ≤ (3359142253549/10000000000000 : ℝ)^13 := by
    have hnat : (2171071227 : ℕ)^17*10000000000000^13 ≤ 3359142253549^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2171071227 5000000000 3359142253549 10000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1631857/7812500 : ℝ)^17 ≤ (12901140039863/100000000000000 : ℝ)^13 := by
    have hnat : (1631857 : ℕ)^17*100000000000000^13 ≤ 12901140039863^13*7812500^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1631857 7812500 12901140039863 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3099464803/5000000000 : ℝ), (2171071227/5000000000 : ℝ), (-1631857/7812500 : ℝ)] ![(26753718706857/50000000000000 : ℝ), (3359142253549/10000000000000 : ℝ), (12901140039863/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3099464803/5000000000 : ℝ)|^17 ≤ (26753718706857/50000000000000 : ℝ)^13
        have hw : |(3099464803/5000000000 : ℝ)|=(3099464803/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2171071227/5000000000 : ℝ)|^17 ≤ (3359142253549/10000000000000 : ℝ)^13
        have hw : |(2171071227/5000000000 : ℝ)|=(2171071227/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1631857/7812500 : ℝ)|^17 ≤ (12901140039863/100000000000000 : ℝ)^13
        have hw : |(-1631857/7812500 : ℝ)|=(1631857/7812500 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307070_s0_6 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (104863613/200000000 : ℝ)*x 0 + (-278395959/1250000000 : ℝ)*x 1 + (-2621590333/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (104863613/200000000 : ℝ)^17 ≤ (21492469003943/50000000000000 : ℝ)^13 := by
    have hnat : (104863613 : ℕ)^17*50000000000000^13 ≤ 21492469003943^13*200000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      104863613 200000000 21492469003943 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (278395959/1250000000 : ℝ)^17 ≤ (1753765474199/12500000000000 : ℝ)^13 := by
    have hnat : (278395959 : ℕ)^17*12500000000000^13 ≤ 1753765474199^13*1250000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      278395959 1250000000 1753765474199 12500000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2621590333/5000000000 : ℝ)^17 ≤ (42984938179419/100000000000000 : ℝ)^13 := by
    have hnat : (2621590333 : ℕ)^17*100000000000000^13 ≤ 42984938179419^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2621590333 5000000000 42984938179419 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(104863613/200000000 : ℝ), (-278395959/1250000000 : ℝ), (-2621590333/5000000000 : ℝ)] ![(21492469003943/50000000000000 : ℝ), (1753765474199/12500000000000 : ℝ), (42984938179419/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(104863613/200000000 : ℝ)|^17 ≤ (21492469003943/50000000000000 : ℝ)^13
        have hw : |(104863613/200000000 : ℝ)|=(104863613/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-278395959/1250000000 : ℝ)|^17 ≤ (1753765474199/12500000000000 : ℝ)^13
        have hw : |(-278395959/1250000000 : ℝ)|=(278395959/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2621590333/5000000000 : ℝ)|^17 ≤ (42984938179419/100000000000000 : ℝ)^13
        have hw : |(-2621590333/5000000000 : ℝ)|=(2621590333/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307070_s0_7 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-404605901/2000000000 : ℝ)*x 0 + (-141252951/312500000 : ℝ)*x 1 + (-760617103/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (404605901/2000000000 : ℝ)^17 ≤ (12372698707277/100000000000000 : ℝ)^13 := by
    have hnat : (404605901 : ℕ)^17*100000000000000^13 ≤ 12372698707277^13*2000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      404605901 2000000000 12372698707277 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (141252951/312500000 : ℝ)^17 ≤ (17701458582809/50000000000000 : ℝ)^13 := by
    have hnat : (141252951 : ℕ)^17*50000000000000^13 ≤ 17701458582809^13*312500000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      141252951 312500000 17701458582809 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (760617103/1250000000 : ℝ)^17 ≤ (5222438411209/10000000000000 : ℝ)^13 := by
    have hnat : (760617103 : ℕ)^17*10000000000000^13 ≤ 5222438411209^13*1250000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      760617103 1250000000 5222438411209 10000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-404605901/2000000000 : ℝ), (-141252951/312500000 : ℝ), (-760617103/1250000000 : ℝ)] ![(12372698707277/100000000000000 : ℝ), (17701458582809/50000000000000 : ℝ), (5222438411209/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-404605901/2000000000 : ℝ)|^17 ≤ (12372698707277/100000000000000 : ℝ)^13
        have hw : |(-404605901/2000000000 : ℝ)|=(404605901/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-141252951/312500000 : ℝ)|^17 ≤ (17701458582809/50000000000000 : ℝ)^13
        have hw : |(-141252951/312500000 : ℝ)|=(141252951/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-760617103/1250000000 : ℝ)|^17 ≤ (5222438411209/10000000000000 : ℝ)^13
        have hw : |(-760617103/1250000000 : ℝ)|=(760617103/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307070_s0_8 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (96674871/156250000 : ℝ)*x 0 + (225432093/500000000 : ℝ)*x 1 + (-1892509779/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (96674871/156250000 : ℝ)^17 ≤ (26687491653693/50000000000000 : ℝ)^13 := by
    have hnat : (96674871 : ℕ)^17*50000000000000^13 ≤ 26687491653693^13*156250000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      96674871 156250000 26687491653693 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (225432093/500000000 : ℝ)^17 ≤ (17642831170621/50000000000000 : ℝ)^13 := by
    have hnat : (225432093 : ℕ)^17*50000000000000^13 ≤ 17642831170621^13*500000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      225432093 500000000 17642831170621 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1892509779/10000000000 : ℝ)^17 ≤ (5669677172253/50000000000000 : ℝ)^13 := by
    have hnat : (1892509779 : ℕ)^17*50000000000000^13 ≤ 5669677172253^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1892509779 10000000000 5669677172253 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(96674871/156250000 : ℝ), (225432093/500000000 : ℝ), (-1892509779/10000000000 : ℝ)] ![(26687491653693/50000000000000 : ℝ), (17642831170621/50000000000000 : ℝ), (5669677172253/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(96674871/156250000 : ℝ)|^17 ≤ (26687491653693/50000000000000 : ℝ)^13
        have hw : |(96674871/156250000 : ℝ)|=(96674871/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(225432093/500000000 : ℝ)|^17 ≤ (17642831170621/50000000000000 : ℝ)^13
        have hw : |(225432093/500000000 : ℝ)|=(225432093/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1892509779/10000000000 : ℝ)|^17 ≤ (5669677172253/50000000000000 : ℝ)^13
        have hw : |(-1892509779/10000000000 : ℝ)|=(1892509779/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307070_s0_9 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (1997315709/5000000000 : ℝ)*x 0 + (-4780951881/10000000000 : ℝ)*x 1 + (4162119117/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1997315709/5000000000 : ℝ)^17 ≤ (15059972126451/50000000000000 : ℝ)^13 := by
    have hnat : (1997315709 : ℕ)^17*50000000000000^13 ≤ 15059972126451^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1997315709 5000000000 15059972126451 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4780951881/10000000000 : ℝ)^17 ≤ (19049054079007/50000000000000 : ℝ)^13 := by
    have hnat : (4780951881 : ℕ)^17*50000000000000^13 ≤ 19049054079007^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4780951881 10000000000 19049054079007 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4162119117/10000000000 : ℝ)^17 ≤ (3178194757077/10000000000000 : ℝ)^13 := by
    have hnat : (4162119117 : ℕ)^17*10000000000000^13 ≤ 3178194757077^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4162119117 10000000000 3178194757077 10000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1997315709/5000000000 : ℝ), (-4780951881/10000000000 : ℝ), (4162119117/10000000000 : ℝ)] ![(15059972126451/50000000000000 : ℝ), (19049054079007/50000000000000 : ℝ), (3178194757077/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1997315709/5000000000 : ℝ)|^17 ≤ (15059972126451/50000000000000 : ℝ)^13
        have hw : |(1997315709/5000000000 : ℝ)|=(1997315709/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-4780951881/10000000000 : ℝ)|^17 ≤ (19049054079007/50000000000000 : ℝ)^13
        have hw : |(-4780951881/10000000000 : ℝ)|=(4780951881/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4162119117/10000000000 : ℝ)|^17 ≤ (3178194757077/10000000000000 : ℝ)^13
        have hw : |(4162119117/10000000000 : ℝ)|=(4162119117/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307070_s0_13 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (519412549/1000000000 : ℝ)*x 0 + (-393103887/2000000000 : ℝ)*x 1 + (-5487741519/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (519412549/1000000000 : ℝ)^17 ≤ (42459786247707/100000000000000 : ℝ)^13 := by
    have hnat : (519412549 : ℕ)^17*100000000000000^13 ≤ 42459786247707^13*1000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      519412549 1000000000 42459786247707 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (393103887/2000000000 : ℝ)^17 ≤ (1489346566509/12500000000000 : ℝ)^13 := by
    have hnat : (393103887 : ℕ)^17*12500000000000^13 ≤ 1489346566509^13*2000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      393103887 2000000000 1489346566509 12500000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5487741519/10000000000 : ℝ)^17 ≤ (11406360301013/25000000000000 : ℝ)^13 := by
    have hnat : (5487741519 : ℕ)^17*25000000000000^13 ≤ 11406360301013^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5487741519 10000000000 11406360301013 25000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(519412549/1000000000 : ℝ), (-393103887/2000000000 : ℝ), (-5487741519/10000000000 : ℝ)] ![(42459786247707/100000000000000 : ℝ), (1489346566509/12500000000000 : ℝ), (11406360301013/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(519412549/1000000000 : ℝ)|^17 ≤ (42459786247707/100000000000000 : ℝ)^13
        have hw : |(519412549/1000000000 : ℝ)|=(519412549/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-393103887/2000000000 : ℝ)|^17 ≤ (1489346566509/12500000000000 : ℝ)^13
        have hw : |(-393103887/2000000000 : ℝ)|=(393103887/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-5487741519/10000000000 : ℝ)|^17 ≤ (11406360301013/25000000000000 : ℝ)^13
        have hw : |(-5487741519/10000000000 : ℝ)|=(5487741519/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307070_s0_14 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-39227871/200000000 : ℝ)*x 0 + (-523975031/1250000000 : ℝ)*x 1 + (-401375373/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (39227871/200000000 : ℝ)^17 ≤ (11882076823197/100000000000000 : ℝ)^13 := by
    have hnat : (39227871 : ℕ)^17*100000000000000^13 ≤ 11882076823197^13*200000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      39227871 200000000 11882076823197 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (523975031/1250000000 : ℝ)^17 ≤ (1603932716697/5000000000000 : ℝ)^13 := by
    have hnat : (523975031 : ℕ)^17*5000000000000^13 ≤ 1603932716697^13*1250000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      523975031 1250000000 1603932716697 5000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (401375373/625000000 : ℝ)^17 ≤ (11207853764473/20000000000000 : ℝ)^13 := by
    have hnat : (401375373 : ℕ)^17*20000000000000^13 ≤ 11207853764473^13*625000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      401375373 625000000 11207853764473 20000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-39227871/200000000 : ℝ), (-523975031/1250000000 : ℝ), (-401375373/625000000 : ℝ)] ![(11882076823197/100000000000000 : ℝ), (1603932716697/5000000000000 : ℝ), (11207853764473/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-39227871/200000000 : ℝ)|^17 ≤ (11882076823197/100000000000000 : ℝ)^13
        have hw : |(-39227871/200000000 : ℝ)|=(39227871/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-523975031/1250000000 : ℝ)|^17 ≤ (1603932716697/5000000000000 : ℝ)^13
        have hw : |(-523975031/1250000000 : ℝ)|=(523975031/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-401375373/625000000 : ℝ)|^17 ≤ (11207853764473/20000000000000 : ℝ)^13
        have hw : |(-401375373/625000000 : ℝ)|=(401375373/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307070_s0_15 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (6285796291/10000000000 : ℝ)*x 0 + (4418608881/10000000000 : ℝ)*x 1 + (-1867379449/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6285796291/10000000000 : ℝ)^17 ≤ (27245032030619/50000000000000 : ℝ)^13 := by
    have hnat : (6285796291 : ℕ)^17*50000000000000^13 ≤ 27245032030619^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6285796291 10000000000 27245032030619 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4418608881/10000000000 : ℝ)^17 ≤ (8591770454631/25000000000000 : ℝ)^13 := by
    have hnat : (4418608881 : ℕ)^17*25000000000000^13 ≤ 8591770454631^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4418608881 10000000000 8591770454631 25000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1867379449/10000000000 : ℝ)^17 ≤ (11142854102939/100000000000000 : ℝ)^13 := by
    have hnat : (1867379449 : ℕ)^17*100000000000000^13 ≤ 11142854102939^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1867379449 10000000000 11142854102939 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6285796291/10000000000 : ℝ), (4418608881/10000000000 : ℝ), (-1867379449/10000000000 : ℝ)] ![(27245032030619/50000000000000 : ℝ), (8591770454631/25000000000000 : ℝ), (11142854102939/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6285796291/10000000000 : ℝ)|^17 ≤ (27245032030619/50000000000000 : ℝ)^13
        have hw : |(6285796291/10000000000 : ℝ)|=(6285796291/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4418608881/10000000000 : ℝ)|^17 ≤ (8591770454631/25000000000000 : ℝ)^13
        have hw : |(4418608881/10000000000 : ℝ)|=(4418608881/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1867379449/10000000000 : ℝ)|^17 ≤ (11142854102939/100000000000000 : ℝ)^13
        have hw : |(-1867379449/10000000000 : ℝ)|=(1867379449/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307070_s0_16 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (4093236261/10000000000 : ℝ)*x 0 + (-5018165049/10000000000 : ℝ)*x 1 + (3810299301/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4093236261/10000000000 : ℝ)^17 ≤ (15547936545527/50000000000000 : ℝ)^13 := by
    have hnat : (4093236261 : ℕ)^17*50000000000000^13 ≤ 15547936545527^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4093236261 10000000000 15547936545527 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5018165049/10000000000 : ℝ)^17 ≤ (40588679583159/100000000000000 : ℝ)^13 := by
    have hnat : (5018165049 : ℕ)^17*100000000000000^13 ≤ 40588679583159^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5018165049 10000000000 40588679583159 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3810299301/10000000000 : ℝ)^17 ≤ (28315447313613/100000000000000 : ℝ)^13 := by
    have hnat : (3810299301 : ℕ)^17*100000000000000^13 ≤ 28315447313613^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3810299301 10000000000 28315447313613 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4093236261/10000000000 : ℝ), (-5018165049/10000000000 : ℝ), (3810299301/10000000000 : ℝ)] ![(15547936545527/50000000000000 : ℝ), (40588679583159/100000000000000 : ℝ), (28315447313613/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4093236261/10000000000 : ℝ)|^17 ≤ (15547936545527/50000000000000 : ℝ)^13
        have hw : |(4093236261/10000000000 : ℝ)|=(4093236261/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-5018165049/10000000000 : ℝ)|^17 ≤ (40588679583159/100000000000000 : ℝ)^13
        have hw : |(-5018165049/10000000000 : ℝ)|=(5018165049/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3810299301/10000000000 : ℝ)|^17 ≤ (28315447313613/100000000000000 : ℝ)^13
        have hw : |(3810299301/10000000000 : ℝ)|=(3810299301/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307070_s0_20 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (1012827313/2000000000 : ℝ)*x 0 + (-2024239883/10000000000 : ℝ)*x 1 + (-222873909/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1012827313/2000000000 : ℝ)^17 ≤ (41075607582347/100000000000000 : ℝ)^13 := by
    have hnat : (1012827313 : ℕ)^17*100000000000000^13 ≤ 41075607582347^13*2000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1012827313 2000000000 41075607582347 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2024239883/10000000000 : ℝ)^17 ≤ (619118994903/5000000000000 : ℝ)^13 := by
    have hnat : (2024239883 : ℕ)^17*5000000000000^13 ≤ 619118994903^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2024239883 10000000000 619118994903 5000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (222873909/400000000 : ℝ)^17 ≤ (11635503128423/25000000000000 : ℝ)^13 := by
    have hnat : (222873909 : ℕ)^17*25000000000000^13 ≤ 11635503128423^13*400000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      222873909 400000000 11635503128423 25000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1012827313/2000000000 : ℝ), (-2024239883/10000000000 : ℝ), (-222873909/400000000 : ℝ)] ![(41075607582347/100000000000000 : ℝ), (619118994903/5000000000000 : ℝ), (11635503128423/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1012827313/2000000000 : ℝ)|^17 ≤ (41075607582347/100000000000000 : ℝ)^13
        have hw : |(1012827313/2000000000 : ℝ)|=(1012827313/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2024239883/10000000000 : ℝ)|^17 ≤ (619118994903/5000000000000 : ℝ)^13
        have hw : |(-2024239883/10000000000 : ℝ)|=(2024239883/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-222873909/400000000 : ℝ)|^17 ≤ (11635503128423/25000000000000 : ℝ)^13
        have hw : |(-222873909/400000000 : ℝ)|=(222873909/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307070_s0_21 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-472844091/2500000000 : ℝ)*x 0 + (-2238212987/5000000000 : ℝ)*x 1 + (-6217151023/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (472844091/2500000000 : ℝ)^17 ≤ (1133047451357/10000000000000 : ℝ)^13 := by
    have hnat : (472844091 : ℕ)^17*10000000000000^13 ≤ 1133047451357^13*2500000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      472844091 2500000000 1133047451357 10000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2238212987/5000000000 : ℝ)^17 ≤ (8739079592741/25000000000000 : ℝ)^13 := by
    have hnat : (2238212987 : ℕ)^17*25000000000000^13 ≤ 8739079592741^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2238212987 5000000000 8739079592741 25000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6217151023/10000000000 : ℝ)^17 ≤ (53713207094611/100000000000000 : ℝ)^13 := by
    have hnat : (6217151023 : ℕ)^17*100000000000000^13 ≤ 53713207094611^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6217151023 10000000000 53713207094611 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-472844091/2500000000 : ℝ), (-2238212987/5000000000 : ℝ), (-6217151023/10000000000 : ℝ)] ![(1133047451357/10000000000000 : ℝ), (8739079592741/25000000000000 : ℝ), (53713207094611/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-472844091/2500000000 : ℝ)|^17 ≤ (1133047451357/10000000000000 : ℝ)^13
        have hw : |(-472844091/2500000000 : ℝ)|=(472844091/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2238212987/5000000000 : ℝ)|^17 ≤ (8739079592741/25000000000000 : ℝ)^13
        have hw : |(-2238212987/5000000000 : ℝ)|=(2238212987/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-6217151023/10000000000 : ℝ)|^17 ≤ (53713207094611/100000000000000 : ℝ)^13
        have hw : |(-6217151023/10000000000 : ℝ)|=(6217151023/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307070_s0_22 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (1609503227/2500000000 : ℝ)*x 0 + (4210617503/10000000000 : ℝ)*x 1 + (-1914366069/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1609503227/2500000000 : ℝ)^17 ≤ (28110997769387/50000000000000 : ℝ)^13 := by
    have hnat : (1609503227 : ℕ)^17*50000000000000^13 ≤ 28110997769387^13*2500000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1609503227 2500000000 28110997769387 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4210617503/10000000000 : ℝ)^17 ≤ (16133547997401/50000000000000 : ℝ)^13 := by
    have hnat : (4210617503 : ℕ)^17*50000000000000^13 ≤ 16133547997401^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4210617503 10000000000 16133547997401 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1914366069/10000000000 : ℝ)^17 ≤ (1438863556009/12500000000000 : ℝ)^13 := by
    have hnat : (1914366069 : ℕ)^17*12500000000000^13 ≤ 1438863556009^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1914366069 10000000000 1438863556009 12500000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1609503227/2500000000 : ℝ), (4210617503/10000000000 : ℝ), (-1914366069/10000000000 : ℝ)] ![(28110997769387/50000000000000 : ℝ), (16133547997401/50000000000000 : ℝ), (1438863556009/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1609503227/2500000000 : ℝ)|^17 ≤ (28110997769387/50000000000000 : ℝ)^13
        have hw : |(1609503227/2500000000 : ℝ)|=(1609503227/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4210617503/10000000000 : ℝ)|^17 ≤ (16133547997401/50000000000000 : ℝ)^13
        have hw : |(4210617503/10000000000 : ℝ)|=(4210617503/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1914366069/10000000000 : ℝ)|^17 ≤ (1438863556009/12500000000000 : ℝ)^13
        have hw : |(-1914366069/10000000000 : ℝ)|=(1914366069/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307070_s0_23 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (3776944537/10000000000 : ℝ)*x 0 + (-5075924977/10000000000 : ℝ)*x 1 + (1016045747/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3776944537/10000000000 : ℝ)^17 ≤ (27991748348279/100000000000000 : ℝ)^13 := by
    have hnat : (3776944537 : ℕ)^17*100000000000000^13 ≤ 27991748348279^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3776944537 10000000000 27991748348279 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5075924977/10000000000 : ℝ)^17 ≤ (41200689601523/100000000000000 : ℝ)^13 := by
    have hnat : (5075924977 : ℕ)^17*100000000000000^13 ≤ 41200689601523^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5075924977 10000000000 41200689601523 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1016045747/2500000000 : ℝ)^17 ≤ (30807562035441/100000000000000 : ℝ)^13 := by
    have hnat : (1016045747 : ℕ)^17*100000000000000^13 ≤ 30807562035441^13*2500000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1016045747 2500000000 30807562035441 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3776944537/10000000000 : ℝ), (-5075924977/10000000000 : ℝ), (1016045747/2500000000 : ℝ)] ![(27991748348279/100000000000000 : ℝ), (41200689601523/100000000000000 : ℝ), (30807562035441/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3776944537/10000000000 : ℝ)|^17 ≤ (27991748348279/100000000000000 : ℝ)^13
        have hw : |(3776944537/10000000000 : ℝ)|=(3776944537/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-5075924977/10000000000 : ℝ)|^17 ≤ (41200689601523/100000000000000 : ℝ)^13
        have hw : |(-5075924977/10000000000 : ℝ)|=(5075924977/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1016045747/2500000000 : ℝ)|^17 ≤ (30807562035441/100000000000000 : ℝ)^13
        have hw : |(1016045747/2500000000 : ℝ)|=(1016045747/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307070_s0_27 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (5557821829/10000000000 : ℝ)*x 0 + (-2064047589/10000000000 : ℝ)*x 1 + (-1262114009/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5557821829/10000000000 : ℝ)^17 ≤ (927777272979/2000000000000 : ℝ)^13 := by
    have hnat : (5557821829 : ℕ)^17*2000000000000^13 ≤ 927777272979^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5557821829 10000000000 927777272979 2000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2064047589/10000000000 : ℝ)^17 ≤ (3175442403711/25000000000000 : ℝ)^13 := by
    have hnat : (2064047589 : ℕ)^17*25000000000000^13 ≤ 3175442403711^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2064047589 10000000000 3175442403711 25000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1262114009/2500000000 : ℝ)^17 ≤ (40909366719129/100000000000000 : ℝ)^13 := by
    have hnat : (1262114009 : ℕ)^17*100000000000000^13 ≤ 40909366719129^13*2500000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1262114009 2500000000 40909366719129 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5557821829/10000000000 : ℝ), (-2064047589/10000000000 : ℝ), (-1262114009/2500000000 : ℝ)] ![(927777272979/2000000000000 : ℝ), (3175442403711/25000000000000 : ℝ), (40909366719129/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5557821829/10000000000 : ℝ)|^17 ≤ (927777272979/2000000000000 : ℝ)^13
        have hw : |(5557821829/10000000000 : ℝ)|=(5557821829/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2064047589/10000000000 : ℝ)|^17 ≤ (3175442403711/25000000000000 : ℝ)^13
        have hw : |(-2064047589/10000000000 : ℝ)|=(2064047589/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1262114009/2500000000 : ℝ)|^17 ≤ (40909366719129/100000000000000 : ℝ)^13
        have hw : |(-1262114009/2500000000 : ℝ)|=(1262114009/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307070_s1_0 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-1725077721/5000000000 : ℝ)*x 0 + (-4170655287/10000000000 : ℝ)*x 1 + (-5269294431/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1725077721/5000000000 : ℝ)^17 ≤ (24867674461307/100000000000000 : ℝ)^13 := by
    have hnat : (1725077721 : ℕ)^17*100000000000000^13 ≤ 24867674461307^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1725077721 5000000000 24867674461307 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4170655287/10000000000 : ℝ)^17 ≤ (7966803180717/25000000000000 : ℝ)^13 := by
    have hnat : (4170655287 : ℕ)^17*25000000000000^13 ≤ 7966803180717^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4170655287 10000000000 7966803180717 25000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5269294431/10000000000 : ℝ)^17 ≤ (8653022561849/20000000000000 : ℝ)^13 := by
    have hnat : (5269294431 : ℕ)^17*20000000000000^13 ≤ 8653022561849^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5269294431 10000000000 8653022561849 20000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1725077721/5000000000 : ℝ), (-4170655287/10000000000 : ℝ), (-5269294431/10000000000 : ℝ)] ![(24867674461307/100000000000000 : ℝ), (7966803180717/25000000000000 : ℝ), (8653022561849/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1725077721/5000000000 : ℝ)|^17 ≤ (24867674461307/100000000000000 : ℝ)^13
        have hw : |(-1725077721/5000000000 : ℝ)|=(1725077721/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-4170655287/10000000000 : ℝ)|^17 ≤ (7966803180717/25000000000000 : ℝ)^13
        have hw : |(-4170655287/10000000000 : ℝ)|=(4170655287/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-5269294431/10000000000 : ℝ)|^17 ≤ (8653022561849/20000000000000 : ℝ)^13
        have hw : |(-5269294431/10000000000 : ℝ)|=(5269294431/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307070_s1_1 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (5268822441/10000000000 : ℝ)*x 0 + (2085661621/5000000000 : ℝ)*x 1 + (-3449984999/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5268822441/10000000000 : ℝ)^17 ≤ (43260045029217/100000000000000 : ℝ)^13 := by
    have hnat : (5268822441 : ℕ)^17*100000000000000^13 ≤ 43260045029217^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5268822441 10000000000 43260045029217 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2085661621/5000000000 : ℝ)^17 ≤ (31873886984973/100000000000000 : ℝ)^13 := by
    have hnat : (2085661621 : ℕ)^17*100000000000000^13 ≤ 31873886984973^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2085661621 5000000000 31873886984973 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3449984999/10000000000 : ℝ)^17 ≤ (3108258496449/12500000000000 : ℝ)^13 := by
    have hnat : (3449984999 : ℕ)^17*12500000000000^13 ≤ 3108258496449^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3449984999 10000000000 3108258496449 12500000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5268822441/10000000000 : ℝ), (2085661621/5000000000 : ℝ), (-3449984999/10000000000 : ℝ)] ![(43260045029217/100000000000000 : ℝ), (31873886984973/100000000000000 : ℝ), (3108258496449/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5268822441/10000000000 : ℝ)|^17 ≤ (43260045029217/100000000000000 : ℝ)^13
        have hw : |(5268822441/10000000000 : ℝ)|=(5268822441/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2085661621/5000000000 : ℝ)|^17 ≤ (31873886984973/100000000000000 : ℝ)^13
        have hw : |(2085661621/5000000000 : ℝ)|=(2085661621/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3449984999/10000000000 : ℝ)|^17 ≤ (3108258496449/12500000000000 : ℝ)^13
        have hw : |(-3449984999/10000000000 : ℝ)|=(3449984999/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307070_s1_2 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (2015380379/5000000000 : ℝ)*x 0 + (-609063633/1250000000 : ℝ)*x 1 + (503739527/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2015380379/5000000000 : ℝ)^17 ≤ (6095335843029/20000000000000 : ℝ)^13 := by
    have hnat : (2015380379 : ℕ)^17*20000000000000^13 ≤ 6095335843029^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2015380379 5000000000 6095335843029 20000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (609063633/1250000000 : ℝ)^17 ≤ (39054991690037/100000000000000 : ℝ)^13 := by
    have hnat : (609063633 : ℕ)^17*100000000000000^13 ≤ 39054991690037^13*1250000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      609063633 1250000000 39054991690037 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (503739527/1250000000 : ℝ)^17 ≤ (1218733163247/4000000000000 : ℝ)^13 := by
    have hnat : (503739527 : ℕ)^17*4000000000000^13 ≤ 1218733163247^13*1250000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      503739527 1250000000 1218733163247 4000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2015380379/5000000000 : ℝ), (-609063633/1250000000 : ℝ), (503739527/1250000000 : ℝ)] ![(6095335843029/20000000000000 : ℝ), (39054991690037/100000000000000 : ℝ), (1218733163247/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2015380379/5000000000 : ℝ)|^17 ≤ (6095335843029/20000000000000 : ℝ)^13
        have hw : |(2015380379/5000000000 : ℝ)|=(2015380379/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-609063633/1250000000 : ℝ)|^17 ≤ (39054991690037/100000000000000 : ℝ)^13
        have hw : |(-609063633/1250000000 : ℝ)|=(609063633/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(503739527/1250000000 : ℝ)|^17 ≤ (1218733163247/4000000000000 : ℝ)^13
        have hw : |(503739527/1250000000 : ℝ)|=(503739527/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307070_s1_6 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (1157546261/2500000000 : ℝ)*x 0 + (-3665714437/10000000000 : ℝ)*x 1 + (-2315670721/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1157546261/2500000000 : ℝ)^17 ≤ (36534698840681/100000000000000 : ℝ)^13 := by
    have hnat : (1157546261 : ℕ)^17*100000000000000^13 ≤ 36534698840681^13*2500000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1157546261 2500000000 36534698840681 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3665714437/10000000000 : ℝ)^17 ≤ (26918669664481/100000000000000 : ℝ)^13 := by
    have hnat : (3665714437 : ℕ)^17*100000000000000^13 ≤ 26918669664481^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3665714437 10000000000 26918669664481 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2315670721/5000000000 : ℝ)^17 ≤ (18273315743531/50000000000000 : ℝ)^13 := by
    have hnat : (2315670721 : ℕ)^17*50000000000000^13 ≤ 18273315743531^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2315670721 5000000000 18273315743531 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1157546261/2500000000 : ℝ), (-3665714437/10000000000 : ℝ), (-2315670721/5000000000 : ℝ)] ![(36534698840681/100000000000000 : ℝ), (26918669664481/100000000000000 : ℝ), (18273315743531/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1157546261/2500000000 : ℝ)|^17 ≤ (36534698840681/100000000000000 : ℝ)^13
        have hw : |(1157546261/2500000000 : ℝ)|=(1157546261/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3665714437/10000000000 : ℝ)|^17 ≤ (26918669664481/100000000000000 : ℝ)^13
        have hw : |(-3665714437/10000000000 : ℝ)|=(3665714437/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2315670721/5000000000 : ℝ)|^17 ≤ (18273315743531/50000000000000 : ℝ)^13
        have hw : |(-2315670721/5000000000 : ℝ)|=(2315670721/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c307070 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (19431/12500 : ℝ) (92559/50000 : ℝ) (4817/6250 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, false], ![true, true, false]]) : False := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (4817/6250 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (4817/6250 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (4817/6250 : ℝ)*P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (4817/6250 : ℝ)*P 1 ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 0+X 2 0)) ∧ ((-1 : ℝ)*(X 0 0+X 2 0)) ≤ ((-1 : ℝ)*(X 0 2+X 2 2)) ∧ ((-1 : ℝ)*(X 0 2+X 2 2)) ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 0) ∧ ((-1 : ℝ)*pair X 1 0) ≤ ((-1 : ℝ)*pair X 1 2) ∧ ((-1 : ℝ)*pair X 1 2) ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (4817/6250 : ℝ)*P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (4817/6250 : ℝ)*P 2 ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base3 : ((1 : ℝ)*N 1+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 1]
  have base21 : ((1 : ℝ)*X 2 0+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 0).2]
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
  have s0_pow0 : (1 : ℝ) ^ (135/32 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^135 ≤ (1 : ℝ)^32 := by
      have hnat : (1 : ℕ)^135*1^32 ≤ 1^32*1^135 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 135 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 135 32 (by norm_num) hpowers
    exact h
  have s0_corner0a : (2 : ℝ) ≤ (5892848319012779/5000000000000000 : ℝ) ^ (135/32 : ℝ) := by
    have hpowers : (2 : ℝ)^32 ≤ (5892848319012779/5000000000000000 : ℝ)^135 := by
      have hnat : (2 : ℕ)^32*5000000000000000^135 ≤ 5892848319012779^135*1^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 5892848319012779 5000000000000000 32 135 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5892848319012779/5000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 135 32 (by norm_num) hpowers
    exact h
  have s0_corner0b : (3 : ℝ) ≤ (12974642747381843/10000000000000000 : ℝ) ^ (135/32 : ℝ) := by
    have hpowers : (3 : ℝ)^32 ≤ (12974642747381843/10000000000000000 : ℝ)^135 := by
      have hnat : (3 : ℕ)^32*10000000000000000^135 ≤ 12974642747381843^135*1^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 12974642747381843 10000000000000000 32 135 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12974642747381843/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 135 32 (by norm_num) hpowers
    exact h
  have major_s0_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(892848319012779/5000000000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(237789221871257/2000000000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (135/32 : ℝ)) (rho := (1 : ℝ)) (alpha := (892848319012779/5000000000000000 : ℝ)) (beta := (237789221871257/2000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow0,s0_corner0a]) (by linarith only [s0_pow0,s0_corner0b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, false], ![true, true, false]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (1 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order0.2.2])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(892848319012779/5000000000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(237789221871257/2000000000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow1 : (1 : ℝ) ^ (135/32 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^135 ≤ (1 : ℝ)^32 := by
      have hnat : (1 : ℕ)^135*1^32 ≤ 1^32*1^135 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 135 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 135 32 (by norm_num) hpowers
    exact h
  have s0_corner1a : (2 : ℝ) ≤ (5892848319012779/5000000000000000 : ℝ) ^ (135/32 : ℝ) := by
    have hpowers : (2 : ℝ)^32 ≤ (5892848319012779/5000000000000000 : ℝ)^135 := by
      have hnat : (2 : ℕ)^32*5000000000000000^135 ≤ 5892848319012779^135*1^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 5892848319012779 5000000000000000 32 135 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5892848319012779/5000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 135 32 (by norm_num) hpowers
    exact h
  have s0_corner1b : (3 : ℝ) ≤ (12974642747381843/10000000000000000 : ℝ) ^ (135/32 : ℝ) := by
    have hpowers : (3 : ℝ)^32 ≤ (12974642747381843/10000000000000000 : ℝ)^135 := by
      have hnat : (3 : ℕ)^32*10000000000000000^135 ≤ 12974642747381843^135*1^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 12974642747381843 10000000000000000 32 135 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12974642747381843/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 135 32 (by norm_num) hpowers
    exact h
  have major_s0_1 : P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1))+(892848319012779/5000000000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2))+(237789221871257/2000000000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 2 0)) := by
    have hh := chart_majorant (a := (135/32 : ℝ)) (rho := (1 : ℝ)) (alpha := (892848319012779/5000000000000000 : ℝ)) (beta := (237789221871257/2000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow1,s0_corner1a]) (by linarith only [s0_pow1,s0_corner1b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, false], ![true, true, false]] hX 1 (by
        change ((-1 : ℝ)*pair X 1 2) ≤ (1 : ℝ)*((-1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order1.2.2])
    change lpNorm p (pair X 1) ≤ ((-1 : ℝ)*pair X 1 1)+(892848319012779/5000000000000000 : ℝ)*((-1 : ℝ)*pair X 1 2)+(237789221871257/2000000000000000 : ℝ)*((-1 : ℝ)*pair X 1 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow2 : (1 : ℝ) ^ (135/32 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^135 ≤ (1 : ℝ)^32 := by
      have hnat : (1 : ℕ)^135*1^32 ≤ 1^32*1^135 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 135 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 135 32 (by norm_num) hpowers
    exact h
  have s0_corner2a : (2 : ℝ) ≤ (5892848319012779/5000000000000000 : ℝ) ^ (135/32 : ℝ) := by
    have hpowers : (2 : ℝ)^32 ≤ (5892848319012779/5000000000000000 : ℝ)^135 := by
      have hnat : (2 : ℕ)^32*5000000000000000^135 ≤ 5892848319012779^135*1^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 5892848319012779 5000000000000000 32 135 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5892848319012779/5000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 135 32 (by norm_num) hpowers
    exact h
  have s0_corner2b : (3 : ℝ) ≤ (12974642747381843/10000000000000000 : ℝ) ^ (135/32 : ℝ) := by
    have hpowers : (3 : ℝ)^32 ≤ (12974642747381843/10000000000000000 : ℝ)^135 := by
      have hnat : (3 : ℕ)^32*10000000000000000^135 ≤ 12974642747381843^135*1^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 12974642747381843 10000000000000000 32 135 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12974642747381843/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 135 32 (by norm_num) hpowers
    exact h
  have major_s0_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(892848319012779/5000000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(237789221871257/2000000000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (135/32 : ℝ)) (rho := (1 : ℝ)) (alpha := (892848319012779/5000000000000000 : ℝ)) (beta := (237789221871257/2000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow2,s0_corner2a]) (by linarith only [s0_pow2,s0_corner2b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, false], ![true, true, false]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (1 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order2.2.2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(892848319012779/5000000000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(237789221871257/2000000000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s0_0 : ((-522194237/2500000000 : ℝ)*X 0 0+(-4342142449/10000000000 : ℝ)*X 0 1+(-6198929619/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c307070_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_1 : ((3099464803/5000000000 : ℝ)*X 1 0+(2171071227/5000000000 : ℝ)*X 1 1+(-1631857/7812500 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c307070_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_6 : ((104863613/200000000 : ℝ)*X 0 0+(-278395959/1250000000 : ℝ)*X 0 1+(-2621590333/5000000000 : ℝ)*X 0 2+(104863613/200000000 : ℝ)*X 1 0+(-278395959/1250000000 : ℝ)*X 1 1+(-2621590333/5000000000 : ℝ)*X 1 2+(104863613/200000000 : ℝ)*X 2 0+(-278395959/1250000000 : ℝ)*X 2 1+(-2621590333/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c307070_s0_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_7 : ((-404605901/2000000000 : ℝ)*X 0 0+(-141252951/312500000 : ℝ)*X 0 1+(-760617103/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c307070_s0_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_8 : ((96674871/156250000 : ℝ)*X 1 0+(225432093/500000000 : ℝ)*X 1 1+(-1892509779/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c307070_s0_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_9 : ((1997315709/5000000000 : ℝ)*X 2 0+(-4780951881/10000000000 : ℝ)*X 2 1+(4162119117/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c307070_s0_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_13 : ((519412549/1000000000 : ℝ)*X 0 0+(-393103887/2000000000 : ℝ)*X 0 1+(-5487741519/10000000000 : ℝ)*X 0 2+(519412549/1000000000 : ℝ)*X 1 0+(-393103887/2000000000 : ℝ)*X 1 1+(-5487741519/10000000000 : ℝ)*X 1 2+(519412549/1000000000 : ℝ)*X 2 0+(-393103887/2000000000 : ℝ)*X 2 1+(-5487741519/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c307070_s0_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_14 : ((-39227871/200000000 : ℝ)*X 0 0+(-523975031/1250000000 : ℝ)*X 0 1+(-401375373/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c307070_s0_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_15 : ((6285796291/10000000000 : ℝ)*X 1 0+(4418608881/10000000000 : ℝ)*X 1 1+(-1867379449/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c307070_s0_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_16 : ((4093236261/10000000000 : ℝ)*X 2 0+(-5018165049/10000000000 : ℝ)*X 2 1+(3810299301/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c307070_s0_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_20 : ((1012827313/2000000000 : ℝ)*X 0 0+(-2024239883/10000000000 : ℝ)*X 0 1+(-222873909/400000000 : ℝ)*X 0 2+(1012827313/2000000000 : ℝ)*X 1 0+(-2024239883/10000000000 : ℝ)*X 1 1+(-222873909/400000000 : ℝ)*X 1 2+(1012827313/2000000000 : ℝ)*X 2 0+(-2024239883/10000000000 : ℝ)*X 2 1+(-222873909/400000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c307070_s0_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_21 : ((-472844091/2500000000 : ℝ)*X 0 0+(-2238212987/5000000000 : ℝ)*X 0 1+(-6217151023/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c307070_s0_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_22 : ((1609503227/2500000000 : ℝ)*X 1 0+(4210617503/10000000000 : ℝ)*X 1 1+(-1914366069/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c307070_s0_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_23 : ((3776944537/10000000000 : ℝ)*X 2 0+(-5075924977/10000000000 : ℝ)*X 2 1+(1016045747/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c307070_s0_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_27 : ((5557821829/10000000000 : ℝ)*X 0 0+(-2064047589/10000000000 : ℝ)*X 0 1+(-1262114009/2500000000 : ℝ)*X 0 2+(5557821829/10000000000 : ℝ)*X 1 0+(-2064047589/10000000000 : ℝ)*X 1 1+(-1262114009/2500000000 : ℝ)*X 1 2+(5557821829/10000000000 : ℝ)*X 2 0+(-2064047589/10000000000 : ℝ)*X 2 1+(-1262114009/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c307070_s0_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s0_0 : (0 : ℝ) ≤ ((541/5000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(541/5000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (31868454901778804593551/2500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (146322135931/25000000000 : ℝ)*(base39) + (305073586421/100000000000 : ℝ)*(base59) + (10785889012261/500000000000 : ℝ)*(major_s0_0) + (10785889012261/500000000000 : ℝ)*(major_s0_1) + (10785889012261/500000000000 : ℝ)*(major_s0_2) + (88622717/500000000000 : ℝ)*(sp_s0_1) + (22450951/100000000000 : ℝ)*(sp_s0_6) + (29266100567873/1000000000000 : ℝ)*(sp_s0_7) + (29266207897767/1000000000000 : ℝ)*(sp_s0_8) + (29266311561023/1000000000000 : ℝ)*(sp_s0_9) + (13876457880401/1000000000000 : ℝ)*(sp_s0_13) + (242133399/500000000000 : ℝ)*(sp_s0_20) + (8892979/31250000000 : ℝ)*(sp_s0_21) + (36791089/500000000000 : ℝ)*(sp_s0_23) + (1387716665671/100000000000 : ℝ)*(f.failure) + (29266385143201/1000000000000 : ℝ)*(f.sum) + (1727054909456253/5000000000000000000000000000 : ℝ)*base63 + (623247023817923/1000000000000000000000000000 : ℝ)*base64 + (756276640433319/2500000000000000000000000000 : ℝ)*base66 + (718333318683319/2500000000000000000000000000 : ℝ)*base69 + (3466972357722977/5000000000000000000000000000 : ℝ)*base70 + (707788017317923/1000000000000000000000000000 : ℝ)*base72 + (309712757517923/1000000000000000000000000000 : ℝ)*base75 + (249296813816681/2500000000000000000000000000 : ℝ)*base76 + (3749234323956253/5000000000000000000000000000 : ℝ)*base78 + (701/1250000000000000 : ℝ)*base87 + (701/1250000000000000 : ℝ)*base89 + (701/1250000000000000 : ℝ)*base91 + (1/1000000000000 : ℝ)*base92 + hcertificate_margin
  have ratio_s0_1 : (0 : ℝ) ≤ ((-20331/100000 : ℝ)*X 0 1+(1 : ℝ)*X 0 2+(-20331/100000 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (44070697610092769006961/5000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1316570872361/250000000000 : ℝ)*(base39) + (335913132129/100000000000 : ℝ)*(base59) + (19553981406809/1000000000000 : ℝ)*(major_s0_0) + (19553981406809/1000000000000 : ℝ)*(major_s0_1) + (19553981406809/1000000000000 : ℝ)*(major_s0_2) + (61883111/1000000000000 : ℝ)*(sp_s0_0) + (94708173/1000000000000 : ℝ)*(sp_s0_1) + (16083373/125000000000 : ℝ)*(sp_s0_9) + (8772867/100000000000 : ℝ)*(sp_s0_13) + (13264391907421/500000000000 : ℝ)*(sp_s0_14) + (26528634086429/1000000000000 : ℝ)*(sp_s0_15) + (26528717030969/1000000000000 : ℝ)*(sp_s0_16) + (12579026448939/1000000000000 : ℝ)*(sp_s0_20) + (116903351/1000000000000 : ℝ)*(sp_s0_22) + (1572389272201/125000000000 : ℝ)*(f.failure) + (829026428061/31250000000 : ℝ)*(f.sum) + (1520415275720143/10000000000000000000000000000 : ℝ)*base62 + (598716610411087/2000000000000000000000000000 : ℝ)*base64 + (2041970166387789/5000000000000000000000000000 : ℝ)*base67 + (1945923641387789/5000000000000000000000000000 : ℝ)*base68 + (5227282813831013/10000000000000000000000000000 : ℝ)*base70 + (468865173811087/2000000000000000000000000000 : ℝ)*base72 + (631908952388913/2000000000000000000000000000 : ℝ)*base74 + (1022299954612211/5000000000000000000000000000 : ℝ)*base77 + (3853065523279857/10000000000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base81 + (1/1000000000000 : ℝ)*base83 + (1/1000000000000 : ℝ)*base85 + (2863/3125000000000000 : ℝ)*base86 + (2863/3125000000000000 : ℝ)*base88 + (2863/3125000000000000 : ℝ)*base90 + (1/1000000000000 : ℝ)*base93 + hcertificate_margin
  have ratio_s0_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-3939/20000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-3939/20000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (23276867274674019682143/5000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (5462601149529/1000000000000 : ℝ)*(base39) + (21278851009/100000000000 : ℝ)*(base49) + (2690508454411/1000000000000 : ℝ)*(base59) + (19080430661051/1000000000000 : ℝ)*(major_s0_0) + (19080430661051/1000000000000 : ℝ)*(major_s0_1) + (19080430661051/1000000000000 : ℝ)*(major_s0_2) + (117822631/1000000000000 : ℝ)*(sp_s0_6) + (95038089/200000000000 : ℝ)*(sp_s0_7) + (112499823/1000000000000 : ℝ)*(sp_s0_15) + (12782901/62500000000 : ℝ)*(sp_s0_16) + (25885906515781/1000000000000 : ℝ)*(sp_s0_21) + (25886269206403/1000000000000 : ℝ)*(sp_s0_22) + (2588617717981/100000000000 : ℝ)*(sp_s0_23) + (245487204829/20000000000 : ℝ)*(sp_s0_27) + (153430975801/12500000000 : ℝ)*(f.failure) + (12943190853113/500000000000 : ℝ)*(f.sum) + (7416067449414077/10000000000000000000000000000 : ℝ)*base62 + (285502870488893/2000000000000000000000000000 : ℝ)*base64 + (3201845857929271/5000000000000000000000000000 : ℝ)*base67 + (3273907621929271/5000000000000000000000000000 : ℝ)*base68 + (2785218685303007/10000000000000000000000000000 : ℝ)*base70 + (289792082311107/2000000000000000000000000000 : ℝ)*base73 + (1643441875511107/2000000000000000000000000000 : ℝ)*base74 + (1518495604570729/5000000000000000000000000000 : ℝ)*base77 + (416082208414077/10000000000000000000000000000 : ℝ)*base79 + (49/625000000000000 : ℝ)*base87 + (49/625000000000000 : ℝ)*base89 + (49/625000000000000 : ℝ)*base91 + (1/1000000000000 : ℝ)*base93 + hcertificate_margin
  have s1_pow0 : (541/5000 : ℝ) ^ (135/32 : ℝ) ≤ (4213240601861861/50000000000000000000 : ℝ) := by
    have hpowers : (541/5000 : ℝ)^135 ≤ (4213240601861861/50000000000000000000 : ℝ)^32 := by
      have hnat : (541 : ℕ)^135*50000000000000000000^32 ≤ 4213240601861861^32*5000^135 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        541 5000 4213240601861861 50000000000000000000 135 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (541/5000 : ℝ)) (X := (4213240601861861/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 135 32 (by norm_num) hpowers
    exact h
  have s1_corner0a : (50004213240601861861/50000000000000000000 : ℝ) ≤ (10000199732393339/10000000000000000 : ℝ) ^ (135/32 : ℝ) := by
    have hpowers : (50004213240601861861/50000000000000000000 : ℝ)^32 ≤ (10000199732393339/10000000000000000 : ℝ)^135 := by
      have hnat : (50004213240601861861 : ℕ)^32*10000000000000000^135 ≤ 10000199732393339^135*50000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50004213240601861861 50000000000000000000 10000199732393339 10000000000000000 32 135 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000199732393339/10000000000000000 : ℝ)) (X := (50004213240601861861/50000000000000000000 : ℝ)) (by norm_num) 135 32 (by norm_num) hpowers
    exact h
  have s1_corner0b : (25004213240601861861/25000000000000000000 : ℝ) ≤ (10000399451947191/10000000000000000 : ℝ) ^ (135/32 : ℝ) := by
    have hpowers : (25004213240601861861/25000000000000000000 : ℝ)^32 ≤ (10000399451947191/10000000000000000 : ℝ)^135 := by
      have hnat : (25004213240601861861 : ℕ)^32*10000000000000000^135 ≤ 10000399451947191^135*25000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25004213240601861861 25000000000000000000 10000399451947191 10000000000000000 32 135 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000399451947191/10000000000000000 : ℝ)) (X := (25004213240601861861/25000000000000000000 : ℝ)) (by norm_num) 135 32 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(199732393339/1082000000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(49929888463/270500000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (135/32 : ℝ)) (rho := (541/5000 : ℝ)) (alpha := (199732393339/1082000000000000 : ℝ)) (beta := (49929888463/270500000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, false], ![true, true, false]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (541/5000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(199732393339/1082000000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(49929888463/270500000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (20331/100000 : ℝ) ^ (135/32 : ℝ) ≤ (120585388213855971/100000000000000000000 : ℝ) := by
    have hpowers : (20331/100000 : ℝ)^135 ≤ (120585388213855971/100000000000000000000 : ℝ)^32 := by
      have hnat : (20331 : ℕ)^135*100000000000000000000^32 ≤ 120585388213855971^32*100000^135 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20331 100000 120585388213855971 100000000000000000000 135 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (20331/100000 : ℝ)) (X := (120585388213855971/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 135 32 (by norm_num) hpowers
    exact h
  have s1_corner1a : (100120585388213855971/100000000000000000000 : ℝ) ≤ (2500714251596403/2500000000000000 : ℝ) ^ (135/32 : ℝ) := by
    have hpowers : (100120585388213855971/100000000000000000000 : ℝ)^32 ≤ (2500714251596403/2500000000000000 : ℝ)^135 := by
      have hnat : (100120585388213855971 : ℕ)^32*2500000000000000^135 ≤ 2500714251596403^135*100000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100120585388213855971 100000000000000000000 2500714251596403 2500000000000000 32 135 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500714251596403/2500000000000000 : ℝ)) (X := (100120585388213855971/100000000000000000000 : ℝ)) (by norm_num) 135 32 (by norm_num) hpowers
    exact h
  have s1_corner1b : (50120585388213855971/50000000000000000000 : ℝ) ≤ (10005711388633687/10000000000000000 : ℝ) ^ (135/32 : ℝ) := by
    have hpowers : (50120585388213855971/50000000000000000000 : ℝ)^32 ≤ (10005711388633687/10000000000000000 : ℝ)^135 := by
      have hnat : (50120585388213855971 : ℕ)^32*10000000000000000^135 ≤ 10005711388633687^135*50000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50120585388213855971 50000000000000000000 10005711388633687 10000000000000000 32 135 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10005711388633687/10000000000000000 : ℝ)) (X := (50120585388213855971/50000000000000000000 : ℝ)) (by norm_num) 135 32 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1))+(714251596403/508275000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2))+(114175289923/81324000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 2 0)) := by
    have hh := chart_majorant (a := (135/32 : ℝ)) (rho := (20331/100000 : ℝ)) (alpha := (714251596403/508275000000000 : ℝ)) (beta := (114175289923/81324000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, false], ![true, true, false]] hX 1 (by
        change ((-1 : ℝ)*pair X 1 2) ≤ (20331/100000 : ℝ)*((-1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((-1 : ℝ)*pair X 1 1)+(714251596403/508275000000000 : ℝ)*((-1 : ℝ)*pair X 1 2)+(114175289923/81324000000000 : ℝ)*((-1 : ℝ)*pair X 1 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (3939/20000 : ℝ) ^ (135/32 : ℝ) ≤ (6590894040189303/6250000000000000000 : ℝ) := by
    have hpowers : (3939/20000 : ℝ)^135 ≤ (6590894040189303/6250000000000000000 : ℝ)^32 := by
      have hnat : (3939 : ℕ)^135*6250000000000000000^32 ≤ 6590894040189303^32*20000^135 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3939 20000 6590894040189303 6250000000000000000 135 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3939/20000 : ℝ)) (X := (6590894040189303/6250000000000000000 : ℝ)) (by norm_num) (by norm_num) 135 32 (by norm_num) hpowers
    exact h
  have s1_corner2a : (6256590894040189303/6250000000000000000 : ℝ) ≤ (1000249865263039/1000000000000000 : ℝ) ^ (135/32 : ℝ) := by
    have hpowers : (6256590894040189303/6250000000000000000 : ℝ)^32 ≤ (1000249865263039/1000000000000000 : ℝ)^135 := by
      have hnat : (6256590894040189303 : ℕ)^32*1000000000000000^135 ≤ 1000249865263039^135*6250000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6256590894040189303 6250000000000000000 1000249865263039 1000000000000000 32 135 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000249865263039/1000000000000000 : ℝ)) (X := (6256590894040189303/6250000000000000000 : ℝ)) (by norm_num) 135 32 (by norm_num) hpowers
    exact h
  have s1_corner2b : (3131590894040189303/3125000000000000000 : ℝ) ≤ (2000999059565143/2000000000000000 : ℝ) ^ (135/32 : ℝ) := by
    have hpowers : (3131590894040189303/3125000000000000000 : ℝ)^32 ≤ (2000999059565143/2000000000000000 : ℝ)^135 := by
      have hnat : (3131590894040189303 : ℕ)^32*2000000000000000^135 ≤ 2000999059565143^135*3125000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3131590894040189303 3125000000000000000 2000999059565143 2000000000000000 32 135 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000999059565143/2000000000000000 : ℝ)) (X := (3131590894040189303/3125000000000000000 : ℝ)) (by norm_num) 135 32 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(83288421013/65650000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(99865807813/78780000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (135/32 : ℝ)) (rho := (3939/20000 : ℝ)) (alpha := (83288421013/65650000000000 : ℝ)) (beta := (99865807813/78780000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, false], ![true, true, false]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (3939/20000 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(83288421013/65650000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(99865807813/78780000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-1725077721/5000000000 : ℝ)*X 0 0+(-4170655287/10000000000 : ℝ)*X 0 1+(-5269294431/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c307070_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_1 : ((5268822441/10000000000 : ℝ)*X 1 0+(2085661621/5000000000 : ℝ)*X 1 1+(-3449984999/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c307070_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((2015380379/5000000000 : ℝ)*X 2 0+(-609063633/1250000000 : ℝ)*X 2 1+(503739527/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c307070_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_6 : ((1157546261/2500000000 : ℝ)*X 0 0+(-3665714437/10000000000 : ℝ)*X 0 1+(-2315670721/5000000000 : ℝ)*X 0 2+(1157546261/2500000000 : ℝ)*X 1 0+(-3665714437/10000000000 : ℝ)*X 1 1+(-2315670721/5000000000 : ℝ)*X 1 2+(1157546261/2500000000 : ℝ)*X 2 0+(-3665714437/10000000000 : ℝ)*X 2 1+(-2315670721/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c307070_s1_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have hsep : (-39543/6250 : ℝ) < ((-19431/12500 : ℝ)*P 0+(-19431/12500 : ℝ)*P 1+(-19431/12500 : ℝ)*P 2+(1 : ℝ)*T) := by
    have hcertificate_margin : (-39543/6250 : ℝ) < (-634062776700832494384666801073/101843250000000000000000000000 : ℝ) := by norm_num
    linear_combination (2203391/1000000000000 : ℝ)*(base3) + (410023/200000000000 : ℝ)*(base21) + (1071361/1000000000000 : ℝ)*(base22) + (34497/125000000000 : ℝ)*(base33) + (551523565777/1000000000000 : ℝ)*(base39) + (176436157237/1000000000000 : ℝ)*(base40) + (50555893113/200000000000 : ℝ)*(base49) + (320406979063/1000000000000 : ℝ)*(base59) + (194309965503/125000000000 : ℝ)*(major_s1_0) + (19431/12500 : ℝ)*(major_s1_1) + (19431/12500 : ℝ)*(major_s1_2) + (415057961917/200000000000 : ℝ)*(sp_s1_0) + (2075291737/1000000000 : ℝ)*(sp_s1_1) + (2075286412133/1000000000000 : ℝ)*(sp_s1_2) + (999997796609/1000000000000 : ℝ)*(sp_s1_6) + (415057961917/200000000000 : ℝ)*(f.sum) + (6771861876999571/14830335000000000000000000000 : ℝ)*base62 + (123247713309/3282500000000000000000000 : ℝ)*base64 + (1190001323933/22590000000000000000000000 : ℝ)*base66 + (671197709713/3282500000000000000000000 : ℝ)*base69 + (23420471799639023/88791625000000000000000000000 : ℝ)*base71 + (28525415249997/67625000000000000000000000 : ℝ)*base72 + (187560189401/2259000000000000000000000 : ℝ)*base75 + (43625265316571/67625000000000000000000000 : ℝ)*base77 + (59177467548638623/152764875000000000000000000000 : ℝ)*base78 + hcertificate_margin
  linarith only [hsep,f.failure]

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
namespace HlawkaSchatten.DiagonalCutoff4
theorem coarse_distinct_p007_b033 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ))
    (c : Fin 88) (hlo : 70 ≤ c.val) (hhi : c.val < 71)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (19431/12500 : ℝ) (92559/50000 : ℝ) (4817/6250 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  have hc : c=70 := by omega
  rcases hc with rfl
  · exact collision_c307070 p hpa (by linarith only [hpb]) X hX

end HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ))
    (c : Fin 88) (hlo : 70 ≤ c.val) (hhi : c.val < 71)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (19431/12500 : ℝ) (92559/50000 : ℝ) (4817/6250 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  exact HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p007_b033 p hpa hpb c hlo hhi hn63 hn87 X hX

#print axioms solution
