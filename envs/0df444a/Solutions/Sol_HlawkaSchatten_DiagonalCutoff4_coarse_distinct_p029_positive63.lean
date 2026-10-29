-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p029_positive63
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T02:28:03.429816+00:00
-- url     : https://prove2.me/submissions/2fd9586d-022f-46cd-a1e5-f664c46919d9

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
namespace HlawkaSchatten.DiagonalCutoff4
theorem positive_chart_nonnegative {p k A d : ℝ} {X : Fin 3 → Fin 3 → ℝ}
    {orders : Fin 3 → Fin 3 → Fin 3}
    (hX : OrderedChart p k A d X orders (fun _ _ => true)) :
    ∀ i h, 0 ≤ pair X i h := by
  intro i h
  obtain ⟨j,rfl⟩ := (hX.permutation i).2 h
  have hh := hX.ordered i
  simp only [signedPair,signValue,Bool.true_eq,if_true,one_mul] at hh
  fin_cases j
  · exact (hh.1.trans hh.2.1).trans hh.2.2
  · exact hh.1.trans hh.2.1
  · exact hh.1
theorem positive_chart_tailratio {p k A d rho : ℝ} {X : Fin 3 → Fin 3 → ℝ}
    {orders : Fin 3 → Fin 3 → Fin 3}
    (hX : OrderedChart p k A d X orders (fun _ _ => true))
    (hm : ∀ i, orders i 0=i)
    (hbig : ∀ i, pair X i (orders i 1) ≤ rho*pair X i i) :
    ∀ i h, i ≠ h → |pair X i h| ≤ rho*pair X i i := by
  intro i h hih
  rw [abs_of_nonneg (positive_chart_nonnegative hX i h)]
  obtain ⟨j,rfl⟩ := (hX.permutation i).2 h
  have hh := hX.ordered i
  simp only [signedPair,signValue,Bool.true_eq,if_true,one_mul] at hh
  fin_cases j
  · exact (hih (hm i).symm).elim
  · exact hbig i
  · exact hh.2.1.trans (hbig i)
end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem collision_support_c329063_s0_0 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-95271071/5000000000 : ℝ)*x 0 + (5433103219/10000000000 : ℝ)*x 1 + (1431125911/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (95271071/5000000000 : ℝ)^95 ≤ (854347983353/100000000000000 : ℝ)^79 := by
    have hnat : (95271071 : ℕ)^95*100000000000000^79 ≤ 854347983353^79*5000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      95271071 5000000000 854347983353 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5433103219/10000000000 : ℝ)^95 ≤ (12004022232271/25000000000000 : ℝ)^79 := by
    have hnat : (5433103219 : ℕ)^95*25000000000000^79 ≤ 12004022232271^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5433103219 10000000000 12004022232271 25000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1431125911/2500000000 : ℝ)^95 ≤ (51129563070137/100000000000000 : ℝ)^79 := by
    have hnat : (1431125911 : ℕ)^95*100000000000000^79 ≤ 51129563070137^79*2500000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1431125911 2500000000 51129563070137 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (95/16 : ℝ)) 95 79 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-95271071/5000000000 : ℝ), (5433103219/10000000000 : ℝ), (1431125911/2500000000 : ℝ)] ![(854347983353/100000000000000 : ℝ), (12004022232271/25000000000000 : ℝ), (51129563070137/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-95271071/5000000000 : ℝ)|^95 ≤ (854347983353/100000000000000 : ℝ)^79
        have hw : |(-95271071/5000000000 : ℝ)|=(95271071/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5433103219/10000000000 : ℝ)|^95 ≤ (12004022232271/25000000000000 : ℝ)^79
        have hw : |(5433103219/10000000000 : ℝ)|=(5433103219/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1431125911/2500000000 : ℝ)|^95 ≤ (51129563070137/100000000000000 : ℝ)^79
        have hw : |(1431125911/2500000000 : ℝ)|=(1431125911/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c329063_s0_1 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1358275739/2500000000 : ℝ)*x 0 + (-95270637/5000000000 : ℝ)*x 1 + (286225217/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1358275739/2500000000 : ℝ)^95 ≤ (6002010766753/12500000000000 : ℝ)^79 := by
    have hnat : (1358275739 : ℕ)^95*12500000000000^79 ≤ 6002010766753^79*2500000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1358275739 2500000000 6002010766753 12500000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (95270637/5000000000 : ℝ)^95 ≤ (427171651601/50000000000000 : ℝ)^79 := by
    have hnat : (95270637 : ℕ)^95*50000000000000^79 ≤ 427171651601^79*5000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      95270637 5000000000 427171651601 50000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (286225217/500000000 : ℝ)^95 ≤ (51129570545633/100000000000000 : ℝ)^79 := by
    have hnat : (286225217 : ℕ)^95*100000000000000^79 ≤ 51129570545633^79*500000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      286225217 500000000 51129570545633 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (95/16 : ℝ)) 95 79 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1358275739/2500000000 : ℝ), (-95270637/5000000000 : ℝ), (286225217/500000000 : ℝ)] ![(6002010766753/12500000000000 : ℝ), (427171651601/50000000000000 : ℝ), (51129570545633/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1358275739/2500000000 : ℝ)|^95 ≤ (6002010766753/12500000000000 : ℝ)^79
        have hw : |(1358275739/2500000000 : ℝ)|=(1358275739/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-95270637/5000000000 : ℝ)|^95 ≤ (427171651601/50000000000000 : ℝ)^79
        have hw : |(-95270637/5000000000 : ℝ)|=(95270637/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(286225217/500000000 : ℝ)|^95 ≤ (51129570545633/100000000000000 : ℝ)^79
        have hw : |(286225217/500000000 : ℝ)|=(286225217/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c329063_s0_7 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-152948803/1000000000 : ℝ)*x 0 + (296510189/2500000000 : ℝ)*x 1 + (1693021101/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (152948803/1000000000 : ℝ)^95 ≤ (10456608753581/100000000000000 : ℝ)^79 := by
    have hnat : (152948803 : ℕ)^95*100000000000000^79 ≤ 10456608753581^79*1000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      152948803 1000000000 10456608753581 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (296510189/2500000000 : ℝ)^95 ≤ (7701502911891/100000000000000 : ℝ)^79 := by
    have hnat : (296510189 : ℕ)^95*100000000000000^79 ≤ 7701502911891^79*2500000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      296510189 2500000000 7701502911891 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1693021101/2000000000 : ℝ)^95 ≤ (2046047208007/2500000000000 : ℝ)^79 := by
    have hnat : (1693021101 : ℕ)^95*2500000000000^79 ≤ 2046047208007^79*2000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1693021101 2000000000 2046047208007 2500000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (95/16 : ℝ)) 95 79 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-152948803/1000000000 : ℝ), (296510189/2500000000 : ℝ), (1693021101/2000000000 : ℝ)] ![(10456608753581/100000000000000 : ℝ), (7701502911891/100000000000000 : ℝ), (2046047208007/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-152948803/1000000000 : ℝ)|^95 ≤ (10456608753581/100000000000000 : ℝ)^79
        have hw : |(-152948803/1000000000 : ℝ)|=(152948803/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(296510189/2500000000 : ℝ)|^95 ≤ (7701502911891/100000000000000 : ℝ)^79
        have hw : |(296510189/2500000000 : ℝ)|=(296510189/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1693021101/2000000000 : ℝ)|^95 ≤ (2046047208007/2500000000000 : ℝ)^79
        have hw : |(1693021101/2000000000 : ℝ)|=(1693021101/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c329063_s0_8 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2401125197/10000000000 : ℝ)*x 0 + (-12581779/2500000000 : ℝ)*x 1 + (1693021301/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2401125197/10000000000 : ℝ)^95 ≤ (8992888327653/50000000000000 : ℝ)^79 := by
    have hnat : (2401125197 : ℕ)^95*50000000000000^79 ≤ 8992888327653^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2401125197 10000000000 8992888327653 50000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (12581779/2500000000 : ℝ)^95 ≤ (4308084753/2500000000000 : ℝ)^79 := by
    have hnat : (12581779 : ℕ)^95*2500000000000^79 ≤ 4308084753^79*2500000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      12581779 2500000000 4308084753 2500000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1693021301/2000000000 : ℝ)^95 ≤ (81841899946533/100000000000000 : ℝ)^79 := by
    have hnat : (1693021301 : ℕ)^95*100000000000000^79 ≤ 81841899946533^79*2000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1693021301 2000000000 81841899946533 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (95/16 : ℝ)) 95 79 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2401125197/10000000000 : ℝ), (-12581779/2500000000 : ℝ), (1693021301/2000000000 : ℝ)] ![(8992888327653/50000000000000 : ℝ), (4308084753/2500000000000 : ℝ), (81841899946533/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2401125197/10000000000 : ℝ)|^95 ≤ (8992888327653/50000000000000 : ℝ)^79
        have hw : |(2401125197/10000000000 : ℝ)|=(2401125197/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-12581779/2500000000 : ℝ)|^95 ≤ (4308084753/2500000000000 : ℝ)^79
        have hw : |(-12581779/2500000000 : ℝ)|=(12581779/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1693021301/2000000000 : ℝ)|^95 ≤ (81841899946533/100000000000000 : ℝ)^79
        have hw : |(1693021301/2000000000 : ℝ)|=(1693021301/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c329063_s0_9 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2401130323/10000000000 : ℝ)*x 0 + (4232550927/5000000000 : ℝ)*x 1 + (-50329033/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2401130323/10000000000 : ℝ)^95 ≤ (8992911414233/50000000000000 : ℝ)^79 := by
    have hnat : (2401130323 : ℕ)^95*50000000000000^79 ≤ 8992911414233^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2401130323 10000000000 8992911414233 50000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4232550927/5000000000 : ℝ)^95 ≤ (81841845872831/100000000000000 : ℝ)^79 := by
    have hnat : (4232550927 : ℕ)^95*100000000000000^79 ≤ 81841845872831^79*5000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4232550927 5000000000 81841845872831 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (50329033/10000000000 : ℝ)^95 ≤ (17233128349/10000000000000 : ℝ)^79 := by
    have hnat : (50329033 : ℕ)^95*10000000000000^79 ≤ 17233128349^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      50329033 10000000000 17233128349 10000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (95/16 : ℝ)) 95 79 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2401130323/10000000000 : ℝ), (4232550927/5000000000 : ℝ), (-50329033/10000000000 : ℝ)] ![(8992911414233/50000000000000 : ℝ), (81841845872831/100000000000000 : ℝ), (17233128349/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2401130323/10000000000 : ℝ)|^95 ≤ (8992911414233/50000000000000 : ℝ)^79
        have hw : |(2401130323/10000000000 : ℝ)|=(2401130323/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4232550927/5000000000 : ℝ)|^95 ≤ (81841845872831/100000000000000 : ℝ)^79
        have hw : |(4232550927/5000000000 : ℝ)|=(4232550927/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-50329033/10000000000 : ℝ)|^95 ≤ (17233128349/10000000000000 : ℝ)^79
        have hw : |(-50329033/10000000000 : ℝ)|=(50329033/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c329063_s0_13 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ)) (x : Fin 3 → ℝ) :
    (313940759/1000000000 : ℝ)*x 0 + (715584067/1000000000 : ℝ)*x 1 + (63128323/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (313940759/1000000000 : ℝ)^95 ≤ (4965619491089/20000000000000 : ℝ)^79 := by
    have hnat : (313940759 : ℕ)^95*20000000000000^79 ≤ 4965619491089^79*1000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      313940759 1000000000 4965619491089 20000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (715584067/1000000000 : ℝ)^95 ≤ (8358625352419/12500000000000 : ℝ)^79 := by
    have hnat : (715584067 : ℕ)^95*12500000000000^79 ≤ 8358625352419^79*1000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      715584067 1000000000 8358625352419 12500000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (63128323/500000000 : ℝ)^95 ≤ (259465615887/3125000000000 : ℝ)^79 := by
    have hnat : (63128323 : ℕ)^95*3125000000000^79 ≤ 259465615887^79*500000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      63128323 500000000 259465615887 3125000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (95/16 : ℝ)) 95 79 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(313940759/1000000000 : ℝ), (715584067/1000000000 : ℝ), (63128323/500000000 : ℝ)] ![(4965619491089/20000000000000 : ℝ), (8358625352419/12500000000000 : ℝ), (259465615887/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(313940759/1000000000 : ℝ)|^95 ≤ (4965619491089/20000000000000 : ℝ)^79
        have hw : |(313940759/1000000000 : ℝ)|=(313940759/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(715584067/1000000000 : ℝ)|^95 ≤ (8358625352419/12500000000000 : ℝ)^79
        have hw : |(715584067/1000000000 : ℝ)|=(715584067/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(63128323/500000000 : ℝ)|^95 ≤ (259465615887/3125000000000 : ℝ)^79
        have hw : |(63128323/500000000 : ℝ)|=(63128323/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c329063_s0_14 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-687777/312500000 : ℝ)*x 0 + (93613549/400000000 : ℝ)*x 1 + (1704276453/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (687777/312500000 : ℝ)^95 ≤ (63736696667/100000000000000 : ℝ)^79 := by
    have hnat : (687777 : ℕ)^95*100000000000000^79 ≤ 63736696667^79*312500000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      687777 312500000 63736696667 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (93613549/400000000 : ℝ)^95 ≤ (17439647395359/100000000000000 : ℝ)^79 := by
    have hnat : (93613549 : ℕ)^95*100000000000000^79 ≤ 17439647395359^79*400000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      93613549 400000000 17439647395359 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1704276453/2000000000 : ℝ)^95 ≤ (82496615891987/100000000000000 : ℝ)^79 := by
    have hnat : (1704276453 : ℕ)^95*100000000000000^79 ≤ 82496615891987^79*2000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1704276453 2000000000 82496615891987 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (95/16 : ℝ)) 95 79 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-687777/312500000 : ℝ), (93613549/400000000 : ℝ), (1704276453/2000000000 : ℝ)] ![(63736696667/100000000000000 : ℝ), (17439647395359/100000000000000 : ℝ), (82496615891987/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-687777/312500000 : ℝ)|^95 ≤ (63736696667/100000000000000 : ℝ)^79
        have hw : |(-687777/312500000 : ℝ)|=(687777/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(93613549/400000000 : ℝ)|^95 ≤ (17439647395359/100000000000000 : ℝ)^79
        have hw : |(93613549/400000000 : ℝ)|=(93613549/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1704276453/2000000000 : ℝ)|^95 ≤ (82496615891987/100000000000000 : ℝ)^79
        have hw : |(1704276453/2000000000 : ℝ)|=(1704276453/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c329063_s0_15 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ)) (x : Fin 3 → ℝ) :
    (215779681/2000000000 : ℝ)*x 0 + (-1550629243/10000000000 : ℝ)*x 1 + (8521382831/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (215779681/2000000000 : ℝ)^95 ≤ (1374543556867/20000000000000 : ℝ)^79 := by
    have hnat : (215779681 : ℕ)^95*20000000000000^79 ≤ 1374543556867^79*2000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      215779681 2000000000 1374543556867 20000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1550629243/10000000000 : ℝ)^95 ≤ (10630659723843/100000000000000 : ℝ)^79 := by
    have hnat : (1550629243 : ℕ)^95*100000000000000^79 ≤ 10630659723843^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1550629243 10000000000 10630659723843 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (8521382831/10000000000 : ℝ)^95 ≤ (20624155620321/25000000000000 : ℝ)^79 := by
    have hnat : (8521382831 : ℕ)^95*25000000000000^79 ≤ 20624155620321^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8521382831 10000000000 20624155620321 25000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (95/16 : ℝ)) 95 79 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(215779681/2000000000 : ℝ), (-1550629243/10000000000 : ℝ), (8521382831/10000000000 : ℝ)] ![(1374543556867/20000000000000 : ℝ), (10630659723843/100000000000000 : ℝ), (20624155620321/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(215779681/2000000000 : ℝ)|^95 ≤ (1374543556867/20000000000000 : ℝ)^79
        have hw : |(215779681/2000000000 : ℝ)|=(215779681/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1550629243/10000000000 : ℝ)|^95 ≤ (10630659723843/100000000000000 : ℝ)^79
        have hw : |(-1550629243/10000000000 : ℝ)|=(1550629243/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(8521382831/10000000000 : ℝ)|^95 ≤ (20624155620321/25000000000000 : ℝ)^79
        have hw : |(8521382831/10000000000 : ℝ)|=(8521382831/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c329063_s0_16 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ)) (x : Fin 3 → ℝ) :
    (8163861227/10000000000 : ℝ)*x 0 + (345563371/1250000000 : ℝ)*x 1 + (-4432809/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (8163861227/10000000000 : ℝ)^95 ≤ (78352288799689/100000000000000 : ℝ)^79 := by
    have hnat : (8163861227 : ℕ)^95*100000000000000^79 ≤ 78352288799689^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8163861227 10000000000 78352288799689 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (345563371/1250000000 : ℝ)^95 ≤ (10653629883607/50000000000000 : ℝ)^79 := by
    have hnat : (345563371 : ℕ)^95*50000000000000^79 ≤ 10653629883607^79*1250000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      345563371 1250000000 10653629883607 50000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4432809/500000000 : ℝ)^95 ≤ (340451415433/100000000000000 : ℝ)^79 := by
    have hnat : (4432809 : ℕ)^95*100000000000000^79 ≤ 340451415433^79*500000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4432809 500000000 340451415433 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (95/16 : ℝ)) 95 79 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(8163861227/10000000000 : ℝ), (345563371/1250000000 : ℝ), (-4432809/500000000 : ℝ)] ![(78352288799689/100000000000000 : ℝ), (10653629883607/50000000000000 : ℝ), (340451415433/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(8163861227/10000000000 : ℝ)|^95 ≤ (78352288799689/100000000000000 : ℝ)^79
        have hw : |(8163861227/10000000000 : ℝ)|=(8163861227/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(345563371/1250000000 : ℝ)|^95 ≤ (10653629883607/50000000000000 : ℝ)^79
        have hw : |(345563371/1250000000 : ℝ)|=(345563371/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-4432809/500000000 : ℝ)|^95 ≤ (340451415433/100000000000000 : ℝ)^79
        have hw : |(-4432809/500000000 : ℝ)|=(4432809/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c329063_s0_20 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ)) (x : Fin 3 → ℝ) :
    (7467464027/10000000000 : ℝ)*x 0 + (551434359/2000000000 : ℝ)*x 1 + (317907987/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (7467464027/10000000000 : ℝ)^95 ≤ (70386065014691/100000000000000 : ℝ)^79 := by
    have hnat : (7467464027 : ℕ)^95*100000000000000^79 ≤ 70386065014691^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7467464027 10000000000 70386065014691 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (551434359/2000000000 : ℝ)^95 ≤ (5309823117621/25000000000000 : ℝ)^79 := by
    have hnat : (551434359 : ℕ)^95*25000000000000^79 ≤ 5309823117621^79*2000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      551434359 2000000000 5309823117621 25000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (317907987/2500000000 : ℝ)^95 ≤ (8374642506303/100000000000000 : ℝ)^79 := by
    have hnat : (317907987 : ℕ)^95*100000000000000^79 ≤ 8374642506303^79*2500000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      317907987 2500000000 8374642506303 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (95/16 : ℝ)) 95 79 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(7467464027/10000000000 : ℝ), (551434359/2000000000 : ℝ), (317907987/2500000000 : ℝ)] ![(70386065014691/100000000000000 : ℝ), (5309823117621/25000000000000 : ℝ), (8374642506303/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(7467464027/10000000000 : ℝ)|^95 ≤ (70386065014691/100000000000000 : ℝ)^79
        have hw : |(7467464027/10000000000 : ℝ)|=(7467464027/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(551434359/2000000000 : ℝ)|^95 ≤ (5309823117621/25000000000000 : ℝ)^79
        have hw : |(551434359/2000000000 : ℝ)|=(551434359/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(317907987/2500000000 : ℝ)|^95 ≤ (8374642506303/100000000000000 : ℝ)^79
        have hw : |(317907987/2500000000 : ℝ)|=(317907987/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c329063_s0_21 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-128571057/10000000000 : ℝ)*x 0 + (1441600377/2000000000 : ℝ)*x 1 + (3878193371/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (128571057/10000000000 : ℝ)^95 ≤ (106466964903/20000000000000 : ℝ)^79 := by
    have hnat : (128571057 : ℕ)^95*20000000000000^79 ≤ 106466964903^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      128571057 10000000000 106466964903 20000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1441600377/2000000000 : ℝ)^95 ≤ (4215974009603/6250000000000 : ℝ)^79 := by
    have hnat : (1441600377 : ℕ)^95*6250000000000^79 ≤ 4215974009603^79*2000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1441600377 2000000000 4215974009603 6250000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3878193371/10000000000 : ℝ)^95 ≤ (8003020251829/25000000000000 : ℝ)^79 := by
    have hnat : (3878193371 : ℕ)^95*25000000000000^79 ≤ 8003020251829^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3878193371 10000000000 8003020251829 25000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (95/16 : ℝ)) 95 79 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-128571057/10000000000 : ℝ), (1441600377/2000000000 : ℝ), (3878193371/10000000000 : ℝ)] ![(106466964903/20000000000000 : ℝ), (4215974009603/6250000000000 : ℝ), (8003020251829/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-128571057/10000000000 : ℝ)|^95 ≤ (106466964903/20000000000000 : ℝ)^79
        have hw : |(-128571057/10000000000 : ℝ)|=(128571057/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1441600377/2000000000 : ℝ)|^95 ≤ (4215974009603/6250000000000 : ℝ)^79
        have hw : |(1441600377/2000000000 : ℝ)|=(1441600377/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3878193371/10000000000 : ℝ)|^95 ≤ (8003020251829/25000000000000 : ℝ)^79
        have hw : |(3878193371/10000000000 : ℝ)|=(3878193371/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c329063_s0_22 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ)) (x : Fin 3 → ℝ) :
    (811632217/1000000000 : ℝ)*x 0 + (-2919597/2000000000 : ℝ)*x 1 + (713975093/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (811632217/1000000000 : ℝ)^95 ≤ (389019765123/500000000000 : ℝ)^79 := by
    have hnat : (811632217 : ℕ)^95*500000000000^79 ≤ 389019765123^79*1000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      811632217 1000000000 389019765123 500000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2919597/2000000000 : ℝ)^95 ≤ (38902050241/100000000000000 : ℝ)^79 := by
    have hnat : (2919597 : ℕ)^95*100000000000000^79 ≤ 38902050241^79*2000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2919597 2000000000 38902050241 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (713975093/2500000000 : ℝ)^95 ≤ (22157144904727/100000000000000 : ℝ)^79 := by
    have hnat : (713975093 : ℕ)^95*100000000000000^79 ≤ 22157144904727^79*2500000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      713975093 2500000000 22157144904727 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (95/16 : ℝ)) 95 79 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(811632217/1000000000 : ℝ), (-2919597/2000000000 : ℝ), (713975093/2500000000 : ℝ)] ![(389019765123/500000000000 : ℝ), (38902050241/100000000000000 : ℝ), (22157144904727/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(811632217/1000000000 : ℝ)|^95 ≤ (389019765123/500000000000 : ℝ)^79
        have hw : |(811632217/1000000000 : ℝ)|=(811632217/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2919597/2000000000 : ℝ)|^95 ≤ (38902050241/100000000000000 : ℝ)^79
        have hw : |(-2919597/2000000000 : ℝ)|=(2919597/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(713975093/2500000000 : ℝ)|^95 ≤ (22157144904727/100000000000000 : ℝ)^79
        have hw : |(713975093/2500000000 : ℝ)|=(713975093/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c329063_s0_23 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ)) (x : Fin 3 → ℝ) :
    (848467489/10000000000 : ℝ)*x 0 + (2164380597/2500000000 : ℝ)*x 1 + (-1567242453/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (848467489/10000000000 : ℝ)^95 ≤ (2574067525533/50000000000000 : ℝ)^79 := by
    have hnat : (848467489 : ℕ)^95*50000000000000^79 ≤ 2574067525533^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      848467489 10000000000 2574067525533 50000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2164380597/2500000000 : ℝ)^95 ≤ (84084094337093/100000000000000 : ℝ)^79 := by
    have hnat : (2164380597 : ℕ)^95*100000000000000^79 ≤ 84084094337093^79*2500000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2164380597 2500000000 84084094337093 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1567242453/10000000000 : ℝ)^95 ≤ (5383885301077/50000000000000 : ℝ)^79 := by
    have hnat : (1567242453 : ℕ)^95*50000000000000^79 ≤ 5383885301077^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1567242453 10000000000 5383885301077 50000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (95/16 : ℝ)) 95 79 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(848467489/10000000000 : ℝ), (2164380597/2500000000 : ℝ), (-1567242453/10000000000 : ℝ)] ![(2574067525533/50000000000000 : ℝ), (84084094337093/100000000000000 : ℝ), (5383885301077/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(848467489/10000000000 : ℝ)|^95 ≤ (2574067525533/50000000000000 : ℝ)^79
        have hw : |(848467489/10000000000 : ℝ)|=(848467489/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2164380597/2500000000 : ℝ)|^95 ≤ (84084094337093/100000000000000 : ℝ)^79
        have hw : |(2164380597/2500000000 : ℝ)|=(2164380597/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1567242453/10000000000 : ℝ)|^95 ≤ (5383885301077/50000000000000 : ℝ)^79
        have hw : |(-1567242453/10000000000 : ℝ)|=(1567242453/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c329063_s0_27 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3786900637/5000000000 : ℝ)*x 0 + (1161094793/5000000000 : ℝ)*x 1 + (1610933841/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3786900637/5000000000 : ℝ)^95 ≤ (7159309744091/10000000000000 : ℝ)^79 := by
    have hnat : (3786900637 : ℕ)^95*10000000000000^79 ≤ 7159309744091^79*5000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3786900637 5000000000 7159309744091 10000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1161094793/5000000000 : ℝ)^95 ≤ (17277141310719/100000000000000 : ℝ)^79 := by
    have hnat : (1161094793 : ℕ)^95*100000000000000^79 ≤ 17277141310719^79*5000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1161094793 5000000000 17277141310719 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1610933841/10000000000 : ℝ)^95 ≤ (11129761235969/100000000000000 : ℝ)^79 := by
    have hnat : (1610933841 : ℕ)^95*100000000000000^79 ≤ 11129761235969^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1610933841 10000000000 11129761235969 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (95/16 : ℝ)) 95 79 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3786900637/5000000000 : ℝ), (1161094793/5000000000 : ℝ), (1610933841/10000000000 : ℝ)] ![(7159309744091/10000000000000 : ℝ), (17277141310719/100000000000000 : ℝ), (11129761235969/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3786900637/5000000000 : ℝ)|^95 ≤ (7159309744091/10000000000000 : ℝ)^79
        have hw : |(3786900637/5000000000 : ℝ)|=(3786900637/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1161094793/5000000000 : ℝ)|^95 ≤ (17277141310719/100000000000000 : ℝ)^79
        have hw : |(1161094793/5000000000 : ℝ)|=(1161094793/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1610933841/10000000000 : ℝ)|^95 ≤ (11129761235969/100000000000000 : ℝ)^79
        have hw : |(1610933841/10000000000 : ℝ)|=(1610933841/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c329063_s1_0 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-979877823/10000000000 : ℝ)*x 0 + (5321014319/10000000000 : ℝ)*x 1 + (667769963/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (979877823/10000000000 : ℝ)^95 ≤ (1530355497303/25000000000000 : ℝ)^79 := by
    have hnat : (979877823 : ℕ)^95*25000000000000^79 ≤ 1530355497303^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      979877823 10000000000 1530355497303 25000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5321014319/10000000000 : ℝ)^95 ≤ (1170683876093/2500000000000 : ℝ)^79 := by
    have hnat : (5321014319 : ℕ)^95*2500000000000^79 ≤ 1170683876093^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5321014319 10000000000 1170683876093 2500000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (667769963/1250000000 : ℝ)^95 ≤ (47051222962929/100000000000000 : ℝ)^79 := by
    have hnat : (667769963 : ℕ)^95*100000000000000^79 ≤ 47051222962929^79*1250000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      667769963 1250000000 47051222962929 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (95/16 : ℝ)) 95 79 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-979877823/10000000000 : ℝ), (5321014319/10000000000 : ℝ), (667769963/1250000000 : ℝ)] ![(1530355497303/25000000000000 : ℝ), (1170683876093/2500000000000 : ℝ), (47051222962929/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-979877823/10000000000 : ℝ)|^95 ≤ (1530355497303/25000000000000 : ℝ)^79
        have hw : |(-979877823/10000000000 : ℝ)|=(979877823/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5321014319/10000000000 : ℝ)|^95 ≤ (1170683876093/2500000000000 : ℝ)^79
        have hw : |(5321014319/10000000000 : ℝ)|=(5321014319/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(667769963/1250000000 : ℝ)|^95 ≤ (47051222962929/100000000000000 : ℝ)^79
        have hw : |(667769963/1250000000 : ℝ)|=(667769963/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c329063_s1_1 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5320924171/10000000000 : ℝ)*x 0 + (-244754663/2500000000 : ℝ)*x 1 + (66785739/125000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5320924171/10000000000 : ℝ)^95 ≤ (46826401024629/100000000000000 : ℝ)^79 := by
    have hnat : (5320924171 : ℕ)^95*100000000000000^79 ≤ 46826401024629^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5320924171 10000000000 46826401024629 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (244754663/2500000000 : ℝ)^95 ≤ (6114968152963/100000000000000 : ℝ)^79 := by
    have hnat : (244754663 : ℕ)^95*100000000000000^79 ≤ 6114968152963^79*2500000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      244754663 2500000000 6114968152963 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (66785739/125000000 : ℝ)^95 ≤ (1176465770197/2500000000000 : ℝ)^79 := by
    have hnat : (66785739 : ℕ)^95*2500000000000^79 ≤ 1176465770197^79*125000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      66785739 125000000 1176465770197 2500000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (95/16 : ℝ)) 95 79 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5320924171/10000000000 : ℝ), (-244754663/2500000000 : ℝ), (66785739/125000000 : ℝ)] ![(46826401024629/100000000000000 : ℝ), (6114968152963/100000000000000 : ℝ), (1176465770197/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5320924171/10000000000 : ℝ)|^95 ≤ (46826401024629/100000000000000 : ℝ)^79
        have hw : |(5320924171/10000000000 : ℝ)|=(5320924171/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-244754663/2500000000 : ℝ)|^95 ≤ (6114968152963/100000000000000 : ℝ)^79
        have hw : |(-244754663/2500000000 : ℝ)|=(244754663/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(66785739/125000000 : ℝ)|^95 ≤ (1176465770197/2500000000000 : ℝ)^79
        have hw : |(66785739/125000000 : ℝ)|=(66785739/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c329063_s1_2 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2668042361/5000000000 : ℝ)*x 0 + (2669876373/5000000000 : ℝ)*x 1 + (-240500467/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2668042361/5000000000 : ℝ)^95 ≤ (11746722056539/25000000000000 : ℝ)^79 := by
    have hnat : (2668042361 : ℕ)^95*25000000000000^79 ≤ 11746722056539^79*5000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2668042361 5000000000 11746722056539 25000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2669876373/5000000000 : ℝ)^95 ≤ (47025731236027/100000000000000 : ℝ)^79 := by
    have hnat : (2669876373 : ℕ)^95*100000000000000^79 ≤ 47025731236027^79*5000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2669876373 5000000000 47025731236027 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (240500467/2500000000 : ℝ)^95 ≤ (5987380522677/100000000000000 : ℝ)^79 := by
    have hnat : (240500467 : ℕ)^95*100000000000000^79 ≤ 5987380522677^79*2500000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      240500467 2500000000 5987380522677 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (95/16 : ℝ)) 95 79 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2668042361/5000000000 : ℝ), (2669876373/5000000000 : ℝ), (-240500467/2500000000 : ℝ)] ![(11746722056539/25000000000000 : ℝ), (47025731236027/100000000000000 : ℝ), (5987380522677/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2668042361/5000000000 : ℝ)|^95 ≤ (11746722056539/25000000000000 : ℝ)^79
        have hw : |(2668042361/5000000000 : ℝ)|=(2668042361/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2669876373/5000000000 : ℝ)|^95 ≤ (47025731236027/100000000000000 : ℝ)^79
        have hw : |(2669876373/5000000000 : ℝ)|=(2669876373/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-240500467/2500000000 : ℝ)|^95 ≤ (5987380522677/100000000000000 : ℝ)^79
        have hw : |(-240500467/2500000000 : ℝ)|=(240500467/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c329063_s1_6 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4025948183/10000000000 : ℝ)*x 0 + (4015853419/10000000000 : ℝ)*x 1 + (1995360191/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4025948183/10000000000 : ℝ)^95 ≤ (4185539996577/12500000000000 : ℝ)^79 := by
    have hnat : (4025948183 : ℕ)^95*12500000000000^79 ≤ 4185539996577^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4025948183 10000000000 4185539996577 12500000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4015853419/10000000000 : ℝ)^95 ≤ (16691690878317/50000000000000 : ℝ)^79 := by
    have hnat : (4015853419 : ℕ)^95*50000000000000^79 ≤ 16691690878317^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4015853419 10000000000 16691690878317 50000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1995360191/5000000000 : ℝ)^95 ≤ (33132298257431/100000000000000 : ℝ)^79 := by
    have hnat : (1995360191 : ℕ)^95*100000000000000^79 ≤ 33132298257431^79*5000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1995360191 5000000000 33132298257431 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (95/16 : ℝ)) 95 79 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4025948183/10000000000 : ℝ), (4015853419/10000000000 : ℝ), (1995360191/5000000000 : ℝ)] ![(4185539996577/12500000000000 : ℝ), (16691690878317/50000000000000 : ℝ), (33132298257431/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4025948183/10000000000 : ℝ)|^95 ≤ (4185539996577/12500000000000 : ℝ)^79
        have hw : |(4025948183/10000000000 : ℝ)|=(4025948183/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4015853419/10000000000 : ℝ)|^95 ≤ (16691690878317/50000000000000 : ℝ)^79
        have hw : |(4015853419/10000000000 : ℝ)|=(4015853419/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1995360191/5000000000 : ℝ)|^95 ≤ (33132298257431/100000000000000 : ℝ)^79
        have hw : |(1995360191/5000000000 : ℝ)|=(1995360191/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c329063_s1_7 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-882501593/10000000000 : ℝ)*x 0 + (4656331357/10000000000 : ℝ)*x 1 + (6056614647/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (882501593/10000000000 : ℝ)^95 ≤ (2698730561799/50000000000000 : ℝ)^79 := by
    have hnat : (882501593 : ℕ)^95*50000000000000^79 ≤ 2698730561799^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      882501593 10000000000 2698730561799 50000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4656331357/10000000000 : ℝ)^95 ≤ (2492827781571/6250000000000 : ℝ)^79 := by
    have hnat : (4656331357 : ℕ)^95*6250000000000^79 ≤ 2492827781571^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4656331357 10000000000 2492827781571 6250000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6056614647/10000000000 : ℝ)^95 ≤ (10943458871361/20000000000000 : ℝ)^79 := by
    have hnat : (6056614647 : ℕ)^95*20000000000000^79 ≤ 10943458871361^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6056614647 10000000000 10943458871361 20000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (95/16 : ℝ)) 95 79 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-882501593/10000000000 : ℝ), (4656331357/10000000000 : ℝ), (6056614647/10000000000 : ℝ)] ![(2698730561799/50000000000000 : ℝ), (2492827781571/6250000000000 : ℝ), (10943458871361/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-882501593/10000000000 : ℝ)|^95 ≤ (2698730561799/50000000000000 : ℝ)^79
        have hw : |(-882501593/10000000000 : ℝ)|=(882501593/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4656331357/10000000000 : ℝ)|^95 ≤ (2492827781571/6250000000000 : ℝ)^79
        have hw : |(4656331357/10000000000 : ℝ)|=(4656331357/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6056614647/10000000000 : ℝ)|^95 ≤ (10943458871361/20000000000000 : ℝ)^79
        have hw : |(6056614647/10000000000 : ℝ)|=(6056614647/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c329063_s1_8 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5018878771/10000000000 : ℝ)*x 0 + (-8136861/250000000 : ℝ)*x 1 + (6057316693/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5018878771/10000000000 : ℝ)^95 ≤ (218242884649/500000000000 : ℝ)^79 := by
    have hnat : (5018878771 : ℕ)^95*500000000000^79 ≤ 218242884649^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5018878771 10000000000 218242884649 500000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (8136861/250000000 : ℝ)^95 ≤ (1626501567281/100000000000000 : ℝ)^79 := by
    have hnat : (8136861 : ℕ)^95*100000000000000^79 ≤ 1626501567281^79*250000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8136861 250000000 1626501567281 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6057316693/10000000000 : ℝ)^95 ≤ (54724921499169/100000000000000 : ℝ)^79 := by
    have hnat : (6057316693 : ℕ)^95*100000000000000^79 ≤ 54724921499169^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6057316693 10000000000 54724921499169 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (95/16 : ℝ)) 95 79 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5018878771/10000000000 : ℝ), (-8136861/250000000 : ℝ), (6057316693/10000000000 : ℝ)] ![(218242884649/500000000000 : ℝ), (1626501567281/100000000000000 : ℝ), (54724921499169/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5018878771/10000000000 : ℝ)|^95 ≤ (218242884649/500000000000 : ℝ)^79
        have hw : |(5018878771/10000000000 : ℝ)|=(5018878771/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-8136861/250000000 : ℝ)|^95 ≤ (1626501567281/100000000000000 : ℝ)^79
        have hw : |(-8136861/250000000 : ℝ)|=(8136861/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6057316693/10000000000 : ℝ)|^95 ≤ (54724921499169/100000000000000 : ℝ)^79
        have hw : |(6057316693/10000000000 : ℝ)|=(6057316693/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c329063_s1_9 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2393129969/5000000000 : ℝ)*x 0 + (314671189/500000000 : ℝ)*x 1 + (-299647777/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2393129969/5000000000 : ℝ)^95 ≤ (41227348205167/100000000000000 : ℝ)^79 := by
    have hnat : (2393129969 : ℕ)^95*100000000000000^79 ≤ 41227348205167^79*5000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2393129969 5000000000 41227348205167 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (314671189/500000000 : ℝ)^95 ≤ (28650039799103/50000000000000 : ℝ)^79 := by
    have hnat : (314671189 : ℕ)^95*50000000000000^79 ≤ 28650039799103^79*500000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      314671189 500000000 28650039799103 50000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (299647777/10000000000 : ℝ)^95 ≤ (736286089711/50000000000000 : ℝ)^79 := by
    have hnat : (299647777 : ℕ)^95*50000000000000^79 ≤ 736286089711^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      299647777 10000000000 736286089711 50000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (95/16 : ℝ)) 95 79 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2393129969/5000000000 : ℝ), (314671189/500000000 : ℝ), (-299647777/10000000000 : ℝ)] ![(41227348205167/100000000000000 : ℝ), (28650039799103/50000000000000 : ℝ), (736286089711/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2393129969/5000000000 : ℝ)|^95 ≤ (41227348205167/100000000000000 : ℝ)^79
        have hw : |(2393129969/5000000000 : ℝ)|=(2393129969/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(314671189/500000000 : ℝ)|^95 ≤ (28650039799103/50000000000000 : ℝ)^79
        have hw : |(314671189/500000000 : ℝ)|=(314671189/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-299647777/10000000000 : ℝ)|^95 ≤ (736286089711/50000000000000 : ℝ)^79
        have hw : |(-299647777/10000000000 : ℝ)|=(299647777/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c329063_s1_13 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4516925383/10000000000 : ℝ)*x 0 + (350258209/625000000 : ℝ)*x 1 + (1680101251/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4516925383/10000000000 : ℝ)^95 ≤ (9613415047707/25000000000000 : ℝ)^79 := by
    have hnat : (4516925383 : ℕ)^95*25000000000000^79 ≤ 9613415047707^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4516925383 10000000000 9613415047707 25000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (350258209/625000000 : ℝ)^95 ≤ (12459863574869/25000000000000 : ℝ)^79 := by
    have hnat : (350258209 : ℕ)^95*25000000000000^79 ≤ 12459863574869^79*625000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      350258209 625000000 12459863574869 25000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1680101251/10000000000 : ℝ)^95 ≤ (11706885484941/100000000000000 : ℝ)^79 := by
    have hnat : (1680101251 : ℕ)^95*100000000000000^79 ≤ 11706885484941^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1680101251 10000000000 11706885484941 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (95/16 : ℝ)) 95 79 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4516925383/10000000000 : ℝ), (350258209/625000000 : ℝ), (1680101251/10000000000 : ℝ)] ![(9613415047707/25000000000000 : ℝ), (12459863574869/25000000000000 : ℝ), (11706885484941/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4516925383/10000000000 : ℝ)|^95 ≤ (9613415047707/25000000000000 : ℝ)^79
        have hw : |(4516925383/10000000000 : ℝ)|=(4516925383/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(350258209/625000000 : ℝ)|^95 ≤ (12459863574869/25000000000000 : ℝ)^79
        have hw : |(350258209/625000000 : ℝ)|=(350258209/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1680101251/10000000000 : ℝ)|^95 ≤ (11706885484941/100000000000000 : ℝ)^79
        have hw : |(1680101251/10000000000 : ℝ)|=(1680101251/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c329063_s1_14 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-164669027/5000000000 : ℝ)*x 0 + (1257016291/2500000000 : ℝ)*x 1 + (6046330287/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (164669027/5000000000 : ℝ)^95 ≤ (1649747552477/100000000000000 : ℝ)^79 := by
    have hnat : (164669027 : ℕ)^95*100000000000000^79 ≤ 1649747552477^79*5000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      164669027 5000000000 1649747552477 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1257016291/2500000000 : ℝ)^95 ≤ (170877611397/390625000000 : ℝ)^79 := by
    have hnat : (1257016291 : ℕ)^95*390625000000^79 ≤ 170877611397^79*2500000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1257016291 2500000000 170877611397 390625000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6046330287/10000000000 : ℝ)^95 ≤ (54605583923091/100000000000000 : ℝ)^79 := by
    have hnat : (6046330287 : ℕ)^95*100000000000000^79 ≤ 54605583923091^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6046330287 10000000000 54605583923091 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (95/16 : ℝ)) 95 79 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-164669027/5000000000 : ℝ), (1257016291/2500000000 : ℝ), (6046330287/10000000000 : ℝ)] ![(1649747552477/100000000000000 : ℝ), (170877611397/390625000000 : ℝ), (54605583923091/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-164669027/5000000000 : ℝ)|^95 ≤ (1649747552477/100000000000000 : ℝ)^79
        have hw : |(-164669027/5000000000 : ℝ)|=(164669027/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1257016291/2500000000 : ℝ)|^95 ≤ (170877611397/390625000000 : ℝ)^79
        have hw : |(1257016291/2500000000 : ℝ)|=(1257016291/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6046330287/10000000000 : ℝ)|^95 ≤ (54605583923091/100000000000000 : ℝ)^79
        have hw : |(6046330287/10000000000 : ℝ)|=(6046330287/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c329063_s1_15 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2337060049/5000000000 : ℝ)*x 0 + (-3486867/40000000 : ℝ)*x 1 + (1209406489/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2337060049/5000000000 : ℝ)^95 ≤ (40068551027749/100000000000000 : ℝ)^79 := by
    have hnat : (2337060049 : ℕ)^95*100000000000000^79 ≤ 40068551027749^79*5000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2337060049 5000000000 40068551027749 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3486867/40000000 : ℝ)^95 ≤ (5318239303443/100000000000000 : ℝ)^79 := by
    have hnat : (3486867 : ℕ)^95*100000000000000^79 ≤ 5318239303443^79*40000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3486867 40000000 5318239303443 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1209406489/2000000000 : ℝ)^95 ≤ (13653302414297/25000000000000 : ℝ)^79 := by
    have hnat : (1209406489 : ℕ)^95*25000000000000^79 ≤ 13653302414297^79*2000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1209406489 2000000000 13653302414297 25000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (95/16 : ℝ)) 95 79 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2337060049/5000000000 : ℝ), (-3486867/40000000 : ℝ), (1209406489/2000000000 : ℝ)] ![(40068551027749/100000000000000 : ℝ), (5318239303443/100000000000000 : ℝ), (13653302414297/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2337060049/5000000000 : ℝ)|^95 ≤ (40068551027749/100000000000000 : ℝ)^79
        have hw : |(2337060049/5000000000 : ℝ)|=(2337060049/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3486867/40000000 : ℝ)|^95 ≤ (5318239303443/100000000000000 : ℝ)^79
        have hw : |(-3486867/40000000 : ℝ)|=(3486867/40000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1209406489/2000000000 : ℝ)|^95 ≤ (13653302414297/25000000000000 : ℝ)^79
        have hw : |(1209406489/2000000000 : ℝ)|=(1209406489/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c329063_s1_16 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3019410357/5000000000 : ℝ)*x 0 + (5046957877/10000000000 : ℝ)*x 1 + (-309932391/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3019410357/5000000000 : ℝ)^95 ≤ (54524037990877/100000000000000 : ℝ)^79 := by
    have hnat : (3019410357 : ℕ)^95*100000000000000^79 ≤ 54524037990877^79*5000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3019410357 5000000000 54524037990877 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5046957877/10000000000 : ℝ)^95 ≤ (4394240196003/10000000000000 : ℝ)^79 := by
    have hnat : (5046957877 : ℕ)^95*10000000000000^79 ≤ 4394240196003^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5046957877 10000000000 4394240196003 10000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (309932391/10000000000 : ℝ)^95 ≤ (1533560036883/100000000000000 : ℝ)^79 := by
    have hnat : (309932391 : ℕ)^95*100000000000000^79 ≤ 1533560036883^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      309932391 10000000000 1533560036883 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (95/16 : ℝ)) 95 79 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3019410357/5000000000 : ℝ), (5046957877/10000000000 : ℝ), (-309932391/10000000000 : ℝ)] ![(54524037990877/100000000000000 : ℝ), (4394240196003/10000000000000 : ℝ), (1533560036883/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3019410357/5000000000 : ℝ)|^95 ≤ (54524037990877/100000000000000 : ℝ)^79
        have hw : |(3019410357/5000000000 : ℝ)|=(3019410357/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5046957877/10000000000 : ℝ)|^95 ≤ (4394240196003/10000000000000 : ℝ)^79
        have hw : |(5046957877/10000000000 : ℝ)|=(5046957877/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-309932391/10000000000 : ℝ)|^95 ≤ (1533560036883/100000000000000 : ℝ)^79
        have hw : |(-309932391/10000000000 : ℝ)|=(309932391/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c329063_s1_20 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ)) (x : Fin 3 → ℝ) :
    (6407138637/10000000000 : ℝ)*x 0 + (904520663/2500000000 : ℝ)*x 1 + (857776639/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6407138637/10000000000 : ℝ)^95 ≤ (29273691518247/50000000000000 : ℝ)^79 := by
    have hnat : (6407138637 : ℕ)^95*50000000000000^79 ≤ 29273691518247^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6407138637 10000000000 29273691518247 50000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (904520663/2500000000 : ℝ)^95 ≤ (14724020343261/50000000000000 : ℝ)^79 := by
    have hnat : (904520663 : ℕ)^95*50000000000000^79 ≤ 14724020343261^79*2500000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      904520663 2500000000 14724020343261 50000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (857776639/5000000000 : ℝ)^95 ≤ (2400915251757/20000000000000 : ℝ)^79 := by
    have hnat : (857776639 : ℕ)^95*20000000000000^79 ≤ 2400915251757^79*5000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      857776639 5000000000 2400915251757 20000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (95/16 : ℝ)) 95 79 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6407138637/10000000000 : ℝ), (904520663/2500000000 : ℝ), (857776639/5000000000 : ℝ)] ![(29273691518247/50000000000000 : ℝ), (14724020343261/50000000000000 : ℝ), (2400915251757/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6407138637/10000000000 : ℝ)|^95 ≤ (29273691518247/50000000000000 : ℝ)^79
        have hw : |(6407138637/10000000000 : ℝ)|=(6407138637/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(904520663/2500000000 : ℝ)|^95 ≤ (14724020343261/50000000000000 : ℝ)^79
        have hw : |(904520663/2500000000 : ℝ)|=(904520663/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(857776639/5000000000 : ℝ)|^95 ≤ (2400915251757/20000000000000 : ℝ)^79
        have hw : |(857776639/5000000000 : ℝ)|=(857776639/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c329063_s1_21 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-276348943/10000000000 : ℝ)*x 0 + (5764243971/10000000000 : ℝ)*x 1 + (5347454617/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (276348943/10000000000 : ℝ)^95 ≤ (16699893669/1250000000000 : ℝ)^79 := by
    have hnat : (276348943 : ℕ)^95*1250000000000^79 ≤ 16699893669^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      276348943 10000000000 16699893669 1250000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5764243971/10000000000 : ℝ)^95 ≤ (51556699719897/100000000000000 : ℝ)^79 := by
    have hnat : (5764243971 : ℕ)^95*100000000000000^79 ≤ 51556699719897^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5764243971 10000000000 51556699719897 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5347454617/10000000000 : ℝ)^95 ≤ (9421461753859/20000000000000 : ℝ)^79 := by
    have hnat : (5347454617 : ℕ)^95*20000000000000^79 ≤ 9421461753859^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5347454617 10000000000 9421461753859 20000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (95/16 : ℝ)) 95 79 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-276348943/10000000000 : ℝ), (5764243971/10000000000 : ℝ), (5347454617/10000000000 : ℝ)] ![(16699893669/1250000000000 : ℝ), (51556699719897/100000000000000 : ℝ), (9421461753859/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-276348943/10000000000 : ℝ)|^95 ≤ (16699893669/1250000000000 : ℝ)^79
        have hw : |(-276348943/10000000000 : ℝ)|=(276348943/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5764243971/10000000000 : ℝ)|^95 ≤ (51556699719897/100000000000000 : ℝ)^79
        have hw : |(5764243971/10000000000 : ℝ)|=(5764243971/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5347454617/10000000000 : ℝ)|^95 ≤ (9421461753859/20000000000000 : ℝ)^79
        have hw : |(5347454617/10000000000 : ℝ)|=(5347454617/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c329063_s1_22 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3038262099/5000000000 : ℝ)*x 0 + (-2159561/80000000 : ℝ)*x 1 + (100604919/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3038262099/5000000000 : ℝ)^95 ≤ (10986732874029/20000000000000 : ℝ)^79 := by
    have hnat : (3038262099 : ℕ)^95*20000000000000^79 ≤ 10986732874029^79*5000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3038262099 5000000000 10986732874029 20000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2159561/80000000 : ℝ)^95 ≤ (1298850399169/100000000000000 : ℝ)^79 := by
    have hnat : (2159561 : ℕ)^95*100000000000000^79 ≤ 1298850399169^79*80000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2159561 80000000 1298850399169 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (100604919/200000000 : ℝ)^95 ≤ (8753497043913/20000000000000 : ℝ)^79 := by
    have hnat : (100604919 : ℕ)^95*20000000000000^79 ≤ 8753497043913^79*200000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      100604919 200000000 8753497043913 20000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (95/16 : ℝ)) 95 79 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3038262099/5000000000 : ℝ), (-2159561/80000000 : ℝ), (100604919/200000000 : ℝ)] ![(10986732874029/20000000000000 : ℝ), (1298850399169/100000000000000 : ℝ), (8753497043913/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3038262099/5000000000 : ℝ)|^95 ≤ (10986732874029/20000000000000 : ℝ)^79
        have hw : |(3038262099/5000000000 : ℝ)|=(3038262099/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2159561/80000000 : ℝ)|^95 ≤ (1298850399169/100000000000000 : ℝ)^79
        have hw : |(-2159561/80000000 : ℝ)|=(2159561/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(100604919/200000000 : ℝ)|^95 ≤ (8753497043913/20000000000000 : ℝ)^79
        have hw : |(100604919/200000000 : ℝ)|=(100604919/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c329063_s1_23 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ)) (x : Fin 3 → ℝ) :
    (7230239/15625000 : ℝ)*x 0 + (762631021/1250000000 : ℝ)*x 1 + (-857304813/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (7230239/15625000 : ℝ)^95 ≤ (7917387285989/20000000000000 : ℝ)^79 := by
    have hnat : (7230239 : ℕ)^95*20000000000000^79 ≤ 7917387285989^79*15625000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7230239 15625000 7917387285989 20000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (762631021/1250000000 : ℝ)^95 ≤ (55200379649331/100000000000000 : ℝ)^79 := by
    have hnat : (762631021 : ℕ)^95*100000000000000^79 ≤ 55200379649331^79*1250000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      762631021 1250000000 55200379649331 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (857304813/10000000000 : ℝ)^95 ≤ (5212683912389/100000000000000 : ℝ)^79 := by
    have hnat : (857304813 : ℕ)^95*100000000000000^79 ≤ 5212683912389^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      857304813 10000000000 5212683912389 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (95/16 : ℝ)) 95 79 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(7230239/15625000 : ℝ), (762631021/1250000000 : ℝ), (-857304813/10000000000 : ℝ)] ![(7917387285989/20000000000000 : ℝ), (55200379649331/100000000000000 : ℝ), (5212683912389/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(7230239/15625000 : ℝ)|^95 ≤ (7917387285989/20000000000000 : ℝ)^79
        have hw : |(7230239/15625000 : ℝ)|=(7230239/15625000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(762631021/1250000000 : ℝ)|^95 ≤ (55200379649331/100000000000000 : ℝ)^79
        have hw : |(762631021/1250000000 : ℝ)|=(762631021/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-857304813/10000000000 : ℝ)|^95 ≤ (5212683912389/100000000000000 : ℝ)^79
        have hw : |(-857304813/10000000000 : ℝ)|=(857304813/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c329063_s1_27 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1655260961/2500000000 : ℝ)*x 0 + (2639578591/10000000000 : ℝ)*x 1 + (1253270741/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1655260961/2500000000 : ℝ)^95 ≤ (60905765463737/100000000000000 : ℝ)^79 := by
    have hnat : (1655260961 : ℕ)^95*100000000000000^79 ≤ 60905765463737^79*2500000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1655260961 2500000000 60905765463737 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2639578591/10000000000 : ℝ)^95 ≤ (10077366456183/50000000000000 : ℝ)^79 := by
    have hnat : (2639578591 : ℕ)^95*50000000000000^79 ≤ 10077366456183^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2639578591 10000000000 10077366456183 50000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1253270741/5000000000 : ℝ)^95 ≤ (18939501602731/100000000000000 : ℝ)^79 := by
    have hnat : (1253270741 : ℕ)^95*100000000000000^79 ≤ 18939501602731^79*5000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1253270741 5000000000 18939501602731 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (95/16 : ℝ)) 95 79 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1655260961/2500000000 : ℝ), (2639578591/10000000000 : ℝ), (1253270741/5000000000 : ℝ)] ![(60905765463737/100000000000000 : ℝ), (10077366456183/50000000000000 : ℝ), (18939501602731/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1655260961/2500000000 : ℝ)|^95 ≤ (60905765463737/100000000000000 : ℝ)^79
        have hw : |(1655260961/2500000000 : ℝ)|=(1655260961/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2639578591/10000000000 : ℝ)|^95 ≤ (10077366456183/50000000000000 : ℝ)^79
        have hw : |(2639578591/10000000000 : ℝ)|=(2639578591/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1253270741/5000000000 : ℝ)|^95 ≤ (18939501602731/100000000000000 : ℝ)^79
        have hw : |(1253270741/5000000000 : ℝ)|=(1253270741/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c329063 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (55589/25000 : ℝ) (160257/100000 : ℝ) (10347/12500 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, true]]) : (0 : ℝ) ≤ ((32949/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(32949/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(419/1250 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(419/1250 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(16027/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(16027/50000 : ℝ)*X 1 2) := by
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
  have main2 : (10347/12500 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (10347/12500 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base7 : ((1 : ℝ)*T) ≤ (160257/100000 : ℝ) := by
    linarith only [f.Tcap]
  have base15 : ((1 : ℝ)*X 1 0+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 0).2]
  have base21 : ((1 : ℝ)*X 2 0+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 0).2]
  have base23 : ((1 : ℝ)*X 2 1+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 1).2]
  have base27 : ((1 : ℝ)*X 0 0+(1 : ℝ)*X 1 0+(1 : ℝ)*X 2 0+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [(f.column 0).2]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base43 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 2+(1 : ℝ)*P 1) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 1,f.sum]
  have base49 : ((-1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.1]
  have base50 : ((-1 : ℝ)*X 0 0+(1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 0+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.2.1]
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
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, true]] hX 0 (by
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
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, true]] hX 1 (by
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
  have major_s0_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(1266528166513657/10000000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(813984837038199/10000000000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (93/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (1266528166513657/10000000000000000 : ℝ)) (beta := (813984837038199/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow2,s0_corner2a]) (by linarith only [s0_pow2,s0_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (1 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order2.2.2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(1266528166513657/10000000000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(813984837038199/10000000000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s0_0 : ((-95271071/5000000000 : ℝ)*X 0 0+(5433103219/10000000000 : ℝ)*X 0 1+(1431125911/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c329063_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_1 : ((1358275739/2500000000 : ℝ)*X 1 0+(-95270637/5000000000 : ℝ)*X 1 1+(286225217/500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c329063_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_7 : ((-152948803/1000000000 : ℝ)*X 0 0+(296510189/2500000000 : ℝ)*X 0 1+(1693021101/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c329063_s0_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_8 : ((2401125197/10000000000 : ℝ)*X 1 0+(-12581779/2500000000 : ℝ)*X 1 1+(1693021301/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c329063_s0_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_9 : ((2401130323/10000000000 : ℝ)*X 2 0+(4232550927/5000000000 : ℝ)*X 2 1+(-50329033/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c329063_s0_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_13 : ((313940759/1000000000 : ℝ)*X 0 0+(715584067/1000000000 : ℝ)*X 0 1+(63128323/500000000 : ℝ)*X 0 2+(313940759/1000000000 : ℝ)*X 1 0+(715584067/1000000000 : ℝ)*X 1 1+(63128323/500000000 : ℝ)*X 1 2+(313940759/1000000000 : ℝ)*X 2 0+(715584067/1000000000 : ℝ)*X 2 1+(63128323/500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c329063_s0_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_14 : ((-687777/312500000 : ℝ)*X 0 0+(93613549/400000000 : ℝ)*X 0 1+(1704276453/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c329063_s0_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_15 : ((215779681/2000000000 : ℝ)*X 1 0+(-1550629243/10000000000 : ℝ)*X 1 1+(8521382831/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c329063_s0_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_16 : ((8163861227/10000000000 : ℝ)*X 2 0+(345563371/1250000000 : ℝ)*X 2 1+(-4432809/500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c329063_s0_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_20 : ((7467464027/10000000000 : ℝ)*X 0 0+(551434359/2000000000 : ℝ)*X 0 1+(317907987/2500000000 : ℝ)*X 0 2+(7467464027/10000000000 : ℝ)*X 1 0+(551434359/2000000000 : ℝ)*X 1 1+(317907987/2500000000 : ℝ)*X 1 2+(7467464027/10000000000 : ℝ)*X 2 0+(551434359/2000000000 : ℝ)*X 2 1+(317907987/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c329063_s0_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_21 : ((-128571057/10000000000 : ℝ)*X 0 0+(1441600377/2000000000 : ℝ)*X 0 1+(3878193371/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c329063_s0_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_22 : ((811632217/1000000000 : ℝ)*X 1 0+(-2919597/2000000000 : ℝ)*X 1 1+(713975093/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c329063_s0_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_23 : ((848467489/10000000000 : ℝ)*X 2 0+(2164380597/2500000000 : ℝ)*X 2 1+(-1567242453/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c329063_s0_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_27 : ((3786900637/5000000000 : ℝ)*X 0 0+(1161094793/5000000000 : ℝ)*X 0 1+(1610933841/10000000000 : ℝ)*X 0 2+(3786900637/5000000000 : ℝ)*X 1 0+(1161094793/5000000000 : ℝ)*X 1 1+(1610933841/10000000000 : ℝ)*X 1 2+(3786900637/5000000000 : ℝ)*X 2 0+(1161094793/5000000000 : ℝ)*X 2 1+(1610933841/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c329063_s0_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s0_0 : (0 : ℝ) ≤ ((60723/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(60723/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (774030179786399219703/156250000000000000000000000 : ℝ) := by norm_num
    linear_combination (238571736587/200000000000 : ℝ)*(base7) + (72581/125000000000 : ℝ)*(base50) + (106983/500000000000 : ℝ)*(base60) + (84462655469/62500000000 : ℝ)*(major_s0_0) + (84462655469/62500000000 : ℝ)*(major_s0_1) + (84462655469/62500000000 : ℝ)*(major_s0_2) + (1701759/500000000000 : ℝ)*(sp_s0_0) + (81271/50000000000 : ℝ)*(sp_s0_1) + (145781132873/100000000000 : ℝ)*(sp_s0_7) + (1457822425019/1000000000000 : ℝ)*(sp_s0_8) + (1457824899199/1000000000000 : ℝ)*(sp_s0_9) + (900311963817/500000000000 : ℝ)*(sp_s0_13) + (10166951/1000000000000 : ℝ)*(sp_s0_14) + (21219/25000000000 : ℝ)*(sp_s0_15) + (607765244699/1000000000000 : ℝ)*(f.failure) + (1457824899199/1000000000000 : ℝ)*(f.sum) + (41736267634867/312500000000000000000000000 : ℝ)*base62 + (36862256802169/625000000000000000000000000 : ℝ)*base64 + (561440160697831/625000000000000000000000000 : ℝ)*base67 + (366560629052633/625000000000000000000000000 : ℝ)*base69 + (4340234999971/39062500000000000000000000 : ℝ)*base70 + (241064617072831/625000000000000000000000000 : ℝ)*base73 + (30704259322367/625000000000000000000000000 : ℝ)*base74 + (319018466365133/625000000000000000000000000 : ℝ)*base77 + (117905933229081/312500000000000000000000000 : ℝ)*base79 + (27289/25000000000000000 : ℝ)*base86 + (27289/25000000000000000 : ℝ)*base88 + (27289/25000000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s0_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(60621/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(60621/100000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (81222718289900670821271/5000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1197091863417/1000000000000 : ℝ)*(base7) + (5389409/1000000000000 : ℝ)*(base27) + (6369/40000000000 : ℝ)*(base49) + (1322948471157/1000000000000 : ℝ)*(major_s0_0) + (1322948471157/1000000000000 : ℝ)*(major_s0_1) + (1322948471157/1000000000000 : ℝ)*(major_s0_2) + (46671/1000000000000 : ℝ)*(sp_s0_0) + (14957/250000000000 : ℝ)*(sp_s0_7) + (44868353/1000000000000 : ℝ)*(sp_s0_8) + (1411448277547/1000000000000 : ℝ)*(sp_s0_14) + (1411403515693/1000000000000 : ℝ)*(sp_s0_15) + (705724192023/500000000000 : ℝ)*(sp_s0_16) + (1791994198773/1000000000000 : ℝ)*(sp_s0_20) + (30458067/500000000000 : ℝ)*(sp_s0_27) + (594968640899/1000000000000 : ℝ)*(f.failure) + (705724192023/500000000000 : ℝ)*(f.sum) + (1124326482591149/5000000000000000000000000000 : ℝ)*base63 + (2467024492273757/10000000000000000000000000000 : ℝ)*base64 + (87238341726243/10000000000000000000000000000 : ℝ)*base67 + (2346902881908851/10000000000000000000000000000 : ℝ)*base68 + (2124266113587/625000000000000000000000000 : ℝ)*base71 + (3685738587273757/10000000000000000000000000000 : ℝ)*base72 + (1785327117908851/10000000000000000000000000000 : ℝ)*base74 + (3519569675908851/10000000000000000000000000000 : ℝ)*base76 + (1944461949726243/5000000000000000000000000000 : ℝ)*base79 + (9511/25000000000000000 : ℝ)*base87 + (9511/25000000000000000 : ℝ)*base89 + (9511/25000000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s0_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(58463/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(58463/100000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (15558393947127704192199/2500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (596977750661/500000000000 : ℝ)*(base7) + (2002919/1000000000000 : ℝ)*(base27) + (140659583281/1000000000000 : ℝ)*(base40) + (418923/500000000000 : ℝ)*(base43) + (44823/1000000000000 : ℝ)*(base49) + (324737876687/250000000000 : ℝ)*(major_s0_0) + (649475334451/500000000000 : ℝ)*(major_s0_1) + (324737876687/250000000000 : ℝ)*(major_s0_2) + (8088167/500000000000 : ℝ)*(sp_s0_9) + (27811511/1000000000000 : ℝ)*(sp_s0_20) + (687962254079/500000000000 : ℝ)*(sp_s0_21) + (343981336501/250000000000 : ℝ)*(sp_s0_22) + (85994270739/62500000000 : ℝ)*(sp_s0_23) + (889051095337/500000000000 : ℝ)*(sp_s0_27) + (584176503781/1000000000000 : ℝ)*(f.failure) + (343981336501/250000000000 : ℝ)*(f.sum) + (58939094582959/200000000000000000000000000 : ℝ)*base62 + (105675589183287/2500000000000000000000000000 : ℝ)*base64 + (1586041347693749/5000000000000000000000000000 : ℝ)*base67 + (587660970835641/2500000000000000000000000000 : ℝ)*base68 + (15320217511423/39062500000000000000000000 : ℝ)*base71 + (1287359266933287/2500000000000000000000000000 : ℝ)*base72 + (1846590911402693/5000000000000000000000000000 : ℝ)*base74 + (1023686528164359/2500000000000000000000000000 : ℝ)*base77 + (20232774206913/200000000000000000000000000 : ℝ)*base78 + (17991/25000000000000000 : ℝ)*base86 + (17991/25000000000000000 : ℝ)*base88 + (17991/25000000000000000 : ℝ)*base90 + (1/1000000000000 : ℝ)*base93 + hcertificate_margin
  have s1_pow0 : (60723/100000 : ℝ) ^ (93/16 : ℝ) ≤ (5504787883156894457/100000000000000000000 : ℝ) := by
    have hpowers : (60723/100000 : ℝ)^93 ≤ (5504787883156894457/100000000000000000000 : ℝ)^16 := by
      have hnat : (60723 : ℕ)^93*100000000000000000000^16 ≤ 5504787883156894457^16*100000^93 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        60723 100000 5504787883156894457 100000000000000000000 93 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (60723/100000 : ℝ)) (X := (5504787883156894457/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 93 16 (by norm_num) hpowers
    exact h
  have s1_corner0a : (105504787883156894457/100000000000000000000 : ℝ) ≤ (2018523498710659/2000000000000000 : ℝ) ^ (93/16 : ℝ) := by
    have hpowers : (105504787883156894457/100000000000000000000 : ℝ)^16 ≤ (2018523498710659/2000000000000000 : ℝ)^93 := by
      have hnat : (105504787883156894457 : ℕ)^16*2000000000000000^93 ≤ 2018523498710659^93*100000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        105504787883156894457 100000000000000000000 2018523498710659 2000000000000000 16 93 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2018523498710659/2000000000000000 : ℝ)) (X := (105504787883156894457/100000000000000000000 : ℝ)) (by norm_num) 93 16 (by norm_num) hpowers
    exact h
  have s1_corner0b : (55504787883156894457/50000000000000000000 : ℝ) ≤ (2036263341674033/2000000000000000 : ℝ) ^ (93/16 : ℝ) := by
    have hpowers : (55504787883156894457/50000000000000000000 : ℝ)^16 ≤ (2036263341674033/2000000000000000 : ℝ)^93 := by
      have hnat : (55504787883156894457 : ℕ)^16*2000000000000000^93 ≤ 2036263341674033^93*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        55504787883156894457 50000000000000000000 2036263341674033 2000000000000000 16 93 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2036263341674033/2000000000000000 : ℝ)) (X := (55504787883156894457/50000000000000000000 : ℝ)) (by norm_num) 93 16 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(18523498710659/1214460000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(8869921481687/607230000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (93/16 : ℝ)) (rho := (60723/100000 : ℝ)) (alpha := (18523498710659/1214460000000000 : ℝ)) (beta := (8869921481687/607230000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (60723/100000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(18523498710659/1214460000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(8869921481687/607230000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (60621/100000 : ℝ) ^ (93/16 : ℝ) ≤ (545125811970088937/10000000000000000000 : ℝ) := by
    have hpowers : (60621/100000 : ℝ)^93 ≤ (545125811970088937/10000000000000000000 : ℝ)^16 := by
      have hnat : (60621 : ℕ)^93*10000000000000000000^16 ≤ 545125811970088937^16*100000^93 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        60621 100000 545125811970088937 10000000000000000000 93 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (60621/100000 : ℝ)) (X := (545125811970088937/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 93 16 (by norm_num) hpowers
    exact h
  have s1_corner1a : (10545125811970088937/10000000000000000000 : ℝ) ≤ (10091736332605731/10000000000000000 : ℝ) ^ (93/16 : ℝ) := by
    have hpowers : (10545125811970088937/10000000000000000000 : ℝ)^16 ≤ (10091736332605731/10000000000000000 : ℝ)^93 := by
      have hnat : (10545125811970088937 : ℕ)^16*10000000000000000^93 ≤ 10091736332605731^93*10000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10545125811970088937 10000000000000000000 10091736332605731 10000000000000000 16 93 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10091736332605731/10000000000000000 : ℝ)) (X := (10545125811970088937/10000000000000000000 : ℝ)) (by norm_num) 93 16 (by norm_num) hpowers
    exact h
  have s1_corner1b : (5545125811970088937/5000000000000000000 : ℝ) ≤ (5089813368559433/5000000000000000 : ℝ) ^ (93/16 : ℝ) := by
    have hpowers : (5545125811970088937/5000000000000000000 : ℝ)^16 ≤ (5089813368559433/5000000000000000 : ℝ)^93 := by
      have hnat : (5545125811970088937 : ℕ)^16*5000000000000000^93 ≤ 5089813368559433^93*5000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5545125811970088937 5000000000000000000 5089813368559433 5000000000000000 16 93 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5089813368559433/5000000000000000 : ℝ)) (X := (5545125811970088937/5000000000000000000 : ℝ)) (by norm_num) 93 16 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(8339666600521/551100000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(17578080902627/1212420000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (93/16 : ℝ)) (rho := (60621/100000 : ℝ)) (alpha := (8339666600521/551100000000000 : ℝ)) (beta := (17578080902627/1212420000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (60621/100000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(8339666600521/551100000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(17578080902627/1212420000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (58463/100000 : ℝ) ^ (93/16 : ℝ) ≤ (883133528310584733/20000000000000000000 : ℝ) := by
    have hpowers : (58463/100000 : ℝ)^93 ≤ (883133528310584733/20000000000000000000 : ℝ)^16 := by
      have hnat : (58463 : ℕ)^93*20000000000000000000^16 ≤ 883133528310584733^16*100000^93 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        58463 100000 883133528310584733 20000000000000000000 93 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (58463/100000 : ℝ)) (X := (883133528310584733/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 93 16 (by norm_num) hpowers
    exact h
  have s1_corner2a : (20883133528310584733/20000000000000000000 : ℝ) ≤ (10074616013569947/10000000000000000 : ℝ) ^ (93/16 : ℝ) := by
    have hpowers : (20883133528310584733/20000000000000000000 : ℝ)^16 ≤ (10074616013569947/10000000000000000 : ℝ)^93 := by
      have hnat : (20883133528310584733 : ℕ)^16*10000000000000000^93 ≤ 10074616013569947^93*20000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20883133528310584733 20000000000000000000 10074616013569947 10000000000000000 16 93 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10074616013569947/10000000000000000 : ℝ)) (X := (20883133528310584733/20000000000000000000 : ℝ)) (by norm_num) 93 16 (by norm_num) hpowers
    exact h
  have s1_corner2b : (10883133528310584733/10000000000000000000 : ℝ) ≤ (10146663586393657/10000000000000000 : ℝ) ^ (93/16 : ℝ) := by
    have hpowers : (10883133528310584733/10000000000000000000 : ℝ)^16 ≤ (10146663586393657/10000000000000000 : ℝ)^93 := by
      have hnat : (10883133528310584733 : ℕ)^16*10000000000000000^93 ≤ 10146663586393657^93*10000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10883133528310584733 10000000000000000000 10146663586393657 10000000000000000 16 93 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10146663586393657/10000000000000000 : ℝ)) (X := (10883133528310584733/10000000000000000000 : ℝ)) (by norm_num) 93 16 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(74616013569947/5846300000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(7204757282371/584630000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (93/16 : ℝ)) (rho := (58463/100000 : ℝ)) (alpha := (74616013569947/5846300000000000 : ℝ)) (beta := (7204757282371/584630000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (58463/100000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(74616013569947/5846300000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(7204757282371/584630000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-979877823/10000000000 : ℝ)*X 0 0+(5321014319/10000000000 : ℝ)*X 0 1+(667769963/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c329063_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_1 : ((5320924171/10000000000 : ℝ)*X 1 0+(-244754663/2500000000 : ℝ)*X 1 1+(66785739/125000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c329063_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((2668042361/5000000000 : ℝ)*X 2 0+(2669876373/5000000000 : ℝ)*X 2 1+(-240500467/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c329063_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_6 : ((4025948183/10000000000 : ℝ)*X 0 0+(4015853419/10000000000 : ℝ)*X 0 1+(1995360191/5000000000 : ℝ)*X 0 2+(4025948183/10000000000 : ℝ)*X 1 0+(4015853419/10000000000 : ℝ)*X 1 1+(1995360191/5000000000 : ℝ)*X 1 2+(4025948183/10000000000 : ℝ)*X 2 0+(4015853419/10000000000 : ℝ)*X 2 1+(1995360191/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c329063_s1_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_7 : ((-882501593/10000000000 : ℝ)*X 0 0+(4656331357/10000000000 : ℝ)*X 0 1+(6056614647/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c329063_s1_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_8 : ((5018878771/10000000000 : ℝ)*X 1 0+(-8136861/250000000 : ℝ)*X 1 1+(6057316693/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c329063_s1_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_9 : ((2393129969/5000000000 : ℝ)*X 2 0+(314671189/500000000 : ℝ)*X 2 1+(-299647777/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c329063_s1_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_13 : ((4516925383/10000000000 : ℝ)*X 0 0+(350258209/625000000 : ℝ)*X 0 1+(1680101251/10000000000 : ℝ)*X 0 2+(4516925383/10000000000 : ℝ)*X 1 0+(350258209/625000000 : ℝ)*X 1 1+(1680101251/10000000000 : ℝ)*X 1 2+(4516925383/10000000000 : ℝ)*X 2 0+(350258209/625000000 : ℝ)*X 2 1+(1680101251/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c329063_s1_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_14 : ((-164669027/5000000000 : ℝ)*X 0 0+(1257016291/2500000000 : ℝ)*X 0 1+(6046330287/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c329063_s1_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_15 : ((2337060049/5000000000 : ℝ)*X 1 0+(-3486867/40000000 : ℝ)*X 1 1+(1209406489/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c329063_s1_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_16 : ((3019410357/5000000000 : ℝ)*X 2 0+(5046957877/10000000000 : ℝ)*X 2 1+(-309932391/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c329063_s1_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_20 : ((6407138637/10000000000 : ℝ)*X 0 0+(904520663/2500000000 : ℝ)*X 0 1+(857776639/5000000000 : ℝ)*X 0 2+(6407138637/10000000000 : ℝ)*X 1 0+(904520663/2500000000 : ℝ)*X 1 1+(857776639/5000000000 : ℝ)*X 1 2+(6407138637/10000000000 : ℝ)*X 2 0+(904520663/2500000000 : ℝ)*X 2 1+(857776639/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c329063_s1_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_21 : ((-276348943/10000000000 : ℝ)*X 0 0+(5764243971/10000000000 : ℝ)*X 0 1+(5347454617/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c329063_s1_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_22 : ((3038262099/5000000000 : ℝ)*X 1 0+(-2159561/80000000 : ℝ)*X 1 1+(100604919/200000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c329063_s1_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_23 : ((7230239/15625000 : ℝ)*X 2 0+(762631021/1250000000 : ℝ)*X 2 1+(-857304813/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c329063_s1_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_27 : ((1655260961/2500000000 : ℝ)*X 0 0+(2639578591/10000000000 : ℝ)*X 0 1+(1253270741/5000000000 : ℝ)*X 0 2+(1655260961/2500000000 : ℝ)*X 1 0+(2639578591/10000000000 : ℝ)*X 1 1+(1253270741/5000000000 : ℝ)*X 1 2+(1655260961/2500000000 : ℝ)*X 2 0+(2639578591/10000000000 : ℝ)*X 2 1+(1253270741/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c329063_s1_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s1_0 : (0 : ℝ) ≤ ((32949/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(32949/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (4130410703556927962367/584630000000000000000000000 : ℝ) := by norm_num
    linear_combination (3781307/1000000000000 : ℝ)*(base23) + (180915287747/1000000000000 : ℝ)*(base60) + (941475943137/200000000000 : ℝ)*(major_s1_0) + (941475943137/200000000000 : ℝ)*(major_s1_1) + (941475943137/200000000000 : ℝ)*(major_s1_2) + (117379/200000000000 : ℝ)*(sp_s1_0) + (1407207/200000000000 : ℝ)*(sp_s1_6) + (7297684671967/1000000000000 : ℝ)*(sp_s1_7) + (1824418988393/250000000000 : ℝ)*(sp_s1_8) + (7297672497613/1000000000000 : ℝ)*(sp_s1_9) + (529259843521/250000000000 : ℝ)*(sp_s1_13) + (25407381/1000000000000 : ℝ)*(sp_s1_14) + (3471267/100000000000 : ℝ)*(sp_s1_15) + (34387323/1000000000000 : ℝ)*(sp_s1_23) + (2117046410119/1000000000000 : ℝ)*(f.failure) + (3648855333121/500000000000 : ℝ)*(f.sum) + (414316722485503933/1073965310000000000000000000000 : ℝ)*base63 + (21565703352307/36539375000000000000000000 : ℝ)*base64 + (55918155191851/80828000000000000000000000 : ℝ)*base66 + (24223191065833/233852000000000000000000000 : ℝ)*base69 + (2782931678548587539/23666991660000000000000000000000 : ℝ)*base71 + (4572585622627/40482000000000000000000000 : ℝ)*base72 + (2859934149663/7348000000000000000000000 : ℝ)*base74 + (10462095099293/16192800000000000000000000 : ℝ)*base76 + (993704323493787079/8180197740000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base81 + (1/1000000000000 : ℝ)*base85 + (19909/25000000000000000 : ℝ)*base86 + (19909/25000000000000000 : ℝ)*base88 + (19909/25000000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s1_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(419/1250 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(419/1250 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (71418408445843800842547607/11833495830000000000000000000000 : ℝ) := by norm_num
    linear_combination (1695169/500000000000 : ℝ)*(base21) + (66247/500000000000 : ℝ)*(base60) + (956043559303/200000000000 : ℝ)*(major_s1_0) + (956043559303/200000000000 : ℝ)*(major_s1_1) + (956043559303/200000000000 : ℝ)*(major_s1_2) + (6423/10000000000 : ℝ)*(sp_s1_1) + (21637/1000000000 : ℝ)*(sp_s1_2) + (13496109/500000000000 : ℝ)*(sp_s1_7) + (693577/31250000000 : ℝ)*(sp_s1_8) + (185265069063/25000000000 : ℝ)*(sp_s1_14) + (7410606917973/1000000000000 : ℝ)*(sp_s1_15) + (37053023637/5000000000 : ℝ)*(sp_s1_16) + (537447188643/250000000000 : ℝ)*(sp_s1_20) + (3767989/250000000000 : ℝ)*(sp_s1_27) + (67181369579/31250000000 : ℝ)*(f.failure) + (3705314877369/500000000000 : ℝ)*(f.sum) + (266350331790482857/805473982500000000000000000000 : ℝ)*base63 + (261301680108233/584630000000000000000000000 : ℝ)*base64 + (503461755143843/1212420000000000000000000000 : ℝ)*base66 + (92854664196253/233852000000000000000000000 : ℝ)*base69 + (923705972545395779/14200194996000000000000000000000 : ℝ)*base70 + (10350706132237/60723000000000000000000000 : ℝ)*base73 + (33939374637353/110220000000000000000000000 : ℝ)*base74 + (64170544035331/242892000000000000000000000 : ℝ)*base76 + (1794395122205839999/24540593220000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base82 + (1251/3125000000000000 : ℝ)*base86 + (1251/3125000000000000 : ℝ)*base88 + (1251/3125000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s1_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(16027/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(16027/50000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (84677566081020271227859095089/21738131839710000000000000000000000 : ℝ) := by norm_num
    linear_combination (2339213/1000000000000 : ℝ)*(base15) + (54271292339/250000000000 : ℝ)*(base40) + (68823502751/15625000000 : ℝ)*(major_s1_0) + (68823502751/15625000000 : ℝ)*(major_s1_1) + (68823502751/15625000000 : ℝ)*(major_s1_2) + (5077299/250000000000 : ℝ)*(sp_s1_0) + (25811039/1000000000000 : ℝ)*(sp_s1_1) + (4490187/250000000000 : ℝ)*(sp_s1_2) + (7198271/1000000000000 : ℝ)*(sp_s1_9) + (24522603/1000000000000 : ℝ)*(sp_s1_20) + (3414231190857/500000000000 : ℝ)*(sp_s1_21) + (3414227270329/500000000000 : ℝ)*(sp_s1_22) + (6828457531891/1000000000000 : ℝ)*(sp_s1_23) + (1980899840159/1000000000000 : ℝ)*(sp_s1_27) + (990462181381/500000000000 : ℝ)*(f.failure) + (682848269091/100000000000 : ℝ)*(f.sum) + (7516336565779307/25775167440000000000000000000 : ℝ)*base63 + (21535924298227/116926000000000000000000000 : ℝ)*base65 + (7617805171799/60621000000000000000000000 : ℝ)*base67 + (204303570684351/730787500000000000000000000 : ℝ)*base69 + (13573608076753728853/35500487490000000000000000000000 : ℝ)*base71 + (20591462108657/151807500000000000000000000 : ℝ)*base72 + (85727678991517/275550000000000000000000000 : ℝ)*base75 + (53946290767753/121446000000000000000000000 : ℝ)*base77 + (1337179135500373769/6135148305000000000000000000000 : ℝ)*base78 + (11591/12500000000000000 : ℝ)*base86 + (11591/12500000000000000 : ℝ)*base88 + (11591/12500000000000000 : ℝ)*base90 + hcertificate_margin
  exact ⟨ratio_s1_0,ratio_s1_1,ratio_s1_2⟩

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
namespace HlawkaSchatten.DiagonalCutoff4
theorem coarse_distinct_p029_positive63 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ)
    (hX : OrderedChart p (55589/25000 : ℝ) (160257/100000 : ℝ) (10347/12500 : ℝ) X (distinctOrders 63) (fun _ _ => true)) :
    ∀ j h, j ≠ h → |pair X j h| ≤ (2/5:ℝ)*pair X j j := by
  have ho : distinctOrders 63=![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] := by decide
  have hs : ![![true, true, true], ![true, true, true], ![true, true, true]]=(fun (_ _ : Fin 3) => true) := by decide
  have hh := collision_c329063 p hpa (by linarith only [hpb]) X (by simpa only [ho,hs] using hX)
  apply positive_chart_tailratio hX (by decide)
  intro j
  have hn := positive_chart_nonnegative hX j j
  fin_cases j
  · change 0 ≤ pair X 0 0 at hn
    change pair X 0 1 ≤ (2/5:ℝ)*pair X 0 0
    simp only [pair0,pair1,pair2,Pi.add_apply] at hn ⊢
    linarith only [hh.1,hn]
  · change 0 ≤ pair X 1 1 at hn
    change pair X 1 0 ≤ (2/5:ℝ)*pair X 1 1
    simp only [pair0,pair1,pair2,Pi.add_apply] at hn ⊢
    linarith only [hh.2.1,hn]
  · change 0 ≤ pair X 2 2 at hn
    change pair X 2 0 ≤ (2/5:ℝ)*pair X 2 2
    simp only [pair0,pair1,pair2,Pi.add_apply] at hn ⊢
    linarith only [hh.2.2,hn]

end HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ)
    (hX : OrderedChart p (55589/25000 : ℝ) (160257/100000 : ℝ) (10347/12500 : ℝ) X (distinctOrders 63) (fun _ _ => true)) :
    ∀ j h, j ≠ h → |pair X j h| ≤ (2/5:ℝ)*pair X j j := by
  exact HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p029_positive63 p hpa hpb X hX

#print axioms solution
