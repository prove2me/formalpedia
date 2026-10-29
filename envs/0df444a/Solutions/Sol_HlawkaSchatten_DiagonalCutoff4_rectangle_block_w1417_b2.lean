-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1417_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:50:15.898996+00:00
-- url     : https://prove2.me/submissions/3033ba75-11df-4f61-93ba-feb806937e9e

import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_rectangle_majorant
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
theorem frame_box_of_interval_base {p k A d ell u v w rho lo : ℝ}
    (base : ∀ X : Fin 3 → Fin 3 → ℝ, Frame p k A d X →
      (∀ i h, i ≠ h → 0 ≤ pair X i h) →
      (∀ i h, i ≠ h → |pair X i h| ≤ rho*pair X i i) →
      (∀ i h, i ≠ h → lo*pair X i i ≤ pair X i h) →
      -u ≤ X 0 0 ∧ X 0 0 ≤ -ell ∧ v ≤ X 0 1 ∧ X 0 1 ≤ w)
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p k A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ rho*pair X i i)
    (hlower : ∀ i h, i ≠ h → lo*pair X i i ≤ pair X i h) :
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
    · intro i j hij
      rw [pair_relabel]
      exact hlower (e i) (e j) (e.injective.ne hij)
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

theorem frame_interval_of_base {p k A d rho lo R L : ℝ}
    (base : ∀ X : Fin 3 → Fin 3 → ℝ, Frame p k A d X →
      (∀ i h, i ≠ h → 0 ≤ pair X i h) →
      (∀ i h, i ≠ h → |pair X i h| ≤ rho*pair X i i) →
      (∀ i h, i ≠ h → lo*pair X i i ≤ pair X i h) →
      L*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ R*pair X 0 0)
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p k A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ rho*pair X i i)
    (hlower : ∀ i h, i ≠ h → lo*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → L*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ R*pair X i i := by
  have permuted (e : Equiv.Perm (Fin 3)) :
      L*pair X (e 0) (e 0) ≤ pair X (e 0) (e 1) ∧
        pair X (e 0) (e 1) ≤ R*pair X (e 0) (e 0) := by
    have hh := base (relabel e X) (frame_relabel hX e)
      (fun i j hij => by rw [pair_relabel];exact hsign (e i) (e j) (e.injective.ne hij))
      (fun i j hij => by rw [pair_relabel];exact hratio (e i) (e j) (e.injective.ne hij))
      (fun i j hij => by rw [pair_relabel];exact hlower (e i) (e j) (e.injective.ne hij))
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


theorem rectangle_pair_majorant {p a lo hi c alpha : ℝ}
    (hp : 1 ≤ p) (ha : 0 < a) (hap : a ≤ p)
    (hlo : 0 ≤ lo) (hlohi : lo < hi) (hhi : hi ≤ 1) (halpha : 0 ≤ alpha)
    (hc : 1 ≤ c+2*alpha*lo)
    (hcorner00 : 1+2*lo^a ≤ (c+2*alpha*lo)^a)
    (hcorner10 : 1+hi^a+lo^a ≤ (c+alpha*(hi+lo))^a)
    (hcorner11 : 1+2*hi^a ≤ (c+2*alpha*hi)^a)
    (X : Fin 3 → Fin 3 → ℝ)
    (hmain : ∀ i, 0 ≤ pair X i i)
    (hlower : ∀ i h, i ≠ h → lo*pair X i i ≤ pair X i h)
    (hupper : ∀ i h, i ≠ h → |pair X i h| ≤ hi*pair X i i)
    (i j l : Fin 3) (hij : i ≠ j) (hil : i ≠ l) (hjl : j ≠ l) :
    lpNorm p (pair X i) ≤ c*pair X i i+alpha*(pair X i j+pair X i l) := by
  have hh := rectangle_majorant hp ha hap hlo hlohi hhi halpha hc hcorner00 hcorner10 hcorner11
    (hmain i) (hlower i j hij) ((le_abs_self _).trans (hupper i j hij))
    (hlower i l hil) ((le_abs_self _).trans (hupper i l hil))
  have he : lpNorm p (pair X i) =
      (|pair X i i|^p+|pair X i j|^p+|pair X i l|^p)^(1/p) := by
    simp only [lpNorm,Real.norm_eq_abs]
    congr 1
    fin_cases i <;> fin_cases j <;> fin_cases l <;> try contradiction
    all_goals simp [Fin.sum_univ_three] <;> ring
  rw [he]
  exact hh

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
theorem support_rectangle_w1417_s6_0 (p : ℝ) (hpa : (547/128 : ℝ) ≤ p) (hpb : p ≤ (4377/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-990453743/5000000000 : ℝ)*x 0 + (1352210737/2500000000 : ℝ)*x 1 + (5246627411/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (990453743/5000000000 : ℝ)^4377 ≤ (6040846806573/50000000000000 : ℝ)^3353 := by
    have hnat : (990453743 : ℕ)^4377*50000000000000^3353 ≤ 6040846806573^3353*5000000000^4377 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      990453743 5000000000 6040846806573 50000000000000 4377 3353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1352210737/2500000000 : ℝ)^4377 ≤ (44832704682317/100000000000000 : ℝ)^3353 := by
    have hnat : (1352210737 : ℕ)^4377*100000000000000^3353 ≤ 44832704682317^3353*2500000000^4377 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1352210737 2500000000 44832704682317 100000000000000 4377 3353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5246627411/10000000000 : ℝ)^4377 ≤ (2154280084461/5000000000000 : ℝ)^3353 := by
    have hnat : (5246627411 : ℕ)^4377*5000000000000^3353 ≤ 2154280084461^3353*10000000000^4377 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5246627411 10000000000 2154280084461 5000000000000 4377 3353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4377/1024 : ℝ)) 4377 3353 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-990453743/5000000000 : ℝ), (1352210737/2500000000 : ℝ), (5246627411/10000000000 : ℝ)] ![(6040846806573/50000000000000 : ℝ), (44832704682317/100000000000000 : ℝ), (2154280084461/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-990453743/5000000000 : ℝ)|^4377 ≤ (6040846806573/50000000000000 : ℝ)^3353
        have hw : |(-990453743/5000000000 : ℝ)|=(990453743/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1352210737/2500000000 : ℝ)|^4377 ≤ (44832704682317/100000000000000 : ℝ)^3353
        have hw : |(1352210737/2500000000 : ℝ)|=(1352210737/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5246627411/10000000000 : ℝ)|^4377 ≤ (2154280084461/5000000000000 : ℝ)^3353
        have hw : |(5246627411/10000000000 : ℝ)|=(5246627411/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1417_s6_1 (p : ℝ) (hpa : (547/128 : ℝ) ≤ p) (hpb : p ≤ (4377/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5347578207/10000000000 : ℝ)*x 0 + (-1031751181/5000000000 : ℝ)*x 1 + (1311656867/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5347578207/10000000000 : ℝ)^4377 ≤ (22085480061083/50000000000000 : ℝ)^3353 := by
    have hnat : (5347578207 : ℕ)^4377*50000000000000^3353 ≤ 22085480061083^3353*10000000000^4377 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5347578207 10000000000 22085480061083 50000000000000 4377 3353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1031751181/5000000000 : ℝ)^4377 ≤ (12743437568351/100000000000000 : ℝ)^3353 := by
    have hnat : (1031751181 : ℕ)^4377*100000000000000^3353 ≤ 12743437568351^3353*5000000000^4377 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1031751181 5000000000 12743437568351 100000000000000 4377 3353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1311656867/2500000000 : ℝ)^4377 ≤ (2154280115013/5000000000000 : ℝ)^3353 := by
    have hnat : (1311656867 : ℕ)^4377*5000000000000^3353 ≤ 2154280115013^3353*2500000000^4377 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1311656867 2500000000 2154280115013 5000000000000 4377 3353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4377/1024 : ℝ)) 4377 3353 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5347578207/10000000000 : ℝ), (-1031751181/5000000000 : ℝ), (1311656867/2500000000 : ℝ)] ![(22085480061083/50000000000000 : ℝ), (12743437568351/100000000000000 : ℝ), (2154280115013/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5347578207/10000000000 : ℝ)|^4377 ≤ (22085480061083/50000000000000 : ℝ)^3353
        have hw : |(5347578207/10000000000 : ℝ)|=(5347578207/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1031751181/5000000000 : ℝ)|^4377 ≤ (12743437568351/100000000000000 : ℝ)^3353
        have hw : |(-1031751181/5000000000 : ℝ)|=(1031751181/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1311656867/2500000000 : ℝ)|^4377 ≤ (2154280115013/5000000000000 : ℝ)^3353
        have hw : |(1311656867/2500000000 : ℝ)|=(1311656867/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1417_s6_2 (p : ℝ) (hpa : (547/128 : ℝ) ≤ p) (hpb : p ≤ (4377/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5347578217/10000000000 : ℝ)*x 0 + (2623313727/5000000000 : ℝ)*x 1 + (-1031751183/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5347578217/10000000000 : ℝ)^4377 ≤ (5521370028749/12500000000000 : ℝ)^3353 := by
    have hnat : (5347578217 : ℕ)^4377*12500000000000^3353 ≤ 5521370028749^3353*10000000000^4377 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5347578217 10000000000 5521370028749 12500000000000 4377 3353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2623313727/5000000000 : ℝ)^4377 ≤ (2154280107509/5000000000000 : ℝ)^3353 := by
    have hnat : (2623313727 : ℕ)^4377*5000000000000^3353 ≤ 2154280107509^3353*5000000000^4377 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2623313727 5000000000 2154280107509 5000000000000 4377 3353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1031751183/5000000000 : ℝ)^4377 ≤ (6371718800299/50000000000000 : ℝ)^3353 := by
    have hnat : (1031751183 : ℕ)^4377*50000000000000^3353 ≤ 6371718800299^3353*5000000000^4377 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1031751183 5000000000 6371718800299 50000000000000 4377 3353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4377/1024 : ℝ)) 4377 3353 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5347578217/10000000000 : ℝ), (2623313727/5000000000 : ℝ), (-1031751183/5000000000 : ℝ)] ![(5521370028749/12500000000000 : ℝ), (2154280107509/5000000000000 : ℝ), (6371718800299/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5347578217/10000000000 : ℝ)|^4377 ≤ (5521370028749/12500000000000 : ℝ)^3353
        have hw : |(5347578217/10000000000 : ℝ)|=(5347578217/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2623313727/5000000000 : ℝ)|^4377 ≤ (2154280107509/5000000000000 : ℝ)^3353
        have hw : |(2623313727/5000000000 : ℝ)|=(2623313727/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1031751183/5000000000 : ℝ)|^4377 ≤ (6371718800299/50000000000000 : ℝ)^3353
        have hw : |(-1031751183/5000000000 : ℝ)|=(1031751183/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1417_s6_3 (p : ℝ) (hpa : (547/128 : ℝ) ≤ p) (hpb : p ≤ (4377/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4307382767/10000000000 : ℝ)*x 0 + (4135893683/10000000000 : ℝ)*x 1 + (4485277843/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4307382767/10000000000 : ℝ)^4377 ≤ (33304501315583/100000000000000 : ℝ)^3353 := by
    have hnat : (4307382767 : ℕ)^4377*100000000000000^3353 ≤ 33304501315583^3353*10000000000^4377 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4307382767 10000000000 33304501315583 100000000000000 4377 3353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4135893683/10000000000 : ℝ)^4377 ≤ (7896058702933/25000000000000 : ℝ)^3353 := by
    have hnat : (4135893683 : ℕ)^4377*25000000000000^3353 ≤ 7896058702933^3353*10000000000^4377 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4135893683 10000000000 7896058702933 25000000000000 4377 3353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4485277843/10000000000 : ℝ)^4377 ≤ (3511126385109/10000000000000 : ℝ)^3353 := by
    have hnat : (4485277843 : ℕ)^4377*10000000000000^3353 ≤ 3511126385109^3353*10000000000^4377 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4485277843 10000000000 3511126385109 10000000000000 4377 3353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4377/1024 : ℝ)) 4377 3353 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4307382767/10000000000 : ℝ), (4135893683/10000000000 : ℝ), (4485277843/10000000000 : ℝ)] ![(33304501315583/100000000000000 : ℝ), (7896058702933/25000000000000 : ℝ), (3511126385109/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4307382767/10000000000 : ℝ)|^4377 ≤ (33304501315583/100000000000000 : ℝ)^3353
        have hw : |(4307382767/10000000000 : ℝ)|=(4307382767/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4135893683/10000000000 : ℝ)|^4377 ≤ (7896058702933/25000000000000 : ℝ)^3353
        have hw : |(4135893683/10000000000 : ℝ)|=(4135893683/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4485277843/10000000000 : ℝ)|^4377 ≤ (3511126385109/10000000000000 : ℝ)^3353
        have hw : |(4485277843/10000000000 : ℝ)|=(4485277843/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1417_s6_4 (p : ℝ) (hpa : (547/128 : ℝ) ≤ p) (hpb : p ≤ (4377/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1980918929/10000000000 : ℝ)*x 0 + (524721191/1000000000 : ℝ)*x 1 + (270412771/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1980918929/10000000000 : ℝ)^4377 ≤ (12081784719129/100000000000000 : ℝ)^3353 := by
    have hnat : (1980918929 : ℕ)^4377*100000000000000^3353 ≤ 12081784719129^3353*10000000000^4377 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1980918929 10000000000 12081784719129 100000000000000 4377 3353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (524721191/1000000000 : ℝ)^4377 ≤ (10772966906799/25000000000000 : ℝ)^3353 := by
    have hnat : (524721191 : ℕ)^4377*25000000000000^3353 ≤ 10772966906799^3353*1000000000^4377 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      524721191 1000000000 10772966906799 25000000000000 4377 3353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (270412771/500000000 : ℝ)^4377 ≤ (11206586910643/25000000000000 : ℝ)^3353 := by
    have hnat : (270412771 : ℕ)^4377*25000000000000^3353 ≤ 11206586910643^3353*500000000^4377 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      270412771 500000000 11206586910643 25000000000000 4377 3353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4377/1024 : ℝ)) 4377 3353 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1980918929/10000000000 : ℝ), (524721191/1000000000 : ℝ), (270412771/500000000 : ℝ)] ![(12081784719129/100000000000000 : ℝ), (10772966906799/25000000000000 : ℝ), (11206586910643/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1980918929/10000000000 : ℝ)|^4377 ≤ (12081784719129/100000000000000 : ℝ)^3353
        have hw : |(-1980918929/10000000000 : ℝ)|=(1980918929/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(524721191/1000000000 : ℝ)|^4377 ≤ (10772966906799/25000000000000 : ℝ)^3353
        have hw : |(524721191/1000000000 : ℝ)|=(524721191/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(270412771/500000000 : ℝ)|^4377 ≤ (11206586910643/25000000000000 : ℝ)^3353
        have hw : |(270412771/500000000 : ℝ)|=(270412771/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1417_s6_5 (p : ℝ) (hpa : (547/128 : ℝ) ≤ p) (hpb : p ≤ (4377/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1061091327/2000000000 : ℝ)*x 0 + (-475468597/2500000000 : ℝ)*x 1 + (270412771/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1061091327/2000000000 : ℝ)^4377 ≤ (8743465635577/20000000000000 : ℝ)^3353 := by
    have hnat : (1061091327 : ℕ)^4377*20000000000000^3353 ≤ 8743465635577^3353*2000000000^4377 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1061091327 2000000000 8743465635577 20000000000000 4377 3353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (475468597/2500000000 : ℝ)^4377 ≤ (2291264832271/20000000000000 : ℝ)^3353 := by
    have hnat : (475468597 : ℕ)^4377*20000000000000^3353 ≤ 2291264832271^3353*2500000000^4377 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      475468597 2500000000 2291264832271 20000000000000 4377 3353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (270412771/500000000 : ℝ)^4377 ≤ (11206586910643/25000000000000 : ℝ)^3353 := by
    have hnat : (270412771 : ℕ)^4377*25000000000000^3353 ≤ 11206586910643^3353*500000000^4377 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      270412771 500000000 11206586910643 25000000000000 4377 3353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4377/1024 : ℝ)) 4377 3353 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1061091327/2000000000 : ℝ), (-475468597/2500000000 : ℝ), (270412771/500000000 : ℝ)] ![(8743465635577/20000000000000 : ℝ), (2291264832271/20000000000000 : ℝ), (11206586910643/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1061091327/2000000000 : ℝ)|^4377 ≤ (8743465635577/20000000000000 : ℝ)^3353
        have hw : |(1061091327/2000000000 : ℝ)|=(1061091327/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-475468597/2500000000 : ℝ)|^4377 ≤ (2291264832271/20000000000000 : ℝ)^3353
        have hw : |(-475468597/2500000000 : ℝ)|=(475468597/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(270412771/500000000 : ℝ)|^4377 ≤ (11206586910643/25000000000000 : ℝ)^3353
        have hw : |(270412771/500000000 : ℝ)|=(270412771/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1417_s6_6 (p : ℝ) (hpa : (547/128 : ℝ) ≤ p) (hpb : p ≤ (4377/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1061091327/2000000000 : ℝ)*x 0 + (270412771/500000000 : ℝ)*x 1 + (-475468597/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1061091327/2000000000 : ℝ)^4377 ≤ (8743465635577/20000000000000 : ℝ)^3353 := by
    have hnat : (1061091327 : ℕ)^4377*20000000000000^3353 ≤ 8743465635577^3353*2000000000^4377 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1061091327 2000000000 8743465635577 20000000000000 4377 3353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (270412771/500000000 : ℝ)^4377 ≤ (11206586910643/25000000000000 : ℝ)^3353 := by
    have hnat : (270412771 : ℕ)^4377*25000000000000^3353 ≤ 11206586910643^3353*500000000^4377 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      270412771 500000000 11206586910643 25000000000000 4377 3353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (475468597/2500000000 : ℝ)^4377 ≤ (2291264832271/20000000000000 : ℝ)^3353 := by
    have hnat : (475468597 : ℕ)^4377*20000000000000^3353 ≤ 2291264832271^3353*2500000000^4377 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      475468597 2500000000 2291264832271 20000000000000 4377 3353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4377/1024 : ℝ)) 4377 3353 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1061091327/2000000000 : ℝ), (270412771/500000000 : ℝ), (-475468597/2500000000 : ℝ)] ![(8743465635577/20000000000000 : ℝ), (11206586910643/25000000000000 : ℝ), (2291264832271/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1061091327/2000000000 : ℝ)|^4377 ≤ (8743465635577/20000000000000 : ℝ)^3353
        have hw : |(1061091327/2000000000 : ℝ)|=(1061091327/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(270412771/500000000 : ℝ)|^4377 ≤ (11206586910643/25000000000000 : ℝ)^3353
        have hw : |(270412771/500000000 : ℝ)|=(270412771/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-475468597/2500000000 : ℝ)|^4377 ≤ (2291264832271/20000000000000 : ℝ)^3353
        have hw : |(-475468597/2500000000 : ℝ)|=(475468597/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1417_s6_7 (p : ℝ) (hpa : (547/128 : ℝ) ≤ p) (hpb : p ≤ (4377/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4307407371/10000000000 : ℝ)*x 0 + (2242009471/5000000000 : ℝ)*x 1 + (4137159127/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4307407371/10000000000 : ℝ)^4377 ≤ (33304749650941/100000000000000 : ℝ)^3353 := by
    have hnat : (4307407371 : ℕ)^4377*100000000000000^3353 ≤ 33304749650941^3353*10000000000^4377 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4307407371 10000000000 33304749650941 100000000000000 4377 3353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2242009471/5000000000 : ℝ)^4377 ≤ (17549199969427/50000000000000 : ℝ)^3353 := by
    have hnat : (2242009471 : ℕ)^4377*50000000000000^3353 ≤ 17549199969427^3353*5000000000^4377 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2242009471 5000000000 17549199969427 50000000000000 4377 3353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4137159127/10000000000 : ℝ)^4377 ≤ (31596850391277/100000000000000 : ℝ)^3353 := by
    have hnat : (4137159127 : ℕ)^4377*100000000000000^3353 ≤ 31596850391277^3353*10000000000^4377 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4137159127 10000000000 31596850391277 100000000000000 4377 3353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4377/1024 : ℝ)) 4377 3353 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4307407371/10000000000 : ℝ), (2242009471/5000000000 : ℝ), (4137159127/10000000000 : ℝ)] ![(33304749650941/100000000000000 : ℝ), (17549199969427/50000000000000 : ℝ), (31596850391277/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4307407371/10000000000 : ℝ)|^4377 ≤ (33304749650941/100000000000000 : ℝ)^3353
        have hw : |(4307407371/10000000000 : ℝ)|=(4307407371/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2242009471/5000000000 : ℝ)|^4377 ≤ (17549199969427/50000000000000 : ℝ)^3353
        have hw : |(2242009471/5000000000 : ℝ)|=(2242009471/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4137159127/10000000000 : ℝ)|^4377 ≤ (31596850391277/100000000000000 : ℝ)^3353
        have hw : |(4137159127/10000000000 : ℝ)|=(4137159127/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1417_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (547/128 : ℝ) ≤ p) (hpb : p ≤ (4377/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (19711417/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2951/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11311/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (2263/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14751/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (2951/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11311/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (2951/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11311/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (2951/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11311/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (2951/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11311/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (2951/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11311/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (2951/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11311/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hlower 2 1 (by decide)
  have fm0 := f.main 0
  simp only [pair0,pair1,pair2,Pi.add_apply] at fm0
  have fx01 := abs_le.mp (f.maximal 0 1)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx01
  have fx02 := abs_le.mp (f.maximal 0 2)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx02
  have fm1 := f.main 1
  simp only [pair0,pair1,pair2,Pi.add_apply] at fm1
  have fx10 := abs_le.mp (f.maximal 1 0)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx10
  have fx12 := abs_le.mp (f.maximal 1 2)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx12
  have fm2 := f.main 2
  simp only [pair0,pair1,pair2,Pi.add_apply] at fm2
  have fx20 := abs_le.mp (f.maximal 2 0)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx20
  have fx21 := abs_le.mp (f.maximal 2 1)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx21
  have base19 : ((1 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 2).2]
  have base23 : ((1 : ℝ)*X 2 1+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 1).2]
  have base65 : ((1 : ℝ)*X 0 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 0).2]
  have base66 : ((-1 : ℝ)*X 0 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 0).1]
  have base67 : ((1 : ℝ)*X 0 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 1).2]
  have base68 : ((-1 : ℝ)*X 0 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 1).1]
  have base69 : ((1 : ℝ)*X 0 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 2).2]
  have base70 : ((-1 : ℝ)*X 0 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 2).1]
  have base71 : ((1 : ℝ)*X 1 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 0).2]
  have base72 : ((-1 : ℝ)*X 1 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 0).1]
  have base73 : ((1 : ℝ)*X 1 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 1).2]
  have base74 : ((-1 : ℝ)*X 1 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 1).1]
  have base75 : ((1 : ℝ)*X 1 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 2).2]
  have base76 : ((-1 : ℝ)*X 1 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 2).1]
  have base77 : ((1 : ℝ)*X 2 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 0).2]
  have base78 : ((-1 : ℝ)*X 2 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 0).1]
  have base79 : ((1 : ℝ)*X 2 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 1).2]
  have base80 : ((-1 : ℝ)*X 2 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 1).1]
  have base81 : ((1 : ℝ)*X 2 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 2).2]
  have base82 : ((-1 : ℝ)*X 2 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 2).1]
  have base83 : ((1 : ℝ)*N 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 0).2]
  have base84 : ((-1 : ℝ)*N 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 0).1]
  have base85 : ((1 : ℝ)*N 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 1).2]
  have base86 : ((-1 : ℝ)*N 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 1).1]
  have base87 : ((1 : ℝ)*N 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 2).2]
  have base88 : ((-1 : ℝ)*N 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 2).1]
  have base89 : ((1 : ℝ)*P 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 0).2]
  have base90 : ((-1 : ℝ)*P 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 0).1]
  have base91 : ((1 : ℝ)*P 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 1).2]
  have base92 : ((-1 : ℝ)*P 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 1).1]
  have base93 : ((1 : ℝ)*P 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 2).2]
  have base94 : ((-1 : ℝ)*P 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 2).1]
  have base95 : ((1 : ℝ)*T) ≤ (3 : ℝ) := by
    linarith only [bounds.2.2.2.2]
  have base96 : ((-1 : ℝ)*T) ≤ (3 : ℝ) := by
    linarith only [bounds.2.2.2.1]
  have hpowlo : (11311/100000 : ℝ) ^ (547/128 : ℝ) ≤ (1127471838049571/12500000000000000000 : ℝ) := by
    have hpowers : (11311/100000 : ℝ)^547 ≤ (1127471838049571/12500000000000000000 : ℝ)^128 := by
      have hnat : (11311 : ℕ)^547*12500000000000000000^128 ≤ 1127471838049571^128*100000^547 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11311 100000 1127471838049571 12500000000000000000 547 128 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11311/100000 : ℝ)) (X := (1127471838049571/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 547 128 (by norm_num) hpowers
    exact h
  have hpowhi : (2951/20000 : ℝ) ^ (547/128 : ℝ) ≤ (1404376895592091/5000000000000000000 : ℝ) := by
    have hpowers : (2951/20000 : ℝ)^547 ≤ (1404376895592091/5000000000000000000 : ℝ)^128 := by
      have hnat : (2951 : ℕ)^547*5000000000000000000^128 ≤ 1404376895592091^128*20000^547 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2951 20000 1404376895592091 5000000000000000000 547 128 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2951/20000 : ℝ)) (X := (1404376895592091/5000000000000000000 : ℝ)) (by norm_num) (by norm_num) 547 128 (by norm_num) hpowers
    exact h
  have hcorner00 : (6251127471838049571/6250000000000000000 : ℝ) ≤ (1000042210288949/1000000000000000 : ℝ) ^ (547/128 : ℝ) := by
    have hpowers : (6251127471838049571/6250000000000000000 : ℝ)^128 ≤ (1000042210288949/1000000000000000 : ℝ)^547 := by
      have hnat : (6251127471838049571 : ℕ)^128*1000000000000000^547 ≤ 1000042210288949^547*6250000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6251127471838049571 6250000000000000000 1000042210288949 1000000000000000 128 547 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000042210288949/1000000000000000 : ℝ)) (X := (6251127471838049571/6250000000000000000 : ℝ)) (by norm_num) 547 128 (by norm_num) hpowers
    exact h
  have hcorner10 : (25009276828154059597/25000000000000000000 : ℝ) ≤ (5000434100651577/5000000000000000 : ℝ) ^ (547/128 : ℝ) := by
    have hpowers : (25009276828154059597/25000000000000000000 : ℝ)^128 ≤ (5000434100651577/5000000000000000 : ℝ)^547 := by
      have hnat : (25009276828154059597 : ℕ)^128*5000000000000000^547 ≤ 5000434100651577^547*25000000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25009276828154059597 25000000000000000000 5000434100651577 5000000000000000 128 547 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000434100651577/5000000000000000 : ℝ)) (X := (25009276828154059597/25000000000000000000 : ℝ)) (by norm_num) 547 128 (by norm_num) hpowers
    exact h
  have hcorner11 : (2501404376895592091/2500000000000000000 : ℝ) ≤ (5000657149858409/5000000000000000 : ℝ) ^ (547/128 : ℝ) := by
    have hpowers : (2501404376895592091/2500000000000000000 : ℝ)^128 ≤ (5000657149858409/5000000000000000 : ℝ)^547 := by
      have hnat : (2501404376895592091 : ℕ)^128*5000000000000000^547 ≤ 5000657149858409^547*2500000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2501404376895592091 2500000000000000000 5000657149858409 5000000000000000 128 547 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000657149858409/5000000000000000 : ℝ)) (X := (2501404376895592091/2500000000000000000 : ℝ)) (by norm_num) 547 128 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1127471838049571/12500000000000000000 : ℝ) ≤ ((4303920260504687069/4305000000000000000 : ℝ)+2*(13940575427/10762500000000 : ℝ)*(11311/100000 : ℝ))^(547/128 : ℝ) := by
    rw [show (4303920260504687069/4305000000000000000 : ℝ)+2*(13940575427/10762500000000 : ℝ)*(11311/100000 : ℝ)=(1000042210288949/1000000000000000 : ℝ) by norm_num, show 1+2*(1127471838049571/12500000000000000000 : ℝ)=(6251127471838049571/6250000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1404376895592091/5000000000000000000 : ℝ)+(1127471838049571/12500000000000000000 : ℝ) ≤ ((4303920260504687069/4305000000000000000 : ℝ)+(13940575427/10762500000000 : ℝ)*((2951/20000 : ℝ)+(11311/100000 : ℝ)))^(547/128 : ℝ) := by
    rw [show (4303920260504687069/4305000000000000000 : ℝ)+(13940575427/10762500000000 : ℝ)*((2951/20000 : ℝ)+(11311/100000 : ℝ))=(5000434100651577/5000000000000000 : ℝ) by norm_num, show 1+(1404376895592091/5000000000000000000 : ℝ)+(1127471838049571/12500000000000000000 : ℝ)=(25009276828154059597/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1404376895592091/5000000000000000000 : ℝ) ≤ ((4303920260504687069/4305000000000000000 : ℝ)+2*(13940575427/10762500000000 : ℝ)*(2951/20000 : ℝ))^(547/128 : ℝ) := by
    rw [show (4303920260504687069/4305000000000000000 : ℝ)+2*(13940575427/10762500000000 : ℝ)*(2951/20000 : ℝ)=(5000657149858409/5000000000000000 : ℝ) by norm_num, show 1+2*(1404376895592091/5000000000000000000 : ℝ)=(2501404376895592091/2500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (4303920260504687069/4305000000000000000 : ℝ)*(X 1 0+X 2 0)+(13940575427/10762500000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (547/128 : ℝ)) (lo := (11311/100000 : ℝ)) (hi := (2951/20000 : ℝ)) (c := (4303920260504687069/4305000000000000000 : ℝ)) (alpha := (13940575427/10762500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (4303920260504687069/4305000000000000000 : ℝ)*(X 0 1+X 2 1)+(13940575427/10762500000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (547/128 : ℝ)) (lo := (11311/100000 : ℝ)) (hi := (2951/20000 : ℝ)) (c := (4303920260504687069/4305000000000000000 : ℝ)) (alpha := (13940575427/10762500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (4303920260504687069/4305000000000000000 : ℝ)*(X 0 2+X 1 2)+(13940575427/10762500000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (547/128 : ℝ)) (lo := (11311/100000 : ℝ)) (hi := (2951/20000 : ℝ)) (c := (4303920260504687069/4305000000000000000 : ℝ)) (alpha := (13940575427/10762500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-990453743/5000000000 : ℝ)*X 0 0+(1352210737/2500000000 : ℝ)*X 0 1+(5246627411/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1417_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5347578207/10000000000 : ℝ)*X 1 0+(-1031751181/5000000000 : ℝ)*X 1 1+(1311656867/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1417_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5347578217/10000000000 : ℝ)*X 2 0+(2623313727/5000000000 : ℝ)*X 2 1+(-1031751183/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1417_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4307382767/10000000000 : ℝ)*X 0 0+(4135893683/10000000000 : ℝ)*X 0 1+(4485277843/10000000000 : ℝ)*X 0 2+(4307382767/10000000000 : ℝ)*X 1 0+(4135893683/10000000000 : ℝ)*X 1 1+(4485277843/10000000000 : ℝ)*X 1 2+(4307382767/10000000000 : ℝ)*X 2 0+(4135893683/10000000000 : ℝ)*X 2 1+(4485277843/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1417_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1980918929/10000000000 : ℝ)*X 0 0+(524721191/1000000000 : ℝ)*X 0 1+(270412771/500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1417_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1061091327/2000000000 : ℝ)*X 1 0+(-475468597/2500000000 : ℝ)*X 1 1+(270412771/500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1417_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1061091327/2000000000 : ℝ)*X 2 0+(270412771/500000000 : ℝ)*X 2 1+(-475468597/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1417_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4307407371/10000000000 : ℝ)*X 0 0+(2242009471/5000000000 : ℝ)*X 0 1+(4137159127/10000000000 : ℝ)*X 0 2+(4307407371/10000000000 : ℝ)*X 1 0+(2242009471/5000000000 : ℝ)*X 1 1+(4137159127/10000000000 : ℝ)*X 1 2+(4307407371/10000000000 : ℝ)*X 2 0+(2242009471/5000000000 : ℝ)*X 2 1+(4137159127/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1417_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (9706224783701735319046673/1281250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1359471651/100000000000000 : ℝ)*(base19) + (1254732879/100000000000000 : ℝ)*(base23) + (2486983/4000000000000 : ℝ)*(lower2) + (201529431/100000000000000 : ℝ)*(upper3) + (56502297/50000000000000 : ℝ)*(upper5) + (564181645062119/12500000000000 : ℝ)*(major0) + (564181645062119/12500000000000 : ℝ)*(major1) + (564181645062119/12500000000000 : ℝ)*(major2) + (3082334468051613/50000000000000 : ℝ)*(sp0) + (6164697263124287/100000000000000 : ℝ)*(sp1) + (6164697367863059/100000000000000 : ℝ)*(sp2) + (1431096118790893/50000000000000 : ℝ)*(sp3) + (3710811589/12500000000000 : ℝ)*(sp4) + (15208296503/100000000000000 : ℝ)*(sp7) + (286220744587829/10000000000000 : ℝ)*(f.failure) + (3082349311297969/50000000000000 : ℝ)*(f.sum) + (3316366345111/615000000000000000000000000 : ℝ)*base65 + (30801803589534173/7687500000000000000000000000000 : ℝ)*base67 + (37502091877903327/7687500000000000000000000000000 : ℝ)*base70 + (28349288872715827/7687500000000000000000000000000 : ℝ)*base72 + (1682216887013/307500000000000000000000000 : ℝ)*base73 + (69408971376028327/7687500000000000000000000000000 : ℝ)*base76 + (14925164151590827/7687500000000000000000000000000 : ℝ)*base78 + (95553065526159173/7687500000000000000000000000000 : ℝ)*base79 + (4378721838301/615000000000000000000000000 : ℝ)*base81 + (543693/125000000000000000000 : ℝ)*base89 + (543693/125000000000000000000 : ℝ)*base91 + (543693/125000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (57793571904195257054666199/7175000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (682107659/50000000000000 : ℝ)*(base19) + (370374341/25000000000000 : ℝ)*(base23) + (462495627/100000000000000 : ℝ)*(lower1) + (20489651/12500000000000 : ℝ)*(upper3) + (26623367/50000000000000 : ℝ)*(lower4) + (20672203/12500000000000 : ℝ)*(upper5) + (454623390830229/10000000000000 : ℝ)*(major0) + (454623390830229/10000000000000 : ℝ)*(major1) + (454623390830229/10000000000000 : ℝ)*(major2) + (2131153867/100000000000000 : ℝ)*(sp2) + (3104736091422909/50000000000000 : ℝ)*(sp4) + (12418941637261/200000000000 : ℝ)*(sp5) + (1552367142548647/25000000000000 : ℝ)*(sp6) + (360374420657953/12500000000000 : ℝ)*(sp7) + (360374420657953/12500000000000 : ℝ)*(f.failure) + (3104736091422909/50000000000000 : ℝ)*(f.sum) + (349087339929/143500000000000000000000000 : ℝ)*base66 + (72570434184305181/2050000000000000000000000000000 : ℝ)*base67 + (8421687363305181/2050000000000000000000000000000 : ℝ)*base69 + (214891721461505181/2050000000000000000000000000000 : ℝ)*base71 + (4751598491/3587500000000000000000000 : ℝ)*base73 + (126543760661305181/2050000000000000000000000000000 : ℝ)*base75 + (7639548527444819/2050000000000000000000000000000 : ℝ)*base78 + (18455386171594819/2050000000000000000000000000000 : ℝ)*base80 + (307618712871/143500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (2175599/156250000000000000000 : ℝ)*base90 + (2175599/156250000000000000000 : ℝ)*base92 + (2175599/156250000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1417_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (547/128 : ℝ) ≤ p) (hpb : p ≤ (4377/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (19711417/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2951/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11311/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2263/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14751/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1417_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1417_s7_0 (p : ℝ) (hpa : (547/128 : ℝ) ≤ p) (hpb : p ≤ (4377/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1980910299/10000000000 : ℝ)*x 0 + (5408813579/10000000000 : ℝ)*x 1 + (1049330993/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1980910299/10000000000 : ℝ)^4377 ≤ (2416343201891/20000000000000 : ℝ)^3353 := by
    have hnat : (1980910299 : ℕ)^4377*20000000000000^3353 ≤ 2416343201891^3353*10000000000^4377 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1980910299 10000000000 2416343201891 20000000000000 4377 3353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5408813579/10000000000 : ℝ)^4377 ≤ (4483238690539/10000000000000 : ℝ)^3353 := by
    have hnat : (5408813579 : ℕ)^4377*10000000000000^3353 ≤ 4483238690539^3353*10000000000^4377 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5408813579 10000000000 4483238690539 10000000000000 4377 3353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1049330993/2000000000 : ℝ)^4377 ≤ (10771474267109/25000000000000 : ℝ)^3353 := by
    have hnat : (1049330993 : ℕ)^4377*25000000000000^3353 ≤ 10771474267109^3353*2000000000^4377 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1049330993 2000000000 10771474267109 25000000000000 4377 3353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4377/1024 : ℝ)) 4377 3353 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1980910299/10000000000 : ℝ), (5408813579/10000000000 : ℝ), (1049330993/2000000000 : ℝ)] ![(2416343201891/20000000000000 : ℝ), (4483238690539/10000000000000 : ℝ), (10771474267109/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1980910299/10000000000 : ℝ)|^4377 ≤ (2416343201891/20000000000000 : ℝ)^3353
        have hw : |(-1980910299/10000000000 : ℝ)|=(1980910299/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5408813579/10000000000 : ℝ)|^4377 ≤ (4483238690539/10000000000000 : ℝ)^3353
        have hw : |(5408813579/10000000000 : ℝ)|=(5408813579/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1049330993/2000000000 : ℝ)|^4377 ≤ (10771474267109/25000000000000 : ℝ)^3353
        have hw : |(1049330993/2000000000 : ℝ)|=(1049330993/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1417_s7_1 (p : ℝ) (hpa : (547/128 : ℝ) ≤ p) (hpb : p ≤ (4377/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2673785399/5000000000 : ℝ)*x 0 + (-2063475687/10000000000 : ℝ)*x 1 + (262332749/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2673785399/5000000000 : ℝ)^4377 ≤ (690170003657/1562500000000 : ℝ)^3353 := by
    have hnat : (2673785399 : ℕ)^4377*1562500000000^3353 ≤ 690170003657^3353*5000000000^4377 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2673785399 5000000000 690170003657 1562500000000 4377 3353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2063475687/10000000000 : ℝ)^4377 ≤ (6371611261963/50000000000000 : ℝ)^3353 := by
    have hnat : (2063475687 : ℕ)^4377*50000000000000^3353 ≤ 6371611261963^3353*10000000000^4377 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2063475687 10000000000 6371611261963 50000000000000 4377 3353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (262332749/500000000 : ℝ)^4377 ≤ (10771474307309/25000000000000 : ℝ)^3353 := by
    have hnat : (262332749 : ℕ)^4377*25000000000000^3353 ≤ 10771474307309^3353*500000000^4377 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      262332749 500000000 10771474307309 25000000000000 4377 3353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4377/1024 : ℝ)) 4377 3353 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2673785399/5000000000 : ℝ), (-2063475687/10000000000 : ℝ), (262332749/500000000 : ℝ)] ![(690170003657/1562500000000 : ℝ), (6371611261963/50000000000000 : ℝ), (10771474307309/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2673785399/5000000000 : ℝ)|^4377 ≤ (690170003657/1562500000000 : ℝ)^3353
        have hw : |(2673785399/5000000000 : ℝ)|=(2673785399/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2063475687/10000000000 : ℝ)|^4377 ≤ (6371611261963/50000000000000 : ℝ)^3353
        have hw : |(-2063475687/10000000000 : ℝ)|=(2063475687/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(262332749/500000000 : ℝ)|^4377 ≤ (10771474307309/25000000000000 : ℝ)^3353
        have hw : |(262332749/500000000 : ℝ)|=(262332749/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1417_s7_2 (p : ℝ) (hpa : (547/128 : ℝ) ≤ p) (hpb : p ≤ (4377/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5347570783/10000000000 : ℝ)*x 0 + (5246654991/10000000000 : ℝ)*x 1 + (-515868923/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5347570783/10000000000 : ℝ)^4377 ≤ (4417088007231/10000000000000 : ℝ)^3353 := by
    have hnat : (5347570783 : ℕ)^4377*10000000000000^3353 ≤ 4417088007231^3353*10000000000^4377 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5347570783 10000000000 4417088007231 10000000000000 4377 3353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5246654991/10000000000 : ℝ)^4377 ≤ (43085897347157/100000000000000 : ℝ)^3353 := by
    have hnat : (5246654991 : ℕ)^4377*100000000000000^3353 ≤ 43085897347157^3353*10000000000^4377 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5246654991 10000000000 43085897347157 100000000000000 4377 3353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (515868923/2500000000 : ℝ)^4377 ≤ (6371611282117/50000000000000 : ℝ)^3353 := by
    have hnat : (515868923 : ℕ)^4377*50000000000000^3353 ≤ 6371611282117^3353*2500000000^4377 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      515868923 2500000000 6371611282117 50000000000000 4377 3353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4377/1024 : ℝ)) 4377 3353 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5347570783/10000000000 : ℝ), (5246654991/10000000000 : ℝ), (-515868923/2500000000 : ℝ)] ![(4417088007231/10000000000000 : ℝ), (43085897347157/100000000000000 : ℝ), (6371611282117/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5347570783/10000000000 : ℝ)|^4377 ≤ (4417088007231/10000000000000 : ℝ)^3353
        have hw : |(5347570783/10000000000 : ℝ)|=(5347570783/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5246654991/10000000000 : ℝ)|^4377 ≤ (43085897347157/100000000000000 : ℝ)^3353
        have hw : |(5246654991/10000000000 : ℝ)|=(5246654991/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-515868923/2500000000 : ℝ)|^4377 ≤ (6371611282117/50000000000000 : ℝ)^3353
        have hw : |(-515868923/2500000000 : ℝ)|=(515868923/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1417_s7_3 (p : ℝ) (hpa : (547/128 : ℝ) ≤ p) (hpb : p ≤ (4377/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (107684619/250000000 : ℝ)*x 0 + (1033988689/2500000000 : ℝ)*x 1 + (560652037/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (107684619/250000000 : ℝ)^4377 ≤ (16652260715749/50000000000000 : ℝ)^3353 := by
    have hnat : (107684619 : ℕ)^4377*50000000000000^3353 ≤ 16652260715749^3353*250000000^4377 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      107684619 250000000 16652260715749 50000000000000 4377 3353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1033988689/2500000000 : ℝ)^4377 ≤ (15792421819587/50000000000000 : ℝ)^3353 := by
    have hnat : (1033988689 : ℕ)^4377*50000000000000^3353 ≤ 15792421819587^3353*2500000000^4377 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1033988689 2500000000 15792421819587 50000000000000 4377 3353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (560652037/1250000000 : ℝ)^4377 ≤ (35110634915627/100000000000000 : ℝ)^3353 := by
    have hnat : (560652037 : ℕ)^4377*100000000000000^3353 ≤ 35110634915627^3353*1250000000^4377 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      560652037 1250000000 35110634915627 100000000000000 4377 3353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4377/1024 : ℝ)) 4377 3353 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(107684619/250000000 : ℝ), (1033988689/2500000000 : ℝ), (560652037/1250000000 : ℝ)] ![(16652260715749/50000000000000 : ℝ), (15792421819587/50000000000000 : ℝ), (35110634915627/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(107684619/250000000 : ℝ)|^4377 ≤ (16652260715749/50000000000000 : ℝ)^3353
        have hw : |(107684619/250000000 : ℝ)|=(107684619/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1033988689/2500000000 : ℝ)|^4377 ≤ (15792421819587/50000000000000 : ℝ)^3353
        have hw : |(1033988689/2500000000 : ℝ)|=(1033988689/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(560652037/1250000000 : ℝ)|^4377 ≤ (35110634915627/100000000000000 : ℝ)^3353
        have hw : |(560652037/1250000000 : ℝ)|=(560652037/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1417_s7_4 (p : ℝ) (hpa : (547/128 : ℝ) ≤ p) (hpb : p ≤ (4377/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1980921743/10000000000 : ℝ)*x 0 + (2623619541/5000000000 : ℝ)*x 1 + (5408226427/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1980921743/10000000000 : ℝ)^4377 ≤ (12081807123439/100000000000000 : ℝ)^3353 := by
    have hnat : (1980921743 : ℕ)^4377*100000000000000^3353 ≤ 12081807123439^3353*10000000000^4377 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1980921743 10000000000 12081807123439 100000000000000 4377 3353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2623619541/5000000000 : ℝ)^4377 ≤ (1723686356851/4000000000000 : ℝ)^3353 := by
    have hnat : (2623619541 : ℕ)^4377*4000000000000^3353 ≤ 1723686356851^3353*5000000000^4377 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2623619541 5000000000 1723686356851 4000000000000 4377 3353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5408226427/10000000000 : ℝ)^4377 ≤ (1793041357777/4000000000000 : ℝ)^3353 := by
    have hnat : (5408226427 : ℕ)^4377*4000000000000^3353 ≤ 1793041357777^3353*10000000000^4377 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5408226427 10000000000 1793041357777 4000000000000 4377 3353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4377/1024 : ℝ)) 4377 3353 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1980921743/10000000000 : ℝ), (2623619541/5000000000 : ℝ), (5408226427/10000000000 : ℝ)] ![(12081807123439/100000000000000 : ℝ), (1723686356851/4000000000000 : ℝ), (1793041357777/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1980921743/10000000000 : ℝ)|^4377 ≤ (12081807123439/100000000000000 : ℝ)^3353
        have hw : |(-1980921743/10000000000 : ℝ)|=(1980921743/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2623619541/5000000000 : ℝ)|^4377 ≤ (1723686356851/4000000000000 : ℝ)^3353
        have hw : |(2623619541/5000000000 : ℝ)|=(2623619541/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5408226427/10000000000 : ℝ)|^4377 ≤ (1793041357777/4000000000000 : ℝ)^3353
        have hw : |(5408226427/10000000000 : ℝ)|=(5408226427/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1417_s7_5 (p : ℝ) (hpa : (547/128 : ℝ) ≤ p) (hpb : p ≤ (4377/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5305463993/10000000000 : ℝ)*x 0 + (-950952087/5000000000 : ℝ)*x 1 + (2704113229/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305463993/10000000000 : ℝ)^4377 ≤ (43717407324749/100000000000000 : ℝ)^3353 := by
    have hnat : (5305463993 : ℕ)^4377*100000000000000^3353 ≤ 43717407324749^3353*10000000000^4377 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305463993 10000000000 43717407324749 100000000000000 4377 3353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (950952087/5000000000 : ℝ)^4377 ≤ (5728279189519/50000000000000 : ℝ)^3353 := by
    have hnat : (950952087 : ℕ)^4377*50000000000000^3353 ≤ 5728279189519^3353*5000000000^4377 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      950952087 5000000000 5728279189519 50000000000000 4377 3353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2704113229/5000000000 : ℝ)^4377 ≤ (22413017139919/50000000000000 : ℝ)^3353 := by
    have hnat : (2704113229 : ℕ)^4377*50000000000000^3353 ≤ 22413017139919^3353*5000000000^4377 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2704113229 5000000000 22413017139919 50000000000000 4377 3353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4377/1024 : ℝ)) 4377 3353 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305463993/10000000000 : ℝ), (-950952087/5000000000 : ℝ), (2704113229/5000000000 : ℝ)] ![(43717407324749/100000000000000 : ℝ), (5728279189519/50000000000000 : ℝ), (22413017139919/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305463993/10000000000 : ℝ)|^4377 ≤ (43717407324749/100000000000000 : ℝ)^3353
        have hw : |(5305463993/10000000000 : ℝ)|=(5305463993/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-950952087/5000000000 : ℝ)|^4377 ≤ (5728279189519/50000000000000 : ℝ)^3353
        have hw : |(-950952087/5000000000 : ℝ)|=(950952087/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2704113229/5000000000 : ℝ)|^4377 ≤ (22413017139919/50000000000000 : ℝ)^3353
        have hw : |(2704113229/5000000000 : ℝ)|=(2704113229/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1417_s7_6 (p : ℝ) (hpa : (547/128 : ℝ) ≤ p) (hpb : p ≤ (4377/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5305464089/10000000000 : ℝ)*x 0 + (270411323/500000000 : ℝ)*x 1 + (-1901904039/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305464089/10000000000 : ℝ)^4377 ≤ (2185870417869/5000000000000 : ℝ)^3353 := by
    have hnat : (5305464089 : ℕ)^4377*5000000000000^3353 ≤ 2185870417869^3353*10000000000^4377 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305464089 10000000000 2185870417869 5000000000000 4377 3353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (270411323/500000000 : ℝ)^4377 ≤ (44826034301477/100000000000000 : ℝ)^3353 := by
    have hnat : (270411323 : ℕ)^4377*100000000000000^3353 ≤ 44826034301477^3353*500000000^4377 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      270411323 500000000 44826034301477 100000000000000 4377 3353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1901904039/10000000000 : ℝ)^4377 ≤ (2864139329371/25000000000000 : ℝ)^3353 := by
    have hnat : (1901904039 : ℕ)^4377*25000000000000^3353 ≤ 2864139329371^3353*10000000000^4377 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1901904039 10000000000 2864139329371 25000000000000 4377 3353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4377/1024 : ℝ)) 4377 3353 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305464089/10000000000 : ℝ), (270411323/500000000 : ℝ), (-1901904039/10000000000 : ℝ)] ![(2185870417869/5000000000000 : ℝ), (44826034301477/100000000000000 : ℝ), (2864139329371/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305464089/10000000000 : ℝ)|^4377 ≤ (2185870417869/5000000000000 : ℝ)^3353
        have hw : |(5305464089/10000000000 : ℝ)|=(5305464089/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(270411323/500000000 : ℝ)|^4377 ≤ (44826034301477/100000000000000 : ℝ)^3353
        have hw : |(270411323/500000000 : ℝ)|=(270411323/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1901904039/10000000000 : ℝ)|^4377 ≤ (2864139329371/25000000000000 : ℝ)^3353
        have hw : |(-1901904039/10000000000 : ℝ)|=(1901904039/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1417_s7_7 (p : ℝ) (hpa : (547/128 : ℝ) ≤ p) (hpb : p ≤ (4377/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4307409397/10000000000 : ℝ)*x 0 + (448395833/1000000000 : ℝ)*x 1 + (4137219197/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4307409397/10000000000 : ℝ)^4377 ≤ (33304770099971/100000000000000 : ℝ)^3353 := by
    have hnat : (4307409397 : ℕ)^4377*100000000000000^3353 ≤ 33304770099971^3353*10000000000^4377 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4307409397 10000000000 33304770099971 100000000000000 4377 3353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (448395833/1000000000 : ℝ)^4377 ≤ (35097780611031/100000000000000 : ℝ)^3353 := by
    have hnat : (448395833 : ℕ)^4377*100000000000000^3353 ≤ 35097780611031^3353*1000000000^4377 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      448395833 1000000000 35097780611031 100000000000000 4377 3353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4137219197/10000000000 : ℝ)^4377 ≤ (7899362318973/25000000000000 : ℝ)^3353 := by
    have hnat : (4137219197 : ℕ)^4377*25000000000000^3353 ≤ 7899362318973^3353*10000000000^4377 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4137219197 10000000000 7899362318973 25000000000000 4377 3353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4377/1024 : ℝ)) 4377 3353 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4307409397/10000000000 : ℝ), (448395833/1000000000 : ℝ), (4137219197/10000000000 : ℝ)] ![(33304770099971/100000000000000 : ℝ), (35097780611031/100000000000000 : ℝ), (7899362318973/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4307409397/10000000000 : ℝ)|^4377 ≤ (33304770099971/100000000000000 : ℝ)^3353
        have hw : |(4307409397/10000000000 : ℝ)|=(4307409397/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(448395833/1000000000 : ℝ)|^4377 ≤ (35097780611031/100000000000000 : ℝ)^3353
        have hw : |(448395833/1000000000 : ℝ)|=(448395833/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4137219197/10000000000 : ℝ)|^4377 ≤ (7899362318973/25000000000000 : ℝ)^3353
        have hw : |(4137219197/10000000000 : ℝ)|=(4137219197/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1417_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (547/128 : ℝ) ≤ p) (hpb : p ≤ (4377/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (19711417/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14751/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2263/20000 : ℝ)*pair X i i ≤ pair X i h) :
    (2829/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (59/400 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14751/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2263/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14751/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2263/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14751/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2263/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14751/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2263/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14751/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2263/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14751/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2263/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hlower 2 1 (by decide)
  have fm0 := f.main 0
  simp only [pair0,pair1,pair2,Pi.add_apply] at fm0
  have fx01 := abs_le.mp (f.maximal 0 1)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx01
  have fx02 := abs_le.mp (f.maximal 0 2)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx02
  have fm1 := f.main 1
  simp only [pair0,pair1,pair2,Pi.add_apply] at fm1
  have fx10 := abs_le.mp (f.maximal 1 0)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx10
  have fx12 := abs_le.mp (f.maximal 1 2)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx12
  have fm2 := f.main 2
  simp only [pair0,pair1,pair2,Pi.add_apply] at fm2
  have fx20 := abs_le.mp (f.maximal 2 0)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx20
  have fx21 := abs_le.mp (f.maximal 2 1)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx21
  have base19 : ((1 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 2).2]
  have base23 : ((1 : ℝ)*X 2 1+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 1).2]
  have base65 : ((1 : ℝ)*X 0 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 0).2]
  have base66 : ((-1 : ℝ)*X 0 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 0).1]
  have base67 : ((1 : ℝ)*X 0 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 1).2]
  have base68 : ((-1 : ℝ)*X 0 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 1).1]
  have base69 : ((1 : ℝ)*X 0 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 2).2]
  have base70 : ((-1 : ℝ)*X 0 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 2).1]
  have base71 : ((1 : ℝ)*X 1 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 0).2]
  have base72 : ((-1 : ℝ)*X 1 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 0).1]
  have base73 : ((1 : ℝ)*X 1 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 1).2]
  have base74 : ((-1 : ℝ)*X 1 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 1).1]
  have base75 : ((1 : ℝ)*X 1 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 2).2]
  have base76 : ((-1 : ℝ)*X 1 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 2).1]
  have base77 : ((1 : ℝ)*X 2 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 0).2]
  have base78 : ((-1 : ℝ)*X 2 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 0).1]
  have base79 : ((1 : ℝ)*X 2 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 1).2]
  have base80 : ((-1 : ℝ)*X 2 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 1).1]
  have base81 : ((1 : ℝ)*X 2 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 2).2]
  have base82 : ((-1 : ℝ)*X 2 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 2).1]
  have base83 : ((1 : ℝ)*N 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 0).2]
  have base84 : ((-1 : ℝ)*N 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 0).1]
  have base85 : ((1 : ℝ)*N 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 1).2]
  have base86 : ((-1 : ℝ)*N 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 1).1]
  have base87 : ((1 : ℝ)*N 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 2).2]
  have base88 : ((-1 : ℝ)*N 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 2).1]
  have base89 : ((1 : ℝ)*P 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 0).2]
  have base90 : ((-1 : ℝ)*P 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 0).1]
  have base91 : ((1 : ℝ)*P 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 1).2]
  have base92 : ((-1 : ℝ)*P 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 1).1]
  have base93 : ((1 : ℝ)*P 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 2).2]
  have base94 : ((-1 : ℝ)*P 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 2).1]
  have base95 : ((1 : ℝ)*T) ≤ (3 : ℝ) := by
    linarith only [bounds.2.2.2.2]
  have base96 : ((-1 : ℝ)*T) ≤ (3 : ℝ) := by
    linarith only [bounds.2.2.2.1]
  have hpowlo : (2263/20000 : ℝ) ^ (547/128 : ℝ) ≤ (9033413731813439/100000000000000000000 : ℝ) := by
    have hpowers : (2263/20000 : ℝ)^547 ≤ (9033413731813439/100000000000000000000 : ℝ)^128 := by
      have hnat : (2263 : ℕ)^547*100000000000000000000^128 ≤ 9033413731813439^128*20000^547 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2263 20000 9033413731813439 100000000000000000000 547 128 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2263/20000 : ℝ)) (X := (9033413731813439/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 547 128 (by norm_num) hpowers
    exact h
  have hpowhi : (14751/100000 : ℝ) ^ (547/128 : ℝ) ≤ (28055012777145349/100000000000000000000 : ℝ) := by
    have hpowers : (14751/100000 : ℝ)^547 ≤ (28055012777145349/100000000000000000000 : ℝ)^128 := by
      have hnat : (14751 : ℕ)^547*100000000000000000000^128 ≤ 28055012777145349^128*100000^547 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14751 100000 28055012777145349 100000000000000000000 547 128 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14751/100000 : ℝ)) (X := (28055012777145349/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 547 128 (by norm_num) hpowers
    exact h
  have hcorner00 : (50009033413731813439/50000000000000000000 : ℝ) ≤ (1000042274111769/1000000000000000 : ℝ) ^ (547/128 : ℝ) := by
    have hpowers : (50009033413731813439/50000000000000000000 : ℝ)^128 ≤ (1000042274111769/1000000000000000 : ℝ)^547 := by
      have hnat : (50009033413731813439 : ℕ)^128*1000000000000000^547 ≤ 1000042274111769^547*50000000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50009033413731813439 50000000000000000000 1000042274111769 1000000000000000 128 547 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000042274111769/1000000000000000 : ℝ)) (X := (50009033413731813439/50000000000000000000 : ℝ)) (by norm_num) 547 128 (by norm_num) hpowers
    exact h
  have hcorner10 : (25009272106627239697/25000000000000000000 : ℝ) ≤ (10000867759486883/10000000000000000 : ℝ) ^ (547/128 : ℝ) := by
    have hpowers : (25009272106627239697/25000000000000000000 : ℝ)^128 ≤ (10000867759486883/10000000000000000 : ℝ)^547 := by
      have hnat : (25009272106627239697 : ℕ)^128*10000000000000000^547 ≤ 10000867759486883^547*25000000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25009272106627239697 25000000000000000000 10000867759486883 10000000000000000 128 547 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000867759486883/10000000000000000 : ℝ)) (X := (25009272106627239697/25000000000000000000 : ℝ)) (by norm_num) 547 128 (by norm_num) hpowers
    exact h
  have hcorner11 : (50028055012777145349/50000000000000000000 : ℝ) ≤ (2500328194464019/2500000000000000 : ℝ) ^ (547/128 : ℝ) := by
    have hpowers : (50028055012777145349/50000000000000000000 : ℝ)^128 ≤ (2500328194464019/2500000000000000 : ℝ)^547 := by
      have hnat : (50028055012777145349 : ℕ)^128*2500000000000000^547 ≤ 2500328194464019^547*50000000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50028055012777145349 50000000000000000000 2500328194464019 2500000000000000 128 547 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500328194464019/2500000000000000 : ℝ)) (X := (50028055012777145349/50000000000000000000 : ℝ)) (by norm_num) 547 128 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(9033413731813439/100000000000000000000 : ℝ) ≤ ((137405527091142181/137440000000000000 : ℝ)+2*(445018369193/343600000000000 : ℝ)*(2263/20000 : ℝ))^(547/128 : ℝ) := by
    rw [show (137405527091142181/137440000000000000 : ℝ)+2*(445018369193/343600000000000 : ℝ)*(2263/20000 : ℝ)=(1000042274111769/1000000000000000 : ℝ) by norm_num, show 1+2*(9033413731813439/100000000000000000000 : ℝ)=(50009033413731813439/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(28055012777145349/100000000000000000000 : ℝ)+(9033413731813439/100000000000000000000 : ℝ) ≤ ((137405527091142181/137440000000000000 : ℝ)+(445018369193/343600000000000 : ℝ)*((14751/100000 : ℝ)+(2263/20000 : ℝ)))^(547/128 : ℝ) := by
    rw [show (137405527091142181/137440000000000000 : ℝ)+(445018369193/343600000000000 : ℝ)*((14751/100000 : ℝ)+(2263/20000 : ℝ))=(10000867759486883/10000000000000000 : ℝ) by norm_num, show 1+(28055012777145349/100000000000000000000 : ℝ)+(9033413731813439/100000000000000000000 : ℝ)=(25009272106627239697/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(28055012777145349/100000000000000000000 : ℝ) ≤ ((137405527091142181/137440000000000000 : ℝ)+2*(445018369193/343600000000000 : ℝ)*(14751/100000 : ℝ))^(547/128 : ℝ) := by
    rw [show (137405527091142181/137440000000000000 : ℝ)+2*(445018369193/343600000000000 : ℝ)*(14751/100000 : ℝ)=(2500328194464019/2500000000000000 : ℝ) by norm_num, show 1+2*(28055012777145349/100000000000000000000 : ℝ)=(50028055012777145349/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (137405527091142181/137440000000000000 : ℝ)*(X 1 0+X 2 0)+(445018369193/343600000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (547/128 : ℝ)) (lo := (2263/20000 : ℝ)) (hi := (14751/100000 : ℝ)) (c := (137405527091142181/137440000000000000 : ℝ)) (alpha := (445018369193/343600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (137405527091142181/137440000000000000 : ℝ)*(X 0 1+X 2 1)+(445018369193/343600000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (547/128 : ℝ)) (lo := (2263/20000 : ℝ)) (hi := (14751/100000 : ℝ)) (c := (137405527091142181/137440000000000000 : ℝ)) (alpha := (445018369193/343600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (137405527091142181/137440000000000000 : ℝ)*(X 0 2+X 1 2)+(445018369193/343600000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (547/128 : ℝ)) (lo := (2263/20000 : ℝ)) (hi := (14751/100000 : ℝ)) (c := (137405527091142181/137440000000000000 : ℝ)) (alpha := (445018369193/343600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1980910299/10000000000 : ℝ)*X 0 0+(5408813579/10000000000 : ℝ)*X 0 1+(1049330993/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1417_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2673785399/5000000000 : ℝ)*X 1 0+(-2063475687/10000000000 : ℝ)*X 1 1+(262332749/500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1417_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5347570783/10000000000 : ℝ)*X 2 0+(5246654991/10000000000 : ℝ)*X 2 1+(-515868923/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1417_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((107684619/250000000 : ℝ)*X 0 0+(1033988689/2500000000 : ℝ)*X 0 1+(560652037/1250000000 : ℝ)*X 0 2+(107684619/250000000 : ℝ)*X 1 0+(1033988689/2500000000 : ℝ)*X 1 1+(560652037/1250000000 : ℝ)*X 1 2+(107684619/250000000 : ℝ)*X 2 0+(1033988689/2500000000 : ℝ)*X 2 1+(560652037/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1417_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1980921743/10000000000 : ℝ)*X 0 0+(2623619541/5000000000 : ℝ)*X 0 1+(5408226427/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1417_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5305463993/10000000000 : ℝ)*X 1 0+(-950952087/5000000000 : ℝ)*X 1 1+(2704113229/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1417_s7_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5305464089/10000000000 : ℝ)*X 2 0+(270411323/500000000 : ℝ)*X 2 1+(-1901904039/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1417_s7_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4307409397/10000000000 : ℝ)*X 0 0+(448395833/1000000000 : ℝ)*X 0 1+(4137219197/10000000000 : ℝ)*X 0 2+(4307409397/10000000000 : ℝ)*X 1 0+(448395833/1000000000 : ℝ)*X 1 1+(4137219197/10000000000 : ℝ)*X 1 2+(4307409397/10000000000 : ℝ)*X 2 0+(448395833/1000000000 : ℝ)*X 2 1+(4137219197/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1417_s7_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (11788320306761145746855163/3436000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (126402423/20000000000000 : ℝ)*(base19) + (286692057/50000000000000 : ℝ)*(base23) + (4420299/20000000000000 : ℝ)*(lower2) + (12021891/12500000000000 : ℝ)*(upper3) + (5656789/10000000000000 : ℝ)*(upper5) + (2257506428613753/50000000000000 : ℝ)*(major0) + (2257506428613753/50000000000000 : ℝ)*(major1) + (2257506428613753/50000000000000 : ℝ)*(major2) + (6166815858656447/100000000000000 : ℝ)*(sp0) + (154170711003339/2500000000000 : ℝ)*(sp1) + (3083414249380781/50000000000000 : ℝ)*(sp2) + (286318981396827/10000000000000 : ℝ)*(sp3) + (13213489229/100000000000000 : ℝ)*(sp4) + (839247521/12500000000000 : ℝ)*(sp7) + (1431598263974219/50000000000000 : ℝ)*(f.failure) + (1541707268036419/25000000000000 : ℝ)*(f.sum) + (35565269986689/8590000000000000000000000000 : ℝ)*base65 + (10519337965874893/6872000000000000000000000000000 : ℝ)*base67 + (120084829177258893/6872000000000000000000000000000 : ℝ)*base69 + (119714375998874893/6872000000000000000000000000000 : ℝ)*base71 + (31061224554271/8590000000000000000000000000 : ℝ)*base74 + (514333619994893/6872000000000000000000000000000 : ℝ)*base75 + (23789075194122893/6872000000000000000000000000000 : ℝ)*base77 + (14904262545802893/6872000000000000000000000000000 : ℝ)*base79 + (56027405769249/8590000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (4541677/625000000000000000000 : ℝ)*base90 + (4541677/625000000000000000000 : ℝ)*base92 + (4541677/625000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (60220995597278267007237/17180000000000000000000000000 : ℝ) := by norm_num
    linear_combination (805342847/100000000000000 : ℝ)*(base19) + (1024530093/100000000000000 : ℝ)*(base23) + (264403191/100000000000000 : ℝ)*(lower1) + (62324069/50000000000000 : ℝ)*(upper3) + (4825543/25000000000000 : ℝ)*(lower4) + (26295481/50000000000000 : ℝ)*(upper5) + (4547828312982401/100000000000000 : ℝ)*(major0) + (4547828312982401/100000000000000 : ℝ)*(major1) + (4547828312982401/100000000000000 : ℝ)*(major2) + (2217877087/25000000000000 : ℝ)*(sp2) + (3105825025866459/50000000000000 : ℝ)*(sp4) + (6211649246390071/100000000000000 : ℝ)*(sp5) + (6211640155694477/100000000000000 : ℝ)*(sp6) + (288400645738863/10000000000000 : ℝ)*(sp7) + (288400645738863/10000000000000 : ℝ)*(f.failure) + (3105825025866459/50000000000000 : ℝ)*(f.sum) + (105844136646087/17180000000000000000000000000 : ℝ)*base66 + (439550665764230219/13744000000000000000000000000000 : ℝ)*base68 + (337298824710219/13744000000000000000000000000000 : ℝ)*base70 + (1596179465690358219/13744000000000000000000000000000 : ℝ)*base72 + (6557678387887/17180000000000000000000000000 : ℝ)*base74 + (2216607360007481781/13744000000000000000000000000000 : ℝ)*base75 + (155337760008745781/13744000000000000000000000000000 : ℝ)*base77 + (72219200070841781/13744000000000000000000000000000 : ℝ)*base79 + (63722911098987/17180000000000000000000000000 : ℝ)*base82 + (448871/125000000000000000000 : ℝ)*base89 + (448871/125000000000000000000 : ℝ)*base91 + (448871/125000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1417_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (547/128 : ℝ) ≤ p) (hpb : p ≤ (4377/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (19711417/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14751/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2263/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2829/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (59/400 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1417_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1417_box_0 (p : ℝ) (hpa : (547/128 : ℝ) ≤ p) (hpb : p ≤ (4377/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1819379989/10000000000 : ℝ)*x 0 + (5386768849/10000000000 : ℝ)*x 1 + (42084131/78125000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1819379989/10000000000 : ℝ)^4377 ≤ (10811983958873/100000000000000 : ℝ)^3353 := by
    have hnat : (1819379989 : ℕ)^4377*100000000000000^3353 ≤ 10811983958873^3353*10000000000^4377 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1819379989 10000000000 10811983958873 100000000000000 4377 3353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5386768849/10000000000 : ℝ)^4377 ≤ (22297004225427/50000000000000 : ℝ)^3353 := by
    have hnat : (5386768849 : ℕ)^4377*50000000000000^3353 ≤ 22297004225427^3353*10000000000^4377 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5386768849 10000000000 22297004225427 50000000000000 4377 3353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (42084131/78125000 : ℝ)^4377 ≤ (8918801515103/20000000000000 : ℝ)^3353 := by
    have hnat : (42084131 : ℕ)^4377*20000000000000^3353 ≤ 8918801515103^3353*78125000^4377 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      42084131 78125000 8918801515103 20000000000000 4377 3353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4377/1024 : ℝ)) 4377 3353 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1819379989/10000000000 : ℝ), (5386768849/10000000000 : ℝ), (42084131/78125000 : ℝ)] ![(10811983958873/100000000000000 : ℝ), (22297004225427/50000000000000 : ℝ), (8918801515103/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1819379989/10000000000 : ℝ)|^4377 ≤ (10811983958873/100000000000000 : ℝ)^3353
        have hw : |(-1819379989/10000000000 : ℝ)|=(1819379989/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5386768849/10000000000 : ℝ)|^4377 ≤ (22297004225427/50000000000000 : ℝ)^3353
        have hw : |(5386768849/10000000000 : ℝ)|=(5386768849/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(42084131/78125000 : ℝ)|^4377 ≤ (8918801515103/20000000000000 : ℝ)^3353
        have hw : |(42084131/78125000 : ℝ)|=(42084131/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1417_box_1 (p : ℝ) (hpa : (547/128 : ℝ) ≤ p) (hpb : p ≤ (4377/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (211438991/400000000 : ℝ)*x 0 + (-1957807303/10000000000 : ℝ)*x 1 + (5386768741/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (211438991/400000000 : ℝ)^4377 ≤ (21753943888199/50000000000000 : ℝ)^3353 := by
    have hnat : (211438991 : ℕ)^4377*50000000000000^3353 ≤ 21753943888199^3353*400000000^4377 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      211438991 400000000 21753943888199 50000000000000 4377 3353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1957807303/10000000000 : ℝ)^4377 ≤ (11898104931063/100000000000000 : ℝ)^3353 := by
    have hnat : (1957807303 : ℕ)^4377*100000000000000^3353 ≤ 11898104931063^3353*10000000000^4377 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1957807303 10000000000 11898104931063 100000000000000 4377 3353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5386768741/10000000000 : ℝ)^4377 ≤ (8918801456747/20000000000000 : ℝ)^3353 := by
    have hnat : (5386768741 : ℕ)^4377*20000000000000^3353 ≤ 8918801456747^3353*10000000000^4377 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5386768741 10000000000 8918801456747 20000000000000 4377 3353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4377/1024 : ℝ)) 4377 3353 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(211438991/400000000 : ℝ), (-1957807303/10000000000 : ℝ), (5386768741/10000000000 : ℝ)] ![(21753943888199/50000000000000 : ℝ), (11898104931063/100000000000000 : ℝ), (8918801456747/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(211438991/400000000 : ℝ)|^4377 ≤ (21753943888199/50000000000000 : ℝ)^3353
        have hw : |(211438991/400000000 : ℝ)|=(211438991/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1957807303/10000000000 : ℝ)|^4377 ≤ (11898104931063/100000000000000 : ℝ)^3353
        have hw : |(-1957807303/10000000000 : ℝ)|=(1957807303/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5386768741/10000000000 : ℝ)|^4377 ≤ (8918801456747/20000000000000 : ℝ)^3353
        have hw : |(5386768741/10000000000 : ℝ)|=(5386768741/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1417_box_2 (p : ℝ) (hpa : (547/128 : ℝ) ≤ p) (hpb : p ≤ (4377/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5285974673/10000000000 : ℝ)*x 0 + (2693384371/5000000000 : ℝ)*x 1 + (-24472593/125000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5285974673/10000000000 : ℝ)^4377 ≤ (2175394334023/5000000000000 : ℝ)^3353 := by
    have hnat : (5285974673 : ℕ)^4377*5000000000000^3353 ≤ 2175394334023^3353*10000000000^4377 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5285974673 10000000000 2175394334023 5000000000000 4377 3353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2693384371/5000000000 : ℝ)^4377 ≤ (22297003647271/50000000000000 : ℝ)^3353 := by
    have hnat : (2693384371 : ℕ)^4377*50000000000000^3353 ≤ 22297003647271^3353*5000000000^4377 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2693384371 5000000000 22297003647271 50000000000000 4377 3353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (24472593/125000000 : ℝ)^4377 ≤ (11898106017917/100000000000000 : ℝ)^3353 := by
    have hnat : (24472593 : ℕ)^4377*100000000000000^3353 ≤ 11898106017917^3353*125000000^4377 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      24472593 125000000 11898106017917 100000000000000 4377 3353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4377/1024 : ℝ)) 4377 3353 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5285974673/10000000000 : ℝ), (2693384371/5000000000 : ℝ), (-24472593/125000000 : ℝ)] ![(2175394334023/5000000000000 : ℝ), (22297003647271/50000000000000 : ℝ), (11898106017917/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5285974673/10000000000 : ℝ)|^4377 ≤ (2175394334023/5000000000000 : ℝ)^3353
        have hw : |(5285974673/10000000000 : ℝ)|=(5285974673/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2693384371/5000000000 : ℝ)|^4377 ≤ (22297003647271/50000000000000 : ℝ)^3353
        have hw : |(2693384371/5000000000 : ℝ)|=(2693384371/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-24472593/125000000 : ℝ)|^4377 ≤ (11898106017917/100000000000000 : ℝ)^3353
        have hw : |(-24472593/125000000 : ℝ)|=(24472593/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1417_box_3 (p : ℝ) (hpa : (547/128 : ℝ) ≤ p) (hpb : p ≤ (4377/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1113480717/2500000000 : ℝ)*x 0 + (1059461943/2500000000 : ℝ)*x 1 + (2118923933/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1113480717/2500000000 : ℝ)^4377 ≤ (34791196062961/100000000000000 : ℝ)^3353 := by
    have hnat : (1113480717 : ℕ)^4377*100000000000000^3353 ≤ 34791196062961^3353*2500000000^4377 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1113480717 2500000000 34791196062961 100000000000000 4377 3353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1059461943/2500000000 : ℝ)^4377 ≤ (32604401489069/100000000000000 : ℝ)^3353 := by
    have hnat : (1059461943 : ℕ)^4377*100000000000000^3353 ≤ 32604401489069^3353*2500000000^4377 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1059461943 2500000000 32604401489069 100000000000000 4377 3353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2118923933/5000000000 : ℝ)^4377 ≤ (32604402433133/100000000000000 : ℝ)^3353 := by
    have hnat : (2118923933 : ℕ)^4377*100000000000000^3353 ≤ 32604402433133^3353*5000000000^4377 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2118923933 5000000000 32604402433133 100000000000000 4377 3353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4377/1024 : ℝ)) 4377 3353 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1113480717/2500000000 : ℝ), (1059461943/2500000000 : ℝ), (2118923933/5000000000 : ℝ)] ![(34791196062961/100000000000000 : ℝ), (32604401489069/100000000000000 : ℝ), (32604402433133/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1113480717/2500000000 : ℝ)|^4377 ≤ (34791196062961/100000000000000 : ℝ)^3353
        have hw : |(1113480717/2500000000 : ℝ)|=(1113480717/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1059461943/2500000000 : ℝ)|^4377 ≤ (32604401489069/100000000000000 : ℝ)^3353
        have hw : |(1059461943/2500000000 : ℝ)|=(1059461943/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2118923933/5000000000 : ℝ)|^4377 ≤ (32604402433133/100000000000000 : ℝ)^3353
        have hw : |(2118923933/5000000000 : ℝ)|=(2118923933/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1417_box_4 (p : ℝ) (hpa : (547/128 : ℝ) ≤ p) (hpb : p ≤ (4377/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1072588959/5000000000 : ℝ)*x 0 + (5266344371/10000000000 : ℝ)*x 1 + (5266344407/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1072588959/5000000000 : ℝ)^4377 ≤ (13405822080253/100000000000000 : ℝ)^3353 := by
    have hnat : (1072588959 : ℕ)^4377*100000000000000^3353 ≤ 13405822080253^3353*5000000000^4377 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1072588959 5000000000 13405822080253 100000000000000 4377 3353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5266344371/10000000000 : ℝ)^4377 ≤ (21648544378937/50000000000000 : ℝ)^3353 := by
    have hnat : (5266344371 : ℕ)^4377*50000000000000^3353 ≤ 21648544378937^3353*10000000000^4377 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266344371 10000000000 21648544378937 50000000000000 4377 3353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5266344407/10000000000 : ℝ)^4377 ≤ (10824272286059/25000000000000 : ℝ)^3353 := by
    have hnat : (5266344407 : ℕ)^4377*25000000000000^3353 ≤ 10824272286059^3353*10000000000^4377 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266344407 10000000000 10824272286059 25000000000000 4377 3353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4377/1024 : ℝ)) 4377 3353 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1072588959/5000000000 : ℝ), (5266344371/10000000000 : ℝ), (5266344407/10000000000 : ℝ)] ![(13405822080253/100000000000000 : ℝ), (21648544378937/50000000000000 : ℝ), (10824272286059/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1072588959/5000000000 : ℝ)|^4377 ≤ (13405822080253/100000000000000 : ℝ)^3353
        have hw : |(-1072588959/5000000000 : ℝ)|=(1072588959/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5266344371/10000000000 : ℝ)|^4377 ≤ (21648544378937/50000000000000 : ℝ)^3353
        have hw : |(5266344371/10000000000 : ℝ)|=(5266344371/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5266344407/10000000000 : ℝ)|^4377 ≤ (10824272286059/25000000000000 : ℝ)^3353
        have hw : |(5266344407/10000000000 : ℝ)|=(5266344407/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1417_box_5 (p : ℝ) (hpa : (547/128 : ℝ) ≤ p) (hpb : p ≤ (4377/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5370294649/10000000000 : ℝ)*x 0 + (-2006623653/10000000000 : ℝ)*x 1 + (2633172533/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5370294649/10000000000 : ℝ)^4377 ≤ (22208030351787/50000000000000 : ℝ)^3353 := by
    have hnat : (5370294649 : ℕ)^4377*50000000000000^3353 ≤ 22208030351787^3353*10000000000^4377 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5370294649 10000000000 22208030351787 50000000000000 4377 3353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2006623653/10000000000 : ℝ)^4377 ≤ (12286843062013/100000000000000 : ℝ)^3353 := by
    have hnat : (2006623653 : ℕ)^4377*100000000000000^3353 ≤ 12286843062013^3353*10000000000^4377 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2006623653 10000000000 12286843062013 100000000000000 4377 3353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2633172533/5000000000 : ℝ)^4377 ≤ (2706068513551/6250000000000 : ℝ)^3353 := by
    have hnat : (2633172533 : ℕ)^4377*6250000000000^3353 ≤ 2706068513551^3353*5000000000^4377 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633172533 5000000000 2706068513551 6250000000000 4377 3353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4377/1024 : ℝ)) 4377 3353 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5370294649/10000000000 : ℝ), (-2006623653/10000000000 : ℝ), (2633172533/5000000000 : ℝ)] ![(22208030351787/50000000000000 : ℝ), (12286843062013/100000000000000 : ℝ), (2706068513551/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5370294649/10000000000 : ℝ)|^4377 ≤ (22208030351787/50000000000000 : ℝ)^3353
        have hw : |(5370294649/10000000000 : ℝ)|=(5370294649/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2006623653/10000000000 : ℝ)|^4377 ≤ (12286843062013/100000000000000 : ℝ)^3353
        have hw : |(-2006623653/10000000000 : ℝ)|=(2006623653/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2633172533/5000000000 : ℝ)|^4377 ≤ (2706068513551/6250000000000 : ℝ)^3353
        have hw : |(2633172533/5000000000 : ℝ)|=(2633172533/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1417_box_6 (p : ℝ) (hpa : (547/128 : ℝ) ≤ p) (hpb : p ≤ (4377/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1074058983/2000000000 : ℝ)*x 0 + (5266344391/10000000000 : ℝ)*x 1 + (-10033121/50000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1074058983/2000000000 : ℝ)^4377 ≤ (1388001986733/3125000000000 : ℝ)^3353 := by
    have hnat : (1074058983 : ℕ)^4377*3125000000000^3353 ≤ 1388001986733^3353*2000000000^4377 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1074058983 2000000000 1388001986733 3125000000000 4377 3353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5266344391/10000000000 : ℝ)^4377 ≤ (1082427224313/2500000000000 : ℝ)^3353 := by
    have hnat : (5266344391 : ℕ)^4377*2500000000000^3353 ≤ 1082427224313^3353*10000000000^4377 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266344391 10000000000 1082427224313 2500000000000 4377 3353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (10033121/50000000 : ℝ)^4377 ≤ (12286847434261/100000000000000 : ℝ)^3353 := by
    have hnat : (10033121 : ℕ)^4377*100000000000000^3353 ≤ 12286847434261^3353*50000000^4377 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      10033121 50000000 12286847434261 100000000000000 4377 3353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4377/1024 : ℝ)) 4377 3353 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1074058983/2000000000 : ℝ), (5266344391/10000000000 : ℝ), (-10033121/50000000 : ℝ)] ![(1388001986733/3125000000000 : ℝ), (1082427224313/2500000000000 : ℝ), (12286847434261/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1074058983/2000000000 : ℝ)|^4377 ≤ (1388001986733/3125000000000 : ℝ)^3353
        have hw : |(1074058983/2000000000 : ℝ)|=(1074058983/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5266344391/10000000000 : ℝ)|^4377 ≤ (1082427224313/2500000000000 : ℝ)^3353
        have hw : |(5266344391/10000000000 : ℝ)|=(5266344391/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-10033121/50000000 : ℝ)|^4377 ≤ (12286847434261/100000000000000 : ℝ)^3353
        have hw : |(-10033121/50000000 : ℝ)|=(10033121/50000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1417_box_7 (p : ℝ) (hpa : (547/128 : ℝ) ≤ p) (hpb : p ≤ (4377/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (415981389/1000000000 : ℝ)*x 0 + (4384851277/10000000000 : ℝ)*x 1 + (137026589/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (415981389/1000000000 : ℝ)^4377 ≤ (994465671483/3125000000000 : ℝ)^3353 := by
    have hnat : (415981389 : ℕ)^4377*3125000000000^3353 ≤ 994465671483^3353*1000000000^4377 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      415981389 1000000000 994465671483 3125000000000 4377 3353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4384851277/10000000000 : ℝ)^4377 ≤ (34088551422011/100000000000000 : ℝ)^3353 := by
    have hnat : (4384851277 : ℕ)^4377*100000000000000^3353 ≤ 34088551422011^3353*10000000000^4377 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4384851277 10000000000 34088551422011 100000000000000 4377 3353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (137026589/312500000 : ℝ)^4377 ≤ (8522136767089/25000000000000 : ℝ)^3353 := by
    have hnat : (137026589 : ℕ)^4377*25000000000000^3353 ≤ 8522136767089^3353*312500000^4377 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      137026589 312500000 8522136767089 25000000000000 4377 3353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4377/1024 : ℝ)) 4377 3353 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(415981389/1000000000 : ℝ), (4384851277/10000000000 : ℝ), (137026589/312500000 : ℝ)] ![(994465671483/3125000000000 : ℝ), (34088551422011/100000000000000 : ℝ), (8522136767089/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(415981389/1000000000 : ℝ)|^4377 ≤ (994465671483/3125000000000 : ℝ)^3353
        have hw : |(415981389/1000000000 : ℝ)|=(415981389/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4384851277/10000000000 : ℝ)|^4377 ≤ (34088551422011/100000000000000 : ℝ)^3353
        have hw : |(4384851277/10000000000 : ℝ)|=(4384851277/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(137026589/312500000 : ℝ)|^4377 ≤ (8522136767089/25000000000000 : ℝ)^3353
        have hw : |(137026589/312500000 : ℝ)|=(137026589/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1417_box_8 (p : ℝ) (hpa : (547/128 : ℝ) ≤ p) (hpb : p ≤ (4377/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-259572731/1250000000 : ℝ)*x 0 + (5183101153/10000000000 : ℝ)*x 1 + (2700374897/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (259572731/1250000000 : ℝ)^4377 ≤ (321224546949/2500000000000 : ℝ)^3353 := by
    have hnat : (259572731 : ℕ)^4377*2500000000000^3353 ≤ 321224546949^3353*1250000000^4377 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      259572731 1250000000 321224546949 2500000000000 4377 3353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5183101153/10000000000 : ℝ)^4377 ≤ (21202931307409/50000000000000 : ℝ)^3353 := by
    have hnat : (5183101153 : ℕ)^4377*50000000000000^3353 ≤ 21202931307409^3353*10000000000^4377 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5183101153 10000000000 21202931307409 50000000000000 4377 3353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2700374897/5000000000 : ℝ)^4377 ≤ (44745155500373/100000000000000 : ℝ)^3353 := by
    have hnat : (2700374897 : ℕ)^4377*100000000000000^3353 ≤ 44745155500373^3353*5000000000^4377 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2700374897 5000000000 44745155500373 100000000000000 4377 3353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4377/1024 : ℝ)) 4377 3353 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-259572731/1250000000 : ℝ), (5183101153/10000000000 : ℝ), (2700374897/5000000000 : ℝ)] ![(321224546949/2500000000000 : ℝ), (21202931307409/50000000000000 : ℝ), (44745155500373/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-259572731/1250000000 : ℝ)|^4377 ≤ (321224546949/2500000000000 : ℝ)^3353
        have hw : |(-259572731/1250000000 : ℝ)|=(259572731/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5183101153/10000000000 : ℝ)|^4377 ≤ (21202931307409/50000000000000 : ℝ)^3353
        have hw : |(5183101153/10000000000 : ℝ)|=(5183101153/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2700374897/5000000000 : ℝ)|^4377 ≤ (44745155500373/100000000000000 : ℝ)^3353
        have hw : |(2700374897/5000000000 : ℝ)|=(2700374897/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1417_box_9 (p : ℝ) (hpa : (547/128 : ℝ) ≤ p) (hpb : p ≤ (4377/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5276181259/10000000000 : ℝ)*x 0 + (-1952012671/10000000000 : ℝ)*x 1 + (540074959/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5276181259/10000000000 : ℝ)^4377 ≤ (10850672799951/25000000000000 : ℝ)^3353 := by
    have hnat : (5276181259 : ℕ)^4377*25000000000000^3353 ≤ 10850672799951^3353*10000000000^4377 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5276181259 10000000000 10850672799951 25000000000000 4377 3353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1952012671/10000000000 : ℝ)^4377 ≤ (11852155488747/100000000000000 : ℝ)^3353 := by
    have hnat : (1952012671 : ℕ)^4377*100000000000000^3353 ≤ 11852155488747^3353*10000000000^4377 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1952012671 10000000000 11852155488747 100000000000000 4377 3353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (540074959/1000000000 : ℝ)^4377 ≤ (4474515329407/10000000000000 : ℝ)^3353 := by
    have hnat : (540074959 : ℕ)^4377*10000000000000^3353 ≤ 4474515329407^3353*1000000000^4377 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      540074959 1000000000 4474515329407 10000000000000 4377 3353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4377/1024 : ℝ)) 4377 3353 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5276181259/10000000000 : ℝ), (-1952012671/10000000000 : ℝ), (540074959/1000000000 : ℝ)] ![(10850672799951/25000000000000 : ℝ), (11852155488747/100000000000000 : ℝ), (4474515329407/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5276181259/10000000000 : ℝ)|^4377 ≤ (10850672799951/25000000000000 : ℝ)^3353
        have hw : |(5276181259/10000000000 : ℝ)|=(5276181259/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1952012671/10000000000 : ℝ)|^4377 ≤ (11852155488747/100000000000000 : ℝ)^3353
        have hw : |(-1952012671/10000000000 : ℝ)|=(1952012671/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(540074959/1000000000 : ℝ)|^4377 ≤ (4474515329407/10000000000000 : ℝ)^3353
        have hw : |(540074959/1000000000 : ℝ)|=(540074959/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1417_box_10 (p : ℝ) (hpa : (547/128 : ℝ) ≤ p) (hpb : p ≤ (4377/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1055236183/2000000000 : ℝ)*x 0 + (5400749949/10000000000 : ℝ)*x 1 + (-244001581/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1055236183/2000000000 : ℝ)^4377 ≤ (43402687505791/100000000000000 : ℝ)^3353 := by
    have hnat : (1055236183 : ℕ)^4377*100000000000000^3353 ≤ 43402687505791^3353*2000000000^4377 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1055236183 2000000000 43402687505791 100000000000000 4377 3353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5400749949/10000000000 : ℝ)^4377 ≤ (44745157176731/100000000000000 : ℝ)^3353 := by
    have hnat : (5400749949 : ℕ)^4377*100000000000000^3353 ≤ 44745157176731^3353*10000000000^4377 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5400749949 10000000000 44745157176731 100000000000000 4377 3353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (244001581/1250000000 : ℝ)^4377 ≤ (11852155306447/100000000000000 : ℝ)^3353 := by
    have hnat : (244001581 : ℕ)^4377*100000000000000^3353 ≤ 11852155306447^3353*1250000000^4377 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      244001581 1250000000 11852155306447 100000000000000 4377 3353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4377/1024 : ℝ)) 4377 3353 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1055236183/2000000000 : ℝ), (5400749949/10000000000 : ℝ), (-244001581/1250000000 : ℝ)] ![(43402687505791/100000000000000 : ℝ), (44745157176731/100000000000000 : ℝ), (11852155306447/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1055236183/2000000000 : ℝ)|^4377 ≤ (43402687505791/100000000000000 : ℝ)^3353
        have hw : |(1055236183/2000000000 : ℝ)|=(1055236183/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5400749949/10000000000 : ℝ)|^4377 ≤ (44745157176731/100000000000000 : ℝ)^3353
        have hw : |(5400749949/10000000000 : ℝ)|=(5400749949/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-244001581/1250000000 : ℝ)|^4377 ≤ (11852155306447/100000000000000 : ℝ)^3353
        have hw : |(-244001581/1250000000 : ℝ)|=(244001581/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1417_box_11 (p : ℝ) (hpa : (547/128 : ℝ) ≤ p) (hpb : p ≤ (4377/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2243755413/5000000000 : ℝ)*x 0 + (4220766529/10000000000 : ℝ)*x 1 + (2110383449/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2243755413/5000000000 : ℝ)^4377 ≤ (35134084003041/100000000000000 : ℝ)^3353 := by
    have hnat : (2243755413 : ℕ)^4377*100000000000000^3353 ≤ 35134084003041^3353*5000000000^4377 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2243755413 5000000000 35134084003041 100000000000000 4377 3353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4220766529/10000000000 : ℝ)^4377 ≤ (16216478068749/50000000000000 : ℝ)^3353 := by
    have hnat : (4220766529 : ℕ)^4377*50000000000000^3353 ≤ 16216478068749^3353*10000000000^4377 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4220766529 10000000000 16216478068749 50000000000000 4377 3353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2110383449/5000000000 : ℝ)^4377 ≤ (16216479919443/50000000000000 : ℝ)^3353 := by
    have hnat : (2110383449 : ℕ)^4377*50000000000000^3353 ≤ 16216479919443^3353*5000000000^4377 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2110383449 5000000000 16216479919443 50000000000000 4377 3353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4377/1024 : ℝ)) 4377 3353 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2243755413/5000000000 : ℝ), (4220766529/10000000000 : ℝ), (2110383449/5000000000 : ℝ)] ![(35134084003041/100000000000000 : ℝ), (16216478068749/50000000000000 : ℝ), (16216479919443/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2243755413/5000000000 : ℝ)|^4377 ≤ (35134084003041/100000000000000 : ℝ)^3353
        have hw : |(2243755413/5000000000 : ℝ)|=(2243755413/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4220766529/10000000000 : ℝ)|^4377 ≤ (16216478068749/50000000000000 : ℝ)^3353
        have hw : |(4220766529/10000000000 : ℝ)|=(4220766529/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2110383449/5000000000 : ℝ)|^4377 ≤ (16216479919443/50000000000000 : ℝ)^3353
        have hw : |(2110383449/5000000000 : ℝ)|=(2110383449/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1417_box_12 (p : ℝ) (hpa : (547/128 : ℝ) ≤ p) (hpb : p ≤ (4377/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-944088491/5000000000 : ℝ)*x 0 + (1366991247/2500000000 : ℝ)*x 1 + (2627612219/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (944088491/5000000000 : ℝ)^4377 ≤ (709295974867/6250000000000 : ℝ)^3353 := by
    have hnat : (944088491 : ℕ)^4377*6250000000000^3353 ≤ 709295974867^3353*5000000000^4377 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      944088491 5000000000 709295974867 6250000000000 4377 3353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1366991247/2500000000 : ℝ)^4377 ≤ (45473479483771/100000000000000 : ℝ)^3353 := by
    have hnat : (1366991247 : ℕ)^4377*100000000000000^3353 ≤ 45473479483771^3353*2500000000^4377 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1366991247 2500000000 45473479483771 100000000000000 4377 3353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2627612219/5000000000 : ℝ)^4377 ≤ (269861155627/625000000000 : ℝ)^3353 := by
    have hnat : (2627612219 : ℕ)^4377*625000000000^3353 ≤ 269861155627^3353*5000000000^4377 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2627612219 5000000000 269861155627 625000000000 4377 3353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4377/1024 : ℝ)) 4377 3353 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-944088491/5000000000 : ℝ), (1366991247/2500000000 : ℝ), (2627612219/5000000000 : ℝ)] ![(709295974867/6250000000000 : ℝ), (45473479483771/100000000000000 : ℝ), (269861155627/625000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-944088491/5000000000 : ℝ)|^4377 ≤ (709295974867/6250000000000 : ℝ)^3353
        have hw : |(-944088491/5000000000 : ℝ)|=(944088491/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1366991247/2500000000 : ℝ)|^4377 ≤ (45473479483771/100000000000000 : ℝ)^3353
        have hw : |(1366991247/2500000000 : ℝ)|=(1366991247/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2627612219/5000000000 : ℝ)|^4377 ≤ (269861155627/625000000000 : ℝ)^3353
        have hw : |(2627612219/5000000000 : ℝ)|=(2627612219/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1417_box_13 (p : ℝ) (hpa : (547/128 : ℝ) ≤ p) (hpb : p ≤ (4377/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5378078881/10000000000 : ℝ)*x 0 + (-1005515827/5000000000 : ℝ)*x 1 + (131380621/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5378078881/10000000000 : ℝ)^4377 ≤ (1112503053323/2500000000000 : ℝ)^3353 := by
    have hnat : (5378078881 : ℕ)^4377*2500000000000^3353 ≤ 1112503053323^3353*10000000000^4377 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5378078881 10000000000 1112503053323 2500000000000 4377 3353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1005515827/5000000000 : ℝ)^4377 ≤ (12322088640409/100000000000000 : ℝ)^3353 := by
    have hnat : (1005515827 : ℕ)^4377*100000000000000^3353 ≤ 12322088640409^3353*5000000000^4377 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1005515827 5000000000 12322088640409 100000000000000 4377 3353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (131380621/250000000 : ℝ)^4377 ≤ (10794447302979/25000000000000 : ℝ)^3353 := by
    have hnat : (131380621 : ℕ)^4377*25000000000000^3353 ≤ 10794447302979^3353*250000000^4377 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      131380621 250000000 10794447302979 25000000000000 4377 3353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4377/1024 : ℝ)) 4377 3353 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5378078881/10000000000 : ℝ), (-1005515827/5000000000 : ℝ), (131380621/250000000 : ℝ)] ![(1112503053323/2500000000000 : ℝ), (12322088640409/100000000000000 : ℝ), (10794447302979/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5378078881/10000000000 : ℝ)|^4377 ≤ (1112503053323/2500000000000 : ℝ)^3353
        have hw : |(5378078881/10000000000 : ℝ)|=(5378078881/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1005515827/5000000000 : ℝ)|^4377 ≤ (12322088640409/100000000000000 : ℝ)^3353
        have hw : |(-1005515827/5000000000 : ℝ)|=(1005515827/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(131380621/250000000 : ℝ)|^4377 ≤ (10794447302979/25000000000000 : ℝ)^3353
        have hw : |(131380621/250000000 : ℝ)|=(131380621/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1417_box_14 (p : ℝ) (hpa : (547/128 : ℝ) ≤ p) (hpb : p ≤ (4377/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5378078887/10000000000 : ℝ)*x 0 + (210208991/400000000 : ℝ)*x 1 + (-2011031733/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5378078887/10000000000 : ℝ)^4377 ≤ (1390628818679/3125000000000 : ℝ)^3353 := by
    have hnat : (5378078887 : ℕ)^4377*3125000000000^3353 ≤ 1390628818679^3353*10000000000^4377 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5378078887 10000000000 1390628818679 3125000000000 4377 3353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (210208991/400000000 : ℝ)^4377 ≤ (2698611782173/6250000000000 : ℝ)^3353 := by
    have hnat : (210208991 : ℕ)^4377*6250000000000^3353 ≤ 2698611782173^3353*400000000^4377 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      210208991 400000000 2698611782173 6250000000000 4377 3353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2011031733/10000000000 : ℝ)^4377 ≤ (1232208927229/10000000000000 : ℝ)^3353 := by
    have hnat : (2011031733 : ℕ)^4377*10000000000000^3353 ≤ 1232208927229^3353*10000000000^4377 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2011031733 10000000000 1232208927229 10000000000000 4377 3353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4377/1024 : ℝ)) 4377 3353 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5378078887/10000000000 : ℝ), (210208991/400000000 : ℝ), (-2011031733/10000000000 : ℝ)] ![(1390628818679/3125000000000 : ℝ), (2698611782173/6250000000000 : ℝ), (1232208927229/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5378078887/10000000000 : ℝ)|^4377 ≤ (1390628818679/3125000000000 : ℝ)^3353
        have hw : |(5378078887/10000000000 : ℝ)|=(5378078887/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(210208991/400000000 : ℝ)|^4377 ≤ (2698611782173/6250000000000 : ℝ)^3353
        have hw : |(210208991/400000000 : ℝ)|=(210208991/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2011031733/10000000000 : ℝ)|^4377 ≤ (1232208927229/10000000000000 : ℝ)^3353
        have hw : |(-2011031733/10000000000 : ℝ)|=(2011031733/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1417_box_15 (p : ℝ) (hpa : (547/128 : ℝ) ≤ p) (hpb : p ≤ (4377/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (64565751/156250000 : ℝ)*x 0 + (4398412921/10000000000 : ℝ)*x 1 + (2199207017/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (64565751/156250000 : ℝ)^4377 ≤ (31547498520271/100000000000000 : ℝ)^3353 := by
    have hnat : (64565751 : ℕ)^4377*100000000000000^3353 ≤ 31547498520271^3353*156250000^4377 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      64565751 156250000 31547498520271 100000000000000 4377 3353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4398412921/10000000000 : ℝ)^4377 ≤ (6845249015041/20000000000000 : ℝ)^3353 := by
    have hnat : (4398412921 : ℕ)^4377*20000000000000^3353 ≤ 6845249015041^3353*10000000000^4377 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4398412921 10000000000 6845249015041 20000000000000 4377 3353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2199207017/5000000000 : ℝ)^4377 ≤ (2139141023813/6250000000000 : ℝ)^3353 := by
    have hnat : (2199207017 : ℕ)^4377*6250000000000^3353 ≤ 2139141023813^3353*5000000000^4377 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2199207017 5000000000 2139141023813 6250000000000 4377 3353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4377/1024 : ℝ)) 4377 3353 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(64565751/156250000 : ℝ), (4398412921/10000000000 : ℝ), (2199207017/5000000000 : ℝ)] ![(31547498520271/100000000000000 : ℝ), (6845249015041/20000000000000 : ℝ), (2139141023813/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(64565751/156250000 : ℝ)|^4377 ≤ (31547498520271/100000000000000 : ℝ)^3353
        have hw : |(64565751/156250000 : ℝ)|=(64565751/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4398412921/10000000000 : ℝ)|^4377 ≤ (6845249015041/20000000000000 : ℝ)^3353
        have hw : |(4398412921/10000000000 : ℝ)|=(4398412921/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2199207017/5000000000 : ℝ)|^4377 ≤ (2139141023813/6250000000000 : ℝ)^3353
        have hw : |(2199207017/5000000000 : ℝ)|=(2199207017/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1417_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (547/128 : ℝ) ≤ p) (hpb : p ≤ (4377/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (19711417/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (59/400 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2829/25000 : ℝ)*pair X i i ≤ pair X i h) :
    -(15723/25000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(59089/100000 : ℝ) ∧ (40191/50000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (529/625 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (59/400 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2829/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (59/400 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2829/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (59/400 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2829/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (59/400 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2829/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (59/400 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2829/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (59/400 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2829/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hlower 2 1 (by decide)
  have fm0 := f.main 0
  simp only [pair0,pair1,pair2,Pi.add_apply] at fm0
  have fx01 := abs_le.mp (f.maximal 0 1)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx01
  have fx02 := abs_le.mp (f.maximal 0 2)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx02
  have fm1 := f.main 1
  simp only [pair0,pair1,pair2,Pi.add_apply] at fm1
  have fx10 := abs_le.mp (f.maximal 1 0)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx10
  have fx12 := abs_le.mp (f.maximal 1 2)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx12
  have fm2 := f.main 2
  simp only [pair0,pair1,pair2,Pi.add_apply] at fm2
  have fx20 := abs_le.mp (f.maximal 2 0)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx20
  have fx21 := abs_le.mp (f.maximal 2 1)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx21
  have base65 : ((1 : ℝ)*X 0 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 0).2]
  have base66 : ((-1 : ℝ)*X 0 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 0).1]
  have base67 : ((1 : ℝ)*X 0 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 1).2]
  have base68 : ((-1 : ℝ)*X 0 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 1).1]
  have base69 : ((1 : ℝ)*X 0 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 2).2]
  have base70 : ((-1 : ℝ)*X 0 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 2).1]
  have base71 : ((1 : ℝ)*X 1 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 0).2]
  have base72 : ((-1 : ℝ)*X 1 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 0).1]
  have base73 : ((1 : ℝ)*X 1 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 1).2]
  have base74 : ((-1 : ℝ)*X 1 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 1).1]
  have base75 : ((1 : ℝ)*X 1 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 2).2]
  have base76 : ((-1 : ℝ)*X 1 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 2).1]
  have base77 : ((1 : ℝ)*X 2 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 0).2]
  have base78 : ((-1 : ℝ)*X 2 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 0).1]
  have base79 : ((1 : ℝ)*X 2 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 1).2]
  have base80 : ((-1 : ℝ)*X 2 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 1).1]
  have base81 : ((1 : ℝ)*X 2 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 2).2]
  have base82 : ((-1 : ℝ)*X 2 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 2).1]
  have base83 : ((1 : ℝ)*N 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 0).2]
  have base84 : ((-1 : ℝ)*N 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 0).1]
  have base85 : ((1 : ℝ)*N 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 1).2]
  have base86 : ((-1 : ℝ)*N 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 1).1]
  have base87 : ((1 : ℝ)*N 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 2).2]
  have base88 : ((-1 : ℝ)*N 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 2).1]
  have base89 : ((1 : ℝ)*P 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 0).2]
  have base90 : ((-1 : ℝ)*P 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 0).1]
  have base91 : ((1 : ℝ)*P 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 1).2]
  have base92 : ((-1 : ℝ)*P 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 1).1]
  have base93 : ((1 : ℝ)*P 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 2).2]
  have base94 : ((-1 : ℝ)*P 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 2).1]
  have base95 : ((1 : ℝ)*T) ≤ (3 : ℝ) := by
    linarith only [bounds.2.2.2.2]
  have base96 : ((-1 : ℝ)*T) ≤ (3 : ℝ) := by
    linarith only [bounds.2.2.2.1]
  have hpowlo : (2829/25000 : ℝ) ^ (547/128 : ℝ) ≤ (1129603244463993/12500000000000000000 : ℝ) := by
    have hpowers : (2829/25000 : ℝ)^547 ≤ (1129603244463993/12500000000000000000 : ℝ)^128 := by
      have hnat : (2829 : ℕ)^547*12500000000000000000^128 ≤ 1129603244463993^128*25000^547 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2829 25000 1129603244463993 12500000000000000000 547 128 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2829/25000 : ℝ)) (X := (1129603244463993/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 547 128 (by norm_num) hpowers
    exact h
  have hpowhi : (59/400 : ℝ) ^ (547/128 : ℝ) ≤ (14023443001628431/50000000000000000000 : ℝ) := by
    have hpowers : (59/400 : ℝ)^547 ≤ (14023443001628431/50000000000000000000 : ℝ)^128 := by
      have hnat : (59 : ℕ)^547*50000000000000000000^128 ≤ 14023443001628431^128*400^547 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        59 400 14023443001628431 50000000000000000000 547 128 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (59/400 : ℝ)) (X := (14023443001628431/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 547 128 (by norm_num) hpowers
    exact h
  have hcorner00 : (6251129603244463993/6250000000000000000 : ℝ) ≤ (10000422900790163/10000000000000000 : ℝ) ^ (547/128 : ℝ) := by
    have hpowers : (6251129603244463993/6250000000000000000 : ℝ)^128 ≤ (10000422900790163/10000000000000000 : ℝ)^547 := by
      have hnat : (6251129603244463993 : ℕ)^128*10000000000000000^547 ≤ 10000422900790163^547*6250000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6251129603244463993 6250000000000000000 10000422900790163 10000000000000000 128 547 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000422900790163/10000000000000000 : ℝ)) (X := (6251129603244463993/6250000000000000000 : ℝ)) (by norm_num) 547 128 (by norm_num) hpowers
    exact h
  have hcorner10 : (50018541855979484403/50000000000000000000 : ℝ) ≤ (10000867649196019/10000000000000000 : ℝ) ^ (547/128 : ℝ) := by
    have hpowers : (50018541855979484403/50000000000000000000 : ℝ)^128 ≤ (10000867649196019/10000000000000000 : ℝ)^547 := by
      have hnat : (50018541855979484403 : ℕ)^128*10000000000000000^547 ≤ 10000867649196019^547*50000000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50018541855979484403 50000000000000000000 10000867649196019 10000000000000000 128 547 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000867649196019/10000000000000000 : ℝ)) (X := (50018541855979484403/50000000000000000000 : ℝ)) (by norm_num) 547 128 (by norm_num) hpowers
    exact h
  have hcorner11 : (25014023443001628431/25000000000000000000 : ℝ) ≤ (16002099836163/16000000000000 : ℝ) ^ (547/128 : ℝ) := by
    have hpowers : (25014023443001628431/25000000000000000000 : ℝ)^128 ≤ (16002099836163/16000000000000 : ℝ)^547 := by
      have hnat : (25014023443001628431 : ℕ)^128*16000000000000^547 ≤ 16002099836163^547*25000000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25014023443001628431 25000000000000000000 16002099836163 16000000000000 128 547 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (16002099836163/16000000000000 : ℝ)) (X := (25014023443001628431/25000000000000000000 : ℝ)) (by norm_num) 547 128 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1129603244463993/12500000000000000000 : ℝ) ≤ ((137325546781568347/137360000000000000 : ℝ)+2*(13898387683/10731250000000 : ℝ)*(2829/25000 : ℝ))^(547/128 : ℝ) := by
    rw [show (137325546781568347/137360000000000000 : ℝ)+2*(13898387683/10731250000000 : ℝ)*(2829/25000 : ℝ)=(10000422900790163/10000000000000000 : ℝ) by norm_num, show 1+2*(1129603244463993/12500000000000000000 : ℝ)=(6251129603244463993/6250000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(14023443001628431/50000000000000000000 : ℝ)+(1129603244463993/12500000000000000000 : ℝ) ≤ ((137325546781568347/137360000000000000 : ℝ)+(13898387683/10731250000000 : ℝ)*((59/400 : ℝ)+(2829/25000 : ℝ)))^(547/128 : ℝ) := by
    rw [show (137325546781568347/137360000000000000 : ℝ)+(13898387683/10731250000000 : ℝ)*((59/400 : ℝ)+(2829/25000 : ℝ))=(10000867649196019/10000000000000000 : ℝ) by norm_num, show 1+(14023443001628431/50000000000000000000 : ℝ)+(1129603244463993/12500000000000000000 : ℝ)=(50018541855979484403/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(14023443001628431/50000000000000000000 : ℝ) ≤ ((137325546781568347/137360000000000000 : ℝ)+2*(13898387683/10731250000000 : ℝ)*(59/400 : ℝ))^(547/128 : ℝ) := by
    rw [show (137325546781568347/137360000000000000 : ℝ)+2*(13898387683/10731250000000 : ℝ)*(59/400 : ℝ)=(16002099836163/16000000000000 : ℝ) by norm_num, show 1+2*(14023443001628431/50000000000000000000 : ℝ)=(25014023443001628431/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (137325546781568347/137360000000000000 : ℝ)*(X 1 0+X 2 0)+(13898387683/10731250000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (547/128 : ℝ)) (lo := (2829/25000 : ℝ)) (hi := (59/400 : ℝ)) (c := (137325546781568347/137360000000000000 : ℝ)) (alpha := (13898387683/10731250000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (137325546781568347/137360000000000000 : ℝ)*(X 0 1+X 2 1)+(13898387683/10731250000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (547/128 : ℝ)) (lo := (2829/25000 : ℝ)) (hi := (59/400 : ℝ)) (c := (137325546781568347/137360000000000000 : ℝ)) (alpha := (13898387683/10731250000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (137325546781568347/137360000000000000 : ℝ)*(X 0 2+X 1 2)+(13898387683/10731250000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (547/128 : ℝ)) (lo := (2829/25000 : ℝ)) (hi := (59/400 : ℝ)) (c := (137325546781568347/137360000000000000 : ℝ)) (alpha := (13898387683/10731250000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1819379989/10000000000 : ℝ)*X 0 0+(5386768849/10000000000 : ℝ)*X 0 1+(42084131/78125000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1417_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((211438991/400000000 : ℝ)*X 1 0+(-1957807303/10000000000 : ℝ)*X 1 1+(5386768741/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1417_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5285974673/10000000000 : ℝ)*X 2 0+(2693384371/5000000000 : ℝ)*X 2 1+(-24472593/125000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1417_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1113480717/2500000000 : ℝ)*X 0 0+(1059461943/2500000000 : ℝ)*X 0 1+(2118923933/5000000000 : ℝ)*X 0 2+(1113480717/2500000000 : ℝ)*X 1 0+(1059461943/2500000000 : ℝ)*X 1 1+(2118923933/5000000000 : ℝ)*X 1 2+(1113480717/2500000000 : ℝ)*X 2 0+(1059461943/2500000000 : ℝ)*X 2 1+(2118923933/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1417_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1072588959/5000000000 : ℝ)*X 0 0+(5266344371/10000000000 : ℝ)*X 0 1+(5266344407/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1417_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5370294649/10000000000 : ℝ)*X 1 0+(-2006623653/10000000000 : ℝ)*X 1 1+(2633172533/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1417_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1074058983/2000000000 : ℝ)*X 2 0+(5266344391/10000000000 : ℝ)*X 2 1+(-10033121/50000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1417_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((415981389/1000000000 : ℝ)*X 0 0+(4384851277/10000000000 : ℝ)*X 0 1+(137026589/312500000 : ℝ)*X 0 2+(415981389/1000000000 : ℝ)*X 1 0+(4384851277/10000000000 : ℝ)*X 1 1+(137026589/312500000 : ℝ)*X 1 2+(415981389/1000000000 : ℝ)*X 2 0+(4384851277/10000000000 : ℝ)*X 2 1+(137026589/312500000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1417_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-259572731/1250000000 : ℝ)*X 0 0+(5183101153/10000000000 : ℝ)*X 0 1+(2700374897/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1417_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((5276181259/10000000000 : ℝ)*X 1 0+(-1952012671/10000000000 : ℝ)*X 1 1+(540074959/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1417_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((1055236183/2000000000 : ℝ)*X 2 0+(5400749949/10000000000 : ℝ)*X 2 1+(-244001581/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1417_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((2243755413/5000000000 : ℝ)*X 0 0+(4220766529/10000000000 : ℝ)*X 0 1+(2110383449/5000000000 : ℝ)*X 0 2+(2243755413/5000000000 : ℝ)*X 1 0+(4220766529/10000000000 : ℝ)*X 1 1+(2110383449/5000000000 : ℝ)*X 1 2+(2243755413/5000000000 : ℝ)*X 2 0+(4220766529/10000000000 : ℝ)*X 2 1+(2110383449/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1417_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-944088491/5000000000 : ℝ)*X 0 0+(1366991247/2500000000 : ℝ)*X 0 1+(2627612219/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1417_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((5378078881/10000000000 : ℝ)*X 1 0+(-1005515827/5000000000 : ℝ)*X 1 1+(131380621/250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1417_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((5378078887/10000000000 : ℝ)*X 2 0+(210208991/400000000 : ℝ)*X 2 1+(-2011031733/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1417_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((64565751/156250000 : ℝ)*X 0 0+(4398412921/10000000000 : ℝ)*X 0 1+(2199207017/5000000000 : ℝ)*X 0 2+(64565751/156250000 : ℝ)*X 1 0+(4398412921/10000000000 : ℝ)*X 1 1+(2199207017/5000000000 : ℝ)*X 1 2+(64565751/156250000 : ℝ)*X 2 0+(4398412921/10000000000 : ℝ)*X 2 1+(2199207017/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1417_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-15723/25000 : ℝ) ≤ (-1079815843595049619282279050627/1717000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (37871077/50000000000000 : ℝ)*(lower0) + (49092063/100000000000000 : ℝ)*(upper1) + (129300909/100000000000000 : ℝ)*(lower4) + (4692943/10000000000000 : ℝ)*(lower5) + (1501874532459547/50000000000000 : ℝ)*(major0) + (1501874532459547/50000000000000 : ℝ)*(major1) + (1501874532459547/50000000000000 : ℝ)*(major2) + (85387447/5000000000000 : ℝ)*(sp2) + (7522053273/100000000000000 : ℝ)*(sp3) + (824726627918261/20000000000000 : ℝ)*(sp4) + (2061672310368237/50000000000000 : ℝ)*(sp5) + (1030907857960591/25000000000000 : ℝ)*(sp6) + (1904820695597881/100000000000000 : ℝ)*(sp7) + (28851885483/10000000000000 : ℝ)*(sp13) + (952414108825577/50000000000000 : ℝ)*(f.failure) + (824726627918261/20000000000000 : ℝ)*(f.sum) + (1330236197151/1073125000000000000000000000 : ℝ)*base66 + (133175157014812391/6868000000000000000000000000000 : ℝ)*base68 + (50205912021663609/6868000000000000000000000000000 : ℝ)*base69 + (17640003858171609/6868000000000000000000000000000 : ℝ)*base71 + (470146995369603/8585000000000000000000000000 : ℝ)*base74 + (99974644980731609/6868000000000000000000000000000 : ℝ)*base75 + (25440658862939609/6868000000000000000000000000000 : ℝ)*base77 + (36492466835855609/6868000000000000000000000000000 : ℝ)*base79 + (13639091918611/4292500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (8987391/625000000000000000000 : ℝ)*base90 + (8987391/625000000000000000000 : ℝ)*base92 + (8987391/625000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (59089/100000 : ℝ) ≤ (1014603343754394763230343989873/1717000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (941867/12500000000000 : ℝ)*(upper2) + (10988259/20000000000000 : ℝ)*(lower4) + (27222799/100000000000000 : ℝ)*(lower5) + (1537476998461953/50000000000000 : ℝ)*(major0) + (1537476998461953/50000000000000 : ℝ)*(major1) + (1537476998461953/50000000000000 : ℝ)*(major2) + (418022690081929/10000000000000 : ℝ)*(sp0) + (26126423388263/625000000000 : ℝ)*(sp1) + (2090104692696843/50000000000000 : ℝ)*(sp2) + (974991203939311/50000000000000 : ℝ)*(sp3) + (197609093/100000000000000 : ℝ)*(sp5) + (217569067/50000000000000 : ℝ)*(sp7) + (9277168743/50000000000000 : ℝ)*(sp10) + (1038911883/100000000000000 : ℝ)*(sp12) + (1949982843016757/100000000000000 : ℝ)*(f.failure) + (1045056984932793/25000000000000 : ℝ)*(f.sum) + (5128445806477/536562500000000000000000000 : ℝ)*base66 + (33875195151779109/6868000000000000000000000000000 : ℝ)*base68 + (66013402550635109/6868000000000000000000000000000 : ℝ)*base70 + (137693995727975109/6868000000000000000000000000000 : ℝ)*base72 + (63982103537963/8585000000000000000000000000 : ℝ)*base73 + (66103063906027109/6868000000000000000000000000000 : ℝ)*base76 + (67985299895523109/6868000000000000000000000000000 : ℝ)*base78 + (3618579377004891/6868000000000000000000000000000 : ℝ)*base79 + (5356111382977/2146250000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (10214669/1250000000000000000000 : ℝ)*base89 + (10214669/1250000000000000000000 : ℝ)*base91 + (10214669/1250000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (40191/50000 : ℝ) ≤ (552081593857898935106371760493/686800000000000000000000000000 : ℝ) := by norm_num
    linear_combination (8277023/50000000000000 : ℝ)*(lower1) + (23311809/25000000000000 : ℝ)*(upper2) + (101562097/100000000000000 : ℝ)*(lower3) + (66719719/100000000000000 : ℝ)*(lower5) + (338350526193773/10000000000000 : ℝ)*(major0) + (338350526193773/10000000000000 : ℝ)*(major1) + (338350526193773/10000000000000 : ℝ)*(major2) + (3118896137/50000000000000 : ℝ)*(sp0) + (66170511893/100000000000000 : ℝ)*(sp2) + (8364023041/20000000000000 : ℝ)*(sp3) + (287159919189043/6250000000000 : ℝ)*(sp8) + (2297282472408481/50000000000000 : ℝ)*(sp9) + (4594498774305069/100000000000000 : ℝ)*(sp10) + (1072804442229897/50000000000000 : ℝ)*(sp11) + (85826028183/4000000000 : ℝ)*(f.failure) + (2297282472408481/50000000000000 : ℝ)*(f.sum) + (69622561953/171700000000000000000000000 : ℝ)*base65 + (2810021511824831/1373600000000000000000000000000 : ℝ)*base67 + (1100848549127169/1373600000000000000000000000000 : ℝ)*base70 + (9025612181952769/1373600000000000000000000000000 : ℝ)*base72 + (51450313733/5365625000000000000000000 : ℝ)*base73 + (2714005572399231/1373600000000000000000000000000 : ℝ)*base75 + (7925535729650369/1373600000000000000000000000000 : ℝ)*base78 + (2101288305974369/1373600000000000000000000000000 : ℝ)*base80 + (553686097891/858500000000000000000000000 : ℝ)*base82 + (311/50000000000000000 : ℝ)*base89 + (311/50000000000000000 : ℝ)*base91 + (311/50000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (-529/625 : ℝ) ≤ (-85483498498928324780017713939/101000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (80246183/100000000000000 : ℝ)*(lower1) + (51743053/50000000000000 : ℝ)*(upper3) + (30234073/25000000000000 : ℝ)*(lower4) + (59522171/20000000000000 : ℝ)*(upper5) + (855210311987157/25000000000000 : ℝ)*(major0) + (855210311987157/25000000000000 : ℝ)*(major1) + (855210311987157/25000000000000 : ℝ)*(major2) + (2351861689/50000000000000 : ℝ)*(sp4) + (79494526341/50000000000000 : ℝ)*(sp6) + (6349411577/6250000000000 : ℝ)*(sp7) + (587570354814143/12500000000000 : ℝ)*(sp12) + (4700567542236523/100000000000000 : ℝ)*(sp13) + (4700408553183841/100000000000000 : ℝ)*(sp14) + (433845147763543/20000000000000 : ℝ)*(sp15) + (2169327329402947/100000000000000 : ℝ)*(f.failure) + (4700567542236523/100000000000000 : ℝ)*(f.sum) + (851108110597/126250000000000000000000000 : ℝ)*base66 + (715806521773513/202000000000000000000000000000 : ℝ)*base68 + (734492466123513/202000000000000000000000000000 : ℝ)*base70 + (607545170001513/202000000000000000000000000000 : ℝ)*base72 + (2568167546433/505000000000000000000000000 : ℝ)*base74 + (2569939489327513/202000000000000000000000000000 : ℝ)*base76 + (1236673170730487/202000000000000000000000000000 : ℝ)*base77 + (341489772972487/202000000000000000000000000000 : ℝ)*base79 + (5315882876713/505000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (654101/1250000000000000000000 : ℝ)*base90 + (654101/1250000000000000000000 : ℝ)*base92 + (654101/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1417_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (547/128 : ℝ) ≤ p) (hpb : p ≤ (4377/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (19711417/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (59/400 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2829/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(15723/25000 : ℝ) ≤ X j i ∧ X j i ≤ -(59089/100000 : ℝ) else (40191/50000 : ℝ) ≤ X j i ∧ X j i ≤ (529/625 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1417_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1417_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (547/128 : ℝ) ≤ p) (hpb : p ≤ (4377/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (19711417/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2951/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11311/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(15723/25000 : ℝ) ≤ X j i ∧ X j i ≤ -(59089/100000 : ℝ) else (40191/50000 : ℝ) ≤ X j i ∧ X j i ≤ (529/625 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1417_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1417_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1417_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (547/128 : ℝ) ≤ p) (hpb : p ≤ (4377/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (19711417/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2951/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11311/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(15723/25000 : ℝ) ≤ X j i ∧ X j i ≤ -(59089/100000 : ℝ) else (40191/50000 : ℝ) ≤ X j i ∧ X j i ≤ (529/625 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1417_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
