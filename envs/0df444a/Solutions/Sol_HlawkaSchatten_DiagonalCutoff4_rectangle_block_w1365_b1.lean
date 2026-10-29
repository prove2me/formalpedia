-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1365_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:19:27.095887+00:00
-- url     : https://prove2.me/submissions/f6c9b581-fb9e-4811-8b16-e9a79c5441c7

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
theorem support_rectangle_w1365_s3_0 (p : ℝ) (hpa : (1081/256 : ℝ) ≤ p) (hpb : p ≤ (4325/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-80909149/400000000 : ℝ)*x 0 + (2712161949/5000000000 : ℝ)*x 1 + (5233494997/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (80909149/400000000 : ℝ)^4325 ≤ (12320639002043/100000000000000 : ℝ)^3301 := by
    have hnat : (80909149 : ℕ)^4325*100000000000000^3301 ≤ 12320639002043^3301*400000000^4325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      80909149 400000000 12320639002043 100000000000000 4325 3301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2712161949/5000000000 : ℝ)^4325 ≤ (11217013286609/25000000000000 : ℝ)^3301 := by
    have hnat : (2712161949 : ℕ)^4325*25000000000000^3301 ≤ 11217013286609^3301*5000000000^4325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2712161949 5000000000 11217013286609 25000000000000 4325 3301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5233494997/10000000000 : ℝ)^4325 ≤ (42811307833669/100000000000000 : ℝ)^3301 := by
    have hnat : (5233494997 : ℕ)^4325*100000000000000^3301 ≤ 42811307833669^3301*10000000000^4325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5233494997 10000000000 42811307833669 100000000000000 4325 3301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4325/1024 : ℝ)) 4325 3301 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-80909149/400000000 : ℝ), (2712161949/5000000000 : ℝ), (5233494997/10000000000 : ℝ)] ![(12320639002043/100000000000000 : ℝ), (11217013286609/25000000000000 : ℝ), (42811307833669/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-80909149/400000000 : ℝ)|^4325 ≤ (12320639002043/100000000000000 : ℝ)^3301
        have hw : |(-80909149/400000000 : ℝ)|=(80909149/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2712161949/5000000000 : ℝ)|^4325 ≤ (11217013286609/25000000000000 : ℝ)^3301
        have hw : |(2712161949/5000000000 : ℝ)|=(2712161949/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5233494997/10000000000 : ℝ)|^4325 ≤ (42811307833669/100000000000000 : ℝ)^3301
        have hw : |(5233494997/10000000000 : ℝ)|=(5233494997/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1365_s3_1 (p : ℝ) (hpa : (1081/256 : ℝ) ≤ p) (hpb : p ≤ (4325/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1337966393/2500000000 : ℝ)*x 0 + (-1060100539/5000000000 : ℝ)*x 1 + (5233495059/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1337966393/2500000000 : ℝ)^4325 ≤ (44084412480083/100000000000000 : ℝ)^3301 := by
    have hnat : (1337966393 : ℕ)^4325*100000000000000^3301 ≤ 44084412480083^3301*2500000000^4325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1337966393 2500000000 44084412480083 100000000000000 4325 3301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1060100539/5000000000 : ℝ)^4325 ≤ (6552139500829/50000000000000 : ℝ)^3301 := by
    have hnat : (1060100539 : ℕ)^4325*50000000000000^3301 ≤ 6552139500829^3301*5000000000^4325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1060100539 5000000000 6552139500829 50000000000000 4325 3301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5233495059/10000000000 : ℝ)^4325 ≤ (1712452339927/4000000000000 : ℝ)^3301 := by
    have hnat : (5233495059 : ℕ)^4325*4000000000000^3301 ≤ 1712452339927^3301*10000000000^4325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5233495059 10000000000 1712452339927 4000000000000 4325 3301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4325/1024 : ℝ)) 4325 3301 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1337966393/2500000000 : ℝ), (-1060100539/5000000000 : ℝ), (5233495059/10000000000 : ℝ)] ![(44084412480083/100000000000000 : ℝ), (6552139500829/50000000000000 : ℝ), (1712452339927/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1337966393/2500000000 : ℝ)|^4325 ≤ (44084412480083/100000000000000 : ℝ)^3301
        have hw : |(1337966393/2500000000 : ℝ)|=(1337966393/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1060100539/5000000000 : ℝ)|^4325 ≤ (6552139500829/50000000000000 : ℝ)^3301
        have hw : |(-1060100539/5000000000 : ℝ)|=(1060100539/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5233495059/10000000000 : ℝ)|^4325 ≤ (1712452339927/4000000000000 : ℝ)^3301
        have hw : |(5233495059/10000000000 : ℝ)|=(5233495059/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1365_s3_2 (p : ℝ) (hpa : (1081/256 : ℝ) ≤ p) (hpb : p ≤ (4325/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2675932677/5000000000 : ℝ)*x 0 + (5233495607/10000000000 : ℝ)*x 1 + (-424040129/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2675932677/5000000000 : ℝ)^4325 ≤ (22042205063663/50000000000000 : ℝ)^3301 := by
    have hnat : (2675932677 : ℕ)^4325*50000000000000^3301 ≤ 22042205063663^3301*5000000000^4325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2675932677 5000000000 22042205063663 50000000000000 4325 3301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5233495607/10000000000 : ℝ)^4325 ≤ (42811314371551/100000000000000 : ℝ)^3301 := by
    have hnat : (5233495607 : ℕ)^4325*100000000000000^3301 ≤ 42811314371551^3301*10000000000^4325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5233495607 10000000000 42811314371551 100000000000000 4325 3301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (424040129/2000000000 : ℝ)^4325 ≤ (13104275495233/100000000000000 : ℝ)^3301 := by
    have hnat : (424040129 : ℕ)^4325*100000000000000^3301 ≤ 13104275495233^3301*2000000000^4325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      424040129 2000000000 13104275495233 100000000000000 4325 3301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4325/1024 : ℝ)) 4325 3301 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2675932677/5000000000 : ℝ), (5233495607/10000000000 : ℝ), (-424040129/2000000000 : ℝ)] ![(22042205063663/50000000000000 : ℝ), (42811314371551/100000000000000 : ℝ), (13104275495233/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2675932677/5000000000 : ℝ)|^4325 ≤ (22042205063663/50000000000000 : ℝ)^3301
        have hw : |(2675932677/5000000000 : ℝ)|=(2675932677/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5233495607/10000000000 : ℝ)|^4325 ≤ (42811314371551/100000000000000 : ℝ)^3301
        have hw : |(5233495607/10000000000 : ℝ)|=(5233495607/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-424040129/2000000000 : ℝ)|^4325 ≤ (13104275495233/100000000000000 : ℝ)^3301
        have hw : |(-424040129/2000000000 : ℝ)|=(424040129/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1365_s3_3 (p : ℝ) (hpa : (1081/256 : ℝ) ≤ p) (hpb : p ≤ (4325/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (539963413/1250000000 : ℝ)*x 0 + (824494891/2000000000 : ℝ)*x 1 + (2262819519/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (539963413/1250000000 : ℝ)^4325 ≤ (1331769153197/4000000000000 : ℝ)^3301 := by
    have hnat : (539963413 : ℕ)^4325*4000000000000^3301 ≤ 1331769153197^3301*1250000000^4325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      539963413 1250000000 1331769153197 4000000000000 4325 3301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (824494891/2000000000 : ℝ)^4325 ≤ (6263347359983/20000000000000 : ℝ)^3301 := by
    have hnat : (824494891 : ℕ)^4325*20000000000000^3301 ≤ 6263347359983^3301*2000000000^4325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      824494891 2000000000 6263347359983 20000000000000 4325 3301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2262819519/5000000000 : ℝ)^4325 ≤ (17694517172471/50000000000000 : ℝ)^3301 := by
    have hnat : (2262819519 : ℕ)^4325*50000000000000^3301 ≤ 17694517172471^3301*5000000000^4325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2262819519 5000000000 17694517172471 50000000000000 4325 3301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4325/1024 : ℝ)) 4325 3301 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(539963413/1250000000 : ℝ), (824494891/2000000000 : ℝ), (2262819519/5000000000 : ℝ)] ![(1331769153197/4000000000000 : ℝ), (6263347359983/20000000000000 : ℝ), (17694517172471/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(539963413/1250000000 : ℝ)|^4325 ≤ (1331769153197/4000000000000 : ℝ)^3301
        have hw : |(539963413/1250000000 : ℝ)|=(539963413/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(824494891/2000000000 : ℝ)|^4325 ≤ (6263347359983/20000000000000 : ℝ)^3301
        have hw : |(824494891/2000000000 : ℝ)|=(824494891/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2262819519/5000000000 : ℝ)|^4325 ≤ (17694517172471/50000000000000 : ℝ)^3301
        have hw : |(2262819519/5000000000 : ℝ)|=(2262819519/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1365_s3_4 (p : ℝ) (hpa : (1081/256 : ℝ) ≤ p) (hpb : p ≤ (4325/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2022746409/10000000000 : ℝ)*x 0 + (327142531/625000000 : ℝ)*x 1 + (5423534019/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2022746409/10000000000 : ℝ)^4325 ≤ (12320780131371/100000000000000 : ℝ)^3301 := by
    have hnat : (2022746409 : ℕ)^4325*100000000000000^3301 ≤ 12320780131371^3301*10000000000^4325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2022746409 10000000000 12320780131371 100000000000000 4325 3301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (327142531/625000000 : ℝ)^4325 ≤ (42819726882251/100000000000000 : ℝ)^3301 := by
    have hnat : (327142531 : ℕ)^4325*100000000000000^3301 ≤ 42819726882251^3301*625000000^4325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      327142531 625000000 42819726882251 100000000000000 4325 3301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5423534019/10000000000 : ℝ)^4325 ≤ (179437971861/400000000000 : ℝ)^3301 := by
    have hnat : (5423534019 : ℕ)^4325*400000000000^3301 ≤ 179437971861^3301*10000000000^4325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5423534019 10000000000 179437971861 400000000000 4325 3301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4325/1024 : ℝ)) 4325 3301 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2022746409/10000000000 : ℝ), (327142531/625000000 : ℝ), (5423534019/10000000000 : ℝ)] ![(12320780131371/100000000000000 : ℝ), (42819726882251/100000000000000 : ℝ), (179437971861/400000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2022746409/10000000000 : ℝ)|^4325 ≤ (12320780131371/100000000000000 : ℝ)^3301
        have hw : |(-2022746409/10000000000 : ℝ)|=(2022746409/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(327142531/625000000 : ℝ)|^4325 ≤ (42819726882251/100000000000000 : ℝ)^3301
        have hw : |(327142531/625000000 : ℝ)|=(327142531/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5423534019/10000000000 : ℝ)|^4325 ≤ (179437971861/400000000000 : ℝ)^3301
        have hw : |(5423534019/10000000000 : ℝ)|=(5423534019/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1365_s3_5 (p : ℝ) (hpa : (1081/256 : ℝ) ≤ p) (hpb : p ≤ (4325/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1325646009/2500000000 : ℝ)*x 0 + (-1930162319/10000000000 : ℝ)*x 1 + (1084706803/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1325646009/2500000000 : ℝ)^4325 ≤ (43553304728421/100000000000000 : ℝ)^3301 := by
    have hnat : (1325646009 : ℕ)^4325*100000000000000^3301 ≤ 43553304728421^3301*2500000000^4325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1325646009 2500000000 43553304728421 100000000000000 4325 3301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1930162319/10000000000 : ℝ)^4325 ≤ (2896800583597/25000000000000 : ℝ)^3301 := by
    have hnat : (1930162319 : ℕ)^4325*25000000000000^3301 ≤ 2896800583597^3301*10000000000^4325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1930162319 10000000000 2896800583597 25000000000000 4325 3301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1084706803/2000000000 : ℝ)^4325 ≤ (22429746460951/50000000000000 : ℝ)^3301 := by
    have hnat : (1084706803 : ℕ)^4325*50000000000000^3301 ≤ 22429746460951^3301*2000000000^4325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1084706803 2000000000 22429746460951 50000000000000 4325 3301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4325/1024 : ℝ)) 4325 3301 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1325646009/2500000000 : ℝ), (-1930162319/10000000000 : ℝ), (1084706803/2000000000 : ℝ)] ![(43553304728421/100000000000000 : ℝ), (2896800583597/25000000000000 : ℝ), (22429746460951/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1325646009/2500000000 : ℝ)|^4325 ≤ (43553304728421/100000000000000 : ℝ)^3301
        have hw : |(1325646009/2500000000 : ℝ)|=(1325646009/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1930162319/10000000000 : ℝ)|^4325 ≤ (2896800583597/25000000000000 : ℝ)^3301
        have hw : |(-1930162319/10000000000 : ℝ)|=(1930162319/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1084706803/2000000000 : ℝ)|^4325 ≤ (22429746460951/50000000000000 : ℝ)^3301
        have hw : |(1084706803/2000000000 : ℝ)|=(1084706803/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1365_s3_6 (p : ℝ) (hpa : (1081/256 : ℝ) ≤ p) (hpb : p ≤ (4325/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2651291963/5000000000 : ℝ)*x 0 + (1084706819/2000000000 : ℝ)*x 1 + (-1930162359/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2651291963/5000000000 : ℝ)^4325 ≤ (10888325886163/25000000000000 : ℝ)^3301 := by
    have hnat : (2651291963 : ℕ)^4325*25000000000000^3301 ≤ 10888325886163^3301*5000000000^4325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2651291963 5000000000 10888325886163 25000000000000 4325 3301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1084706819/2000000000 : ℝ)^4325 ≤ (44859493788869/100000000000000 : ℝ)^3301 := by
    have hnat : (1084706819 : ℕ)^4325*100000000000000^3301 ≤ 44859493788869^3301*2000000000^4325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1084706819 2000000000 44859493788869 100000000000000 4325 3301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1930162359/10000000000 : ℝ)^4325 ≤ (11587202649007/100000000000000 : ℝ)^3301 := by
    have hnat : (1930162359 : ℕ)^4325*100000000000000^3301 ≤ 11587202649007^3301*10000000000^4325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1930162359 10000000000 11587202649007 100000000000000 4325 3301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4325/1024 : ℝ)) 4325 3301 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2651291963/5000000000 : ℝ), (1084706819/2000000000 : ℝ), (-1930162359/10000000000 : ℝ)] ![(10888325886163/25000000000000 : ℝ), (44859493788869/100000000000000 : ℝ), (11587202649007/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2651291963/5000000000 : ℝ)|^4325 ≤ (10888325886163/25000000000000 : ℝ)^3301
        have hw : |(2651291963/5000000000 : ℝ)|=(2651291963/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1084706819/2000000000 : ℝ)|^4325 ≤ (44859493788869/100000000000000 : ℝ)^3301
        have hw : |(1084706819/2000000000 : ℝ)|=(1084706819/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1930162359/10000000000 : ℝ)|^4325 ≤ (11587202649007/100000000000000 : ℝ)^3301
        have hw : |(-1930162359/10000000000 : ℝ)|=(1930162359/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1365_s3_7 (p : ℝ) (hpa : (1081/256 : ℝ) ≤ p) (hpb : p ≤ (4325/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4319745787/10000000000 : ℝ)*x 0 + (1130995137/2500000000 : ℝ)*x 1 + (1031035601/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4319745787/10000000000 : ℝ)^4325 ≤ (1040456795299/3125000000000 : ℝ)^3301 := by
    have hnat : (4319745787 : ℕ)^4325*3125000000000^3301 ≤ 1040456795299^3301*10000000000^4325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4319745787 10000000000 1040456795299 3125000000000 4325 3301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1130995137/2500000000 : ℝ)^4325 ≤ (17686021699527/50000000000000 : ℝ)^3301 := by
    have hnat : (1130995137 : ℕ)^4325*50000000000000^3301 ≤ 17686021699527^3301*2500000000^4325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1130995137 2500000000 17686021699527 50000000000000 4325 3301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1031035601/2500000000 : ℝ)^4325 ≤ (1566666956673/5000000000000 : ℝ)^3301 := by
    have hnat : (1031035601 : ℕ)^4325*5000000000000^3301 ≤ 1566666956673^3301*2500000000^4325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1031035601 2500000000 1566666956673 5000000000000 4325 3301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4325/1024 : ℝ)) 4325 3301 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4319745787/10000000000 : ℝ), (1130995137/2500000000 : ℝ), (1031035601/2500000000 : ℝ)] ![(1040456795299/3125000000000 : ℝ), (17686021699527/50000000000000 : ℝ), (1566666956673/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4319745787/10000000000 : ℝ)|^4325 ≤ (1040456795299/3125000000000 : ℝ)^3301
        have hw : |(4319745787/10000000000 : ℝ)|=(4319745787/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1130995137/2500000000 : ℝ)|^4325 ≤ (17686021699527/50000000000000 : ℝ)^3301
        have hw : |(1130995137/2500000000 : ℝ)|=(1130995137/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1031035601/2500000000 : ℝ)|^4325 ≤ (1566666956673/5000000000000 : ℝ)^3301
        have hw : |(1031035601/2500000000 : ℝ)|=(1031035601/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1365_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1081/256 : ℝ) ≤ p) (hpb : p ≤ (4325/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (38908903/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1001/6250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4999/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (219/2000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14989/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (1001/6250 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (4999/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1001/6250 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (4999/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1001/6250 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (4999/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1001/6250 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (4999/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1001/6250 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (4999/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1001/6250 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (4999/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (4999/50000 : ℝ) ^ (1081/256 : ℝ) ≤ (239351927599373/4000000000000000000 : ℝ) := by
    have hpowers : (4999/50000 : ℝ)^1081 ≤ (239351927599373/4000000000000000000 : ℝ)^256 := by
      have hnat : (4999 : ℕ)^1081*4000000000000000000^256 ≤ 239351927599373^256*50000^1081 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4999 50000 239351927599373 4000000000000000000 1081 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4999/50000 : ℝ)) (X := (239351927599373/4000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1081 256 (by norm_num) hpowers
    exact h
  have hpowhi : (1001/6250 : ℝ) ^ (1081/256 : ℝ) ≤ (4376281305558871/10000000000000000000 : ℝ) := by
    have hpowers : (1001/6250 : ℝ)^1081 ≤ (4376281305558871/10000000000000000000 : ℝ)^256 := by
      have hnat : (1001 : ℕ)^1081*10000000000000000000^256 ≤ 4376281305558871^256*6250^1081 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1001 6250 4376281305558871 10000000000000000000 1081 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1001/6250 : ℝ)) (X := (4376281305558871/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1081 256 (by norm_num) hpowers
    exact h
  have hcorner00 : (2000239351927599373/2000000000000000000 : ℝ) ≤ (10000283400996489/10000000000000000 : ℝ) ^ (1081/256 : ℝ) := by
    have hpowers : (2000239351927599373/2000000000000000000 : ℝ)^256 ≤ (10000283400996489/10000000000000000 : ℝ)^1081 := by
      have hnat : (2000239351927599373 : ℕ)^256*10000000000000000^1081 ≤ 10000283400996489^1081*2000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2000239351927599373 2000000000000000000 10000283400996489 10000000000000000 256 1081 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000283400996489/10000000000000000 : ℝ)) (X := (2000239351927599373/2000000000000000000 : ℝ)) (by norm_num) 1081 256 (by norm_num) hpowers
    exact h
  have hcorner10 : (20009949322249114607/20000000000000000000 : ℝ) ≤ (1000117786454139/1000000000000000 : ℝ) ^ (1081/256 : ℝ) := by
    have hpowers : (20009949322249114607/20000000000000000000 : ℝ)^256 ≤ (1000117786454139/1000000000000000 : ℝ)^1081 := by
      have hnat : (20009949322249114607 : ℕ)^256*1000000000000000^1081 ≤ 1000117786454139^1081*20000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20009949322249114607 20000000000000000000 1000117786454139 1000000000000000 256 1081 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000117786454139/1000000000000000 : ℝ)) (X := (20009949322249114607/20000000000000000000 : ℝ)) (by norm_num) 1081 256 (by norm_num) hpowers
    exact h
  have hcorner11 : (5004376281305558871/5000000000000000000 : ℝ) ≤ (10002072328086291/10000000000000000 : ℝ) ^ (1081/256 : ℝ) := by
    have hpowers : (5004376281305558871/5000000000000000000 : ℝ)^256 ≤ (10002072328086291/10000000000000000 : ℝ)^1081 := by
      have hnat : (5004376281305558871 : ℕ)^256*10000000000000000^1081 ≤ 10002072328086291^1081*5000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5004376281305558871 5000000000000000000 10002072328086291 10000000000000000 256 1081 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10002072328086291/10000000000000000 : ℝ)) (X := (5004376281305558871/5000000000000000000 : ℝ)) (by norm_num) 1081 256 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(239351927599373/4000000000000000000 : ℝ) ≤ ((10027303302358838401/10030000000000000000 : ℝ)+2*(298154514967/200600000000000 : ℝ)*(4999/50000 : ℝ))^(1081/256 : ℝ) := by
    rw [show (10027303302358838401/10030000000000000000 : ℝ)+2*(298154514967/200600000000000 : ℝ)*(4999/50000 : ℝ)=(10000283400996489/10000000000000000 : ℝ) by norm_num, show 1+2*(239351927599373/4000000000000000000 : ℝ)=(2000239351927599373/2000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(4376281305558871/10000000000000000000 : ℝ)+(239351927599373/4000000000000000000 : ℝ) ≤ ((10027303302358838401/10030000000000000000 : ℝ)+(298154514967/200600000000000 : ℝ)*((1001/6250 : ℝ)+(4999/50000 : ℝ)))^(1081/256 : ℝ) := by
    rw [show (10027303302358838401/10030000000000000000 : ℝ)+(298154514967/200600000000000 : ℝ)*((1001/6250 : ℝ)+(4999/50000 : ℝ))=(1000117786454139/1000000000000000 : ℝ) by norm_num, show 1+(4376281305558871/10000000000000000000 : ℝ)+(239351927599373/4000000000000000000 : ℝ)=(20009949322249114607/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(4376281305558871/10000000000000000000 : ℝ) ≤ ((10027303302358838401/10030000000000000000 : ℝ)+2*(298154514967/200600000000000 : ℝ)*(1001/6250 : ℝ))^(1081/256 : ℝ) := by
    rw [show (10027303302358838401/10030000000000000000 : ℝ)+2*(298154514967/200600000000000 : ℝ)*(1001/6250 : ℝ)=(10002072328086291/10000000000000000 : ℝ) by norm_num, show 1+2*(4376281305558871/10000000000000000000 : ℝ)=(5004376281305558871/5000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (10027303302358838401/10030000000000000000 : ℝ)*(X 1 0+X 2 0)+(298154514967/200600000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1081/256 : ℝ)) (lo := (4999/50000 : ℝ)) (hi := (1001/6250 : ℝ)) (c := (10027303302358838401/10030000000000000000 : ℝ)) (alpha := (298154514967/200600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (10027303302358838401/10030000000000000000 : ℝ)*(X 0 1+X 2 1)+(298154514967/200600000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1081/256 : ℝ)) (lo := (4999/50000 : ℝ)) (hi := (1001/6250 : ℝ)) (c := (10027303302358838401/10030000000000000000 : ℝ)) (alpha := (298154514967/200600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (10027303302358838401/10030000000000000000 : ℝ)*(X 0 2+X 1 2)+(298154514967/200600000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1081/256 : ℝ)) (lo := (4999/50000 : ℝ)) (hi := (1001/6250 : ℝ)) (c := (10027303302358838401/10030000000000000000 : ℝ)) (alpha := (298154514967/200600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-80909149/400000000 : ℝ)*X 0 0+(2712161949/5000000000 : ℝ)*X 0 1+(5233494997/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1365_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1337966393/2500000000 : ℝ)*X 1 0+(-1060100539/5000000000 : ℝ)*X 1 1+(5233495059/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1365_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2675932677/5000000000 : ℝ)*X 2 0+(5233495607/10000000000 : ℝ)*X 2 1+(-424040129/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1365_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((539963413/1250000000 : ℝ)*X 0 0+(824494891/2000000000 : ℝ)*X 0 1+(2262819519/5000000000 : ℝ)*X 0 2+(539963413/1250000000 : ℝ)*X 1 0+(824494891/2000000000 : ℝ)*X 1 1+(2262819519/5000000000 : ℝ)*X 1 2+(539963413/1250000000 : ℝ)*X 2 0+(824494891/2000000000 : ℝ)*X 2 1+(2262819519/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1365_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2022746409/10000000000 : ℝ)*X 0 0+(327142531/625000000 : ℝ)*X 0 1+(5423534019/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1365_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1325646009/2500000000 : ℝ)*X 1 0+(-1930162319/10000000000 : ℝ)*X 1 1+(1084706803/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1365_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2651291963/5000000000 : ℝ)*X 2 0+(1084706819/2000000000 : ℝ)*X 2 1+(-1930162359/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1365_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4319745787/10000000000 : ℝ)*X 0 0+(1130995137/2500000000 : ℝ)*X 0 1+(1031035601/2500000000 : ℝ)*X 0 2+(4319745787/10000000000 : ℝ)*X 1 0+(1130995137/2500000000 : ℝ)*X 1 1+(1031035601/2500000000 : ℝ)*X 1 2+(4319745787/10000000000 : ℝ)*X 2 0+(1130995137/2500000000 : ℝ)*X 2 1+(1031035601/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1365_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (191050860777998792087638659/31343750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (540901561/25000000000000 : ℝ)*(base19) + (23719321/1562500000000 : ℝ)*(base23) + (5893241/5000000000000 : ℝ)*(upper3) + (115629903/50000000000000 : ℝ)*(upper4) + (122358533/50000000000000 : ℝ)*(upper5) + (482549740094397/12500000000000 : ℝ)*(major0) + (482549740094397/12500000000000 : ℝ)*(major1) + (482549740094397/12500000000000 : ℝ)*(major2) + (5240338024563411/100000000000000 : ℝ)*(sp0) + (2620192817724381/50000000000000 : ℝ)*(sp1) + (5240386281018461/100000000000000 : ℝ)*(sp2) + (1240196308195381/50000000000000 : ℝ)*(sp3) + (9954898319/20000000000000 : ℝ)*(sp4) + (15222886521/100000000000000 : ℝ)*(sp7) + (620101959819321/25000000000000 : ℝ)*(f.failure) + (2620193899527503/50000000000000 : ℝ)*(f.sum) + (16375395605579/5015000000000000000000000000 : ℝ)*base66 + (3377333618177783/2125000000000000000000000000000 : ℝ)*base67 + (28184534539177783/2125000000000000000000000000000 : ℝ)*base69 + (31136234518197217/2125000000000000000000000000000 : ℝ)*base72 + (201235128933/2507500000000000000000000000 : ℝ)*base73 + (43729245531427783/2125000000000000000000000000000 : ℝ)*base75 + (17435999030552783/2125000000000000000000000000000 : ℝ)*base77 + (29299627156552783/2125000000000000000000000000000 : ℝ)*base79 + (22545784943171/5015000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (8314863/625000000000000000000 : ℝ)*base89 + (8314863/625000000000000000000 : ℝ)*base91 + (8314863/625000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (49061576374355669078420553/7835937500000000000000000000000 : ℝ) := by norm_num
    linear_combination (583291923/50000000000000 : ℝ)*(base19) + (572050219/50000000000000 : ℝ)*(base23) + (932997/781250000000 : ℝ)*(upper3) + (9637631/20000000000000 : ℝ)*(lower4) + (139682481/100000000000000 : ℝ)*(upper5) + (60819747894701/1562500000000 : ℝ)*(major0) + (60819747894701/1562500000000 : ℝ)*(major1) + (60819747894701/1562500000000 : ℝ)*(major2) + (1356123093/6250000000000 : ℝ)*(sp1) + (21294801663/100000000000000 : ℝ)*(sp2) + (2641958232244973/50000000000000 : ℝ)*(sp4) + (5283893599936611/100000000000000 : ℝ)*(sp5) + (2641947012793923/50000000000000 : ℝ)*(sp6) + (312626382166061/12500000000000 : ℝ)*(sp7) + (312626382166061/12500000000000 : ℝ)*(f.failure) + (2641958232244973/50000000000000 : ℝ)*(f.sum) + (9270084161807/2507500000000000000000000000 : ℝ)*base65 + (1693218879888761/265625000000000000000000000000 : ℝ)*base68 + (530666837107511/265625000000000000000000000000 : ℝ)*base70 + (793364599548739/265625000000000000000000000000 : ℝ)*base71 + (27215720316021/5015000000000000000000000000 : ℝ)*base74 + (1093523068079057/132812500000000000000000000000 : ℝ)*base75 + (847570485170011/265625000000000000000000000000 : ℝ)*base78 + (1054795657921409/66406250000000000000000000000 : ℝ)*base80 + (14245986003699/5015000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base87 + (2658917/312500000000000000000 : ℝ)*base90 + (2658917/312500000000000000000 : ℝ)*base92 + (2658917/312500000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1365_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1081/256 : ℝ) ≤ p) (hpb : p ≤ (4325/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (38908903/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1001/6250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4999/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (219/2000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14989/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1365_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1365_s4_0 (p : ℝ) (hpa : (1081/256 : ℝ) ≤ p) (hpb : p ≤ (4325/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-506003687/2500000000 : ℝ)*x 0 + (1082739083/2000000000 : ℝ)*x 1 + (1048655687/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (506003687/2500000000 : ℝ)^4325 ≤ (2466180652827/20000000000000 : ℝ)^3301 := by
    have hnat : (506003687 : ℕ)^4325*20000000000000^3301 ≤ 2466180652827^3301*2500000000^4325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      506003687 2500000000 2466180652827 20000000000000 4325 3301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1082739083/2000000000 : ℝ)^4325 ≤ (8950580233099/20000000000000 : ℝ)^3301 := by
    have hnat : (1082739083 : ℕ)^4325*20000000000000^3301 ≤ 8950580233099^3301*2000000000^4325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1082739083 2000000000 8950580233099 20000000000000 4325 3301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1048655687/2000000000 : ℝ)^4325 ≤ (10729048886793/25000000000000 : ℝ)^3301 := by
    have hnat : (1048655687 : ℕ)^4325*25000000000000^3301 ≤ 10729048886793^3301*2000000000^4325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1048655687 2000000000 10729048886793 25000000000000 4325 3301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4325/1024 : ℝ)) 4325 3301 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-506003687/2500000000 : ℝ), (1082739083/2000000000 : ℝ), (1048655687/2000000000 : ℝ)] ![(2466180652827/20000000000000 : ℝ), (8950580233099/20000000000000 : ℝ), (10729048886793/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-506003687/2500000000 : ℝ)|^4325 ≤ (2466180652827/20000000000000 : ℝ)^3301
        have hw : |(-506003687/2500000000 : ℝ)|=(506003687/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1082739083/2000000000 : ℝ)|^4325 ≤ (8950580233099/20000000000000 : ℝ)^3301
        have hw : |(1082739083/2000000000 : ℝ)|=(1082739083/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1048655687/2000000000 : ℝ)|^4325 ≤ (10729048886793/25000000000000 : ℝ)^3301
        have hw : |(1048655687/2000000000 : ℝ)|=(1048655687/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1365_s4_1 (p : ℝ) (hpa : (1081/256 : ℝ) ≤ p) (hpb : p ≤ (4325/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5349147069/10000000000 : ℝ)*x 0 + (-2110866341/10000000000 : ℝ)*x 1 + (5243277579/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5349147069/10000000000 : ℝ)^4325 ≤ (22027537728473/50000000000000 : ℝ)^3301 := by
    have hnat : (5349147069 : ℕ)^4325*50000000000000^3301 ≤ 22027537728473^3301*10000000000^4325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5349147069 10000000000 22027537728473 50000000000000 4325 3301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2110866341/10000000000 : ℝ)^4325 ≤ (3257184541831/25000000000000 : ℝ)^3301 := by
    have hnat : (2110866341 : ℕ)^4325*25000000000000^3301 ≤ 3257184541831^3301*10000000000^4325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2110866341 10000000000 3257184541831 25000000000000 4325 3301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5243277579/10000000000 : ℝ)^4325 ≤ (5364523295923/12500000000000 : ℝ)^3301 := by
    have hnat : (5243277579 : ℕ)^4325*12500000000000^3301 ≤ 5364523295923^3301*10000000000^4325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5243277579 10000000000 5364523295923 12500000000000 4325 3301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4325/1024 : ℝ)) 4325 3301 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5349147069/10000000000 : ℝ), (-2110866341/10000000000 : ℝ), (5243277579/10000000000 : ℝ)] ![(22027537728473/50000000000000 : ℝ), (3257184541831/25000000000000 : ℝ), (5364523295923/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5349147069/10000000000 : ℝ)|^4325 ≤ (22027537728473/50000000000000 : ℝ)^3301
        have hw : |(5349147069/10000000000 : ℝ)|=(5349147069/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2110866341/10000000000 : ℝ)|^4325 ≤ (3257184541831/25000000000000 : ℝ)^3301
        have hw : |(-2110866341/10000000000 : ℝ)|=(2110866341/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5243277579/10000000000 : ℝ)|^4325 ≤ (5364523295923/12500000000000 : ℝ)^3301
        have hw : |(5243277579/10000000000 : ℝ)|=(5243277579/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1365_s4_2 (p : ℝ) (hpa : (1081/256 : ℝ) ≤ p) (hpb : p ≤ (4325/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5349146659/10000000000 : ℝ)*x 0 + (163852449/312500000 : ℝ)*x 1 + (-26385823/125000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5349146659/10000000000 : ℝ)^4325 ≤ (8811014206547/20000000000000 : ℝ)^3301 := by
    have hnat : (5349146659 : ℕ)^4325*20000000000000^3301 ≤ 8811014206547^3301*10000000000^4325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5349146659 10000000000 8811014206547 20000000000000 4325 3301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (163852449/312500000 : ℝ)^4325 ≤ (2145809741433/5000000000000 : ℝ)^3301 := by
    have hnat : (163852449 : ℕ)^4325*5000000000000^3301 ≤ 2145809741433^3301*312500000^4325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      163852449 312500000 2145809741433 5000000000000 4325 3301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (26385823/125000000 : ℝ)^4325 ≤ (6514367057893/50000000000000 : ℝ)^3301 := by
    have hnat : (26385823 : ℕ)^4325*50000000000000^3301 ≤ 6514367057893^3301*125000000^4325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      26385823 125000000 6514367057893 50000000000000 4325 3301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4325/1024 : ℝ)) 4325 3301 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5349146659/10000000000 : ℝ), (163852449/312500000 : ℝ), (-26385823/125000000 : ℝ)] ![(8811014206547/20000000000000 : ℝ), (2145809741433/5000000000000 : ℝ), (6514367057893/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5349146659/10000000000 : ℝ)|^4325 ≤ (8811014206547/20000000000000 : ℝ)^3301
        have hw : |(5349146659/10000000000 : ℝ)|=(5349146659/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(163852449/312500000 : ℝ)|^4325 ≤ (2145809741433/5000000000000 : ℝ)^3301
        have hw : |(163852449/312500000 : ℝ)|=(163852449/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-26385823/125000000 : ℝ)|^4325 ≤ (6514367057893/50000000000000 : ℝ)^3301
        have hw : |(-26385823/125000000 : ℝ)|=(26385823/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1365_s4_3 (p : ℝ) (hpa : (1081/256 : ℝ) ≤ p) (hpb : p ≤ (4325/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4320490219/10000000000 : ℝ)*x 0 + (4143940069/10000000000 : ℝ)*x 1 + (11259953/25000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4320490219/10000000000 : ℝ)^4325 ≤ (33302135289389/100000000000000 : ℝ)^3301 := by
    have hnat : (4320490219 : ℕ)^4325*100000000000000^3301 ≤ 33302135289389^3301*10000000000^4325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4320490219 10000000000 33302135289389 100000000000000 4325 3301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4143940069/10000000000 : ℝ)^4325 ≤ (31530558913899/100000000000000 : ℝ)^3301 := by
    have hnat : (4143940069 : ℕ)^4325*100000000000000^3301 ≤ 31530558913899^3301*10000000000^4325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4143940069 10000000000 31530558913899 100000000000000 4325 3301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (11259953/25000000 : ℝ)^4325 ≤ (35167305777443/100000000000000 : ℝ)^3301 := by
    have hnat : (11259953 : ℕ)^4325*100000000000000^3301 ≤ 35167305777443^3301*25000000^4325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      11259953 25000000 35167305777443 100000000000000 4325 3301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4325/1024 : ℝ)) 4325 3301 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4320490219/10000000000 : ℝ), (4143940069/10000000000 : ℝ), (11259953/25000000 : ℝ)] ![(33302135289389/100000000000000 : ℝ), (31530558913899/100000000000000 : ℝ), (35167305777443/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4320490219/10000000000 : ℝ)|^4325 ≤ (33302135289389/100000000000000 : ℝ)^3301
        have hw : |(4320490219/10000000000 : ℝ)|=(4320490219/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4143940069/10000000000 : ℝ)|^4325 ≤ (31530558913899/100000000000000 : ℝ)^3301
        have hw : |(4143940069/10000000000 : ℝ)|=(4143940069/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(11259953/25000000 : ℝ)|^4325 ≤ (35167305777443/100000000000000 : ℝ)^3301
        have hw : |(11259953/25000000 : ℝ)|=(11259953/25000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1365_s4_4 (p : ℝ) (hpa : (1081/256 : ℝ) ≤ p) (hpb : p ≤ (4325/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-253003499/1250000000 : ℝ)*x 0 + (524390479/1000000000 : ℝ)*x 1 + (5413065461/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (253003499/1250000000 : ℝ)^4325 ≤ (2466201796061/20000000000000 : ℝ)^3301 := by
    have hnat : (253003499 : ℕ)^4325*20000000000000^3301 ≤ 2466201796061^3301*1250000000^4325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      253003499 1250000000 2466201796061 20000000000000 4325 3301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (524390479/1000000000 : ℝ)^4325 ≤ (2682682045923/6250000000000 : ℝ)^3301 := by
    have hnat : (524390479 : ℕ)^4325*6250000000000^3301 ≤ 2682682045923^3301*1000000000^4325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      524390479 1000000000 2682682045923 6250000000000 4325 3301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5413065461/10000000000 : ℝ)^4325 ≤ (44746078266169/100000000000000 : ℝ)^3301 := by
    have hnat : (5413065461 : ℕ)^4325*100000000000000^3301 ≤ 44746078266169^3301*10000000000^4325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5413065461 10000000000 44746078266169 100000000000000 4325 3301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4325/1024 : ℝ)) 4325 3301 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-253003499/1250000000 : ℝ), (524390479/1000000000 : ℝ), (5413065461/10000000000 : ℝ)] ![(2466201796061/20000000000000 : ℝ), (2682682045923/6250000000000 : ℝ), (44746078266169/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-253003499/1250000000 : ℝ)|^4325 ≤ (2466201796061/20000000000000 : ℝ)^3301
        have hw : |(-253003499/1250000000 : ℝ)|=(253003499/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(524390479/1000000000 : ℝ)|^4325 ≤ (2682682045923/6250000000000 : ℝ)^3301
        have hw : |(524390479/1000000000 : ℝ)|=(524390479/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5413065461/10000000000 : ℝ)|^4325 ≤ (44746078266169/100000000000000 : ℝ)^3301
        have hw : |(5413065461/10000000000 : ℝ)|=(5413065461/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1365_s4_5 (p : ℝ) (hpa : (1081/256 : ℝ) ≤ p) (hpb : p ≤ (4325/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2652568633/5000000000 : ℝ)*x 0 + (-1941078659/10000000000 : ℝ)*x 1 + (5413065317/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2652568633/5000000000 : ℝ)^4325 ≤ (21790391724567/50000000000000 : ℝ)^3301 := by
    have hnat : (2652568633 : ℕ)^4325*50000000000000^3301 ≤ 21790391724567^3301*5000000000^4325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2652568633 5000000000 21790391724567 50000000000000 4325 3301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1941078659/10000000000 : ℝ)^4325 ≤ (11673139833117/100000000000000 : ℝ)^3301 := by
    have hnat : (1941078659 : ℕ)^4325*100000000000000^3301 ≤ 11673139833117^3301*10000000000^4325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1941078659 10000000000 11673139833117 100000000000000 4325 3301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5413065317/10000000000 : ℝ)^4325 ≤ (11186519176641/25000000000000 : ℝ)^3301 := by
    have hnat : (5413065317 : ℕ)^4325*25000000000000^3301 ≤ 11186519176641^3301*10000000000^4325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5413065317 10000000000 11186519176641 25000000000000 4325 3301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4325/1024 : ℝ)) 4325 3301 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2652568633/5000000000 : ℝ), (-1941078659/10000000000 : ℝ), (5413065317/10000000000 : ℝ)] ![(21790391724567/50000000000000 : ℝ), (11673139833117/100000000000000 : ℝ), (11186519176641/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2652568633/5000000000 : ℝ)|^4325 ≤ (21790391724567/50000000000000 : ℝ)^3301
        have hw : |(2652568633/5000000000 : ℝ)|=(2652568633/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1941078659/10000000000 : ℝ)|^4325 ≤ (11673139833117/100000000000000 : ℝ)^3301
        have hw : |(-1941078659/10000000000 : ℝ)|=(1941078659/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5413065317/10000000000 : ℝ)|^4325 ≤ (11186519176641/25000000000000 : ℝ)^3301
        have hw : |(5413065317/10000000000 : ℝ)|=(5413065317/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1365_s4_6 (p : ℝ) (hpa : (1081/256 : ℝ) ≤ p) (hpb : p ≤ (4325/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5305137249/10000000000 : ℝ)*x 0 + (2706532717/5000000000 : ℝ)*x 1 + (-970539261/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305137249/10000000000 : ℝ)^4325 ≤ (544759790827/1250000000000 : ℝ)^3301 := by
    have hnat : (5305137249 : ℕ)^4325*1250000000000^3301 ≤ 544759790827^3301*10000000000^4325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305137249 10000000000 544759790827 1250000000000 4325 3301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2706532717/5000000000 : ℝ)^4325 ≤ (44746077973743/100000000000000 : ℝ)^3301 := by
    have hnat : (2706532717 : ℕ)^4325*100000000000000^3301 ≤ 44746077973743^3301*5000000000^4325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2706532717 5000000000 44746077973743 100000000000000 4325 3301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (970539261/5000000000 : ℝ)^4325 ≤ (11673138753659/100000000000000 : ℝ)^3301 := by
    have hnat : (970539261 : ℕ)^4325*100000000000000^3301 ≤ 11673138753659^3301*5000000000^4325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      970539261 5000000000 11673138753659 100000000000000 4325 3301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4325/1024 : ℝ)) 4325 3301 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305137249/10000000000 : ℝ), (2706532717/5000000000 : ℝ), (-970539261/5000000000 : ℝ)] ![(544759790827/1250000000000 : ℝ), (44746077973743/100000000000000 : ℝ), (11673138753659/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305137249/10000000000 : ℝ)|^4325 ≤ (544759790827/1250000000000 : ℝ)^3301
        have hw : |(5305137249/10000000000 : ℝ)|=(5305137249/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2706532717/5000000000 : ℝ)|^4325 ≤ (44746077973743/100000000000000 : ℝ)^3301
        have hw : |(2706532717/5000000000 : ℝ)|=(2706532717/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-970539261/5000000000 : ℝ)|^4325 ≤ (11673138753659/100000000000000 : ℝ)^3301
        have hw : |(-970539261/5000000000 : ℝ)|=(970539261/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1365_s4_7 (p : ℝ) (hpa : (1081/256 : ℝ) ≤ p) (hpb : p ≤ (4325/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2160259139/5000000000 : ℝ)*x 0 + (4502657881/10000000000 : ℝ)*x 1 + (4145269483/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2160259139/5000000000 : ℝ)^4325 ≤ (4162802332293/12500000000000 : ℝ)^3301 := by
    have hnat : (2160259139 : ℕ)^4325*12500000000000^3301 ≤ 4162802332293^3301*5000000000^4325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2160259139 5000000000 4162802332293 12500000000000 4325 3301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4502657881/10000000000 : ℝ)^4325 ≤ (7030753721563/20000000000000 : ℝ)^3301 := by
    have hnat : (4502657881 : ℕ)^4325*20000000000000^3301 ≤ 7030753721563^3301*10000000000^4325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4502657881 10000000000 7030753721563 20000000000000 4325 3301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4145269483/10000000000 : ℝ)^4325 ≤ (7885953180259/25000000000000 : ℝ)^3301 := by
    have hnat : (4145269483 : ℕ)^4325*25000000000000^3301 ≤ 7885953180259^3301*10000000000^4325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4145269483 10000000000 7885953180259 25000000000000 4325 3301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4325/1024 : ℝ)) 4325 3301 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2160259139/5000000000 : ℝ), (4502657881/10000000000 : ℝ), (4145269483/10000000000 : ℝ)] ![(4162802332293/12500000000000 : ℝ), (7030753721563/20000000000000 : ℝ), (7885953180259/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2160259139/5000000000 : ℝ)|^4325 ≤ (4162802332293/12500000000000 : ℝ)^3301
        have hw : |(2160259139/5000000000 : ℝ)|=(2160259139/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4502657881/10000000000 : ℝ)|^4325 ≤ (7030753721563/20000000000000 : ℝ)^3301
        have hw : |(4502657881/10000000000 : ℝ)|=(4502657881/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4145269483/10000000000 : ℝ)|^4325 ≤ (7885953180259/25000000000000 : ℝ)^3301
        have hw : |(4145269483/10000000000 : ℝ)|=(4145269483/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1365_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1081/256 : ℝ) ≤ p) (hpb : p ≤ (4325/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (38908903/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14989/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (219/2000 : ℝ)*pair X i i ≤ pair X i h) :
    (11159/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14767/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14989/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (219/2000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14989/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (219/2000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14989/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (219/2000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14989/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (219/2000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14989/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (219/2000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14989/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (219/2000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (219/2000 : ℝ) ^ (1081/256 : ℝ) ≤ (4392846531463519/50000000000000000000 : ℝ) := by
    have hpowers : (219/2000 : ℝ)^1081 ≤ (4392846531463519/50000000000000000000 : ℝ)^256 := by
      have hnat : (219 : ℕ)^1081*50000000000000000000^256 ≤ 4392846531463519^256*2000^1081 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        219 2000 4392846531463519 50000000000000000000 1081 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (219/2000 : ℝ)) (X := (4392846531463519/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1081 256 (by norm_num) hpowers
    exact h
  have hpowhi : (14989/100000 : ℝ) ^ (1081/256 : ℝ) ≤ (33080439406952753/100000000000000000000 : ℝ) := by
    have hpowers : (14989/100000 : ℝ)^1081 ≤ (33080439406952753/100000000000000000000 : ℝ)^256 := by
      have hnat : (14989 : ℕ)^1081*100000000000000000000^256 ≤ 33080439406952753^256*100000^1081 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14989 100000 33080439406952753 100000000000000000000 1081 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14989/100000 : ℝ)) (X := (33080439406952753/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1081 256 (by norm_num) hpowers
    exact h
  have hcorner00 : (25004392846531463519/25000000000000000000 : ℝ) ≤ (2000083218746831/2000000000000000 : ℝ) ^ (1081/256 : ℝ) := by
    have hpowers : (25004392846531463519/25000000000000000000 : ℝ)^256 ≤ (2000083218746831/2000000000000000 : ℝ)^1081 := by
      have hnat : (25004392846531463519 : ℕ)^256*2000000000000000^1081 ≤ 2000083218746831^1081*25000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25004392846531463519 25000000000000000000 2000083218746831 2000000000000000 256 1081 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000083218746831/2000000000000000 : ℝ)) (X := (25004392846531463519/25000000000000000000 : ℝ)) (by norm_num) 1081 256 (by norm_num) hpowers
    exact h
  have hcorner10 : (100041866132469879791/100000000000000000000 : ℝ) ≤ (1250123913252733/1250000000000000 : ℝ) ^ (1081/256 : ℝ) := by
    have hpowers : (100041866132469879791/100000000000000000000 : ℝ)^256 ≤ (1250123913252733/1250000000000000 : ℝ)^1081 := by
      have hnat : (100041866132469879791 : ℕ)^256*1250000000000000^1081 ≤ 1250123913252733^1081*100000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100041866132469879791 100000000000000000000 1250123913252733 1250000000000000 256 1081 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250123913252733/1250000000000000 : ℝ)) (X := (100041866132469879791/100000000000000000000 : ℝ)) (by norm_num) 1081 256 (by norm_num) hpowers
    exact h
  have hcorner11 : (50033080439406952753/50000000000000000000 : ℝ) ≤ (10001566518309573/10000000000000000 : ℝ) ^ (1081/256 : ℝ) := by
    have hpowers : (50033080439406952753/50000000000000000000 : ℝ)^256 ≤ (10001566518309573/10000000000000000 : ℝ)^1081 := by
      have hnat : (50033080439406952753 : ℕ)^256*10000000000000000^1081 ≤ 10001566518309573^1081*50000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50033080439406952753 50000000000000000000 10001566518309573 10000000000000000 256 1081 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001566518309573/10000000000000000 : ℝ)) (X := (50033080439406952753/50000000000000000000 : ℝ)) (by norm_num) 1081 256 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(4392846531463519/50000000000000000000 : ℝ) ≤ ((8075816690698284989/8078000000000000000 : ℝ)+2*(575212287709/403900000000000 : ℝ)*(219/2000 : ℝ))^(1081/256 : ℝ) := by
    rw [show (8075816690698284989/8078000000000000000 : ℝ)+2*(575212287709/403900000000000 : ℝ)*(219/2000 : ℝ)=(2000083218746831/2000000000000000 : ℝ) by norm_num, show 1+2*(4392846531463519/50000000000000000000 : ℝ)=(25004392846531463519/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(33080439406952753/100000000000000000000 : ℝ)+(4392846531463519/50000000000000000000 : ℝ) ≤ ((8075816690698284989/8078000000000000000 : ℝ)+(575212287709/403900000000000 : ℝ)*((14989/100000 : ℝ)+(219/2000 : ℝ)))^(1081/256 : ℝ) := by
    rw [show (8075816690698284989/8078000000000000000 : ℝ)+(575212287709/403900000000000 : ℝ)*((14989/100000 : ℝ)+(219/2000 : ℝ))=(1250123913252733/1250000000000000 : ℝ) by norm_num, show 1+(33080439406952753/100000000000000000000 : ℝ)+(4392846531463519/50000000000000000000 : ℝ)=(100041866132469879791/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(33080439406952753/100000000000000000000 : ℝ) ≤ ((8075816690698284989/8078000000000000000 : ℝ)+2*(575212287709/403900000000000 : ℝ)*(14989/100000 : ℝ))^(1081/256 : ℝ) := by
    rw [show (8075816690698284989/8078000000000000000 : ℝ)+2*(575212287709/403900000000000 : ℝ)*(14989/100000 : ℝ)=(10001566518309573/10000000000000000 : ℝ) by norm_num, show 1+2*(33080439406952753/100000000000000000000 : ℝ)=(50033080439406952753/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (8075816690698284989/8078000000000000000 : ℝ)*(X 1 0+X 2 0)+(575212287709/403900000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1081/256 : ℝ)) (lo := (219/2000 : ℝ)) (hi := (14989/100000 : ℝ)) (c := (8075816690698284989/8078000000000000000 : ℝ)) (alpha := (575212287709/403900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (8075816690698284989/8078000000000000000 : ℝ)*(X 0 1+X 2 1)+(575212287709/403900000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1081/256 : ℝ)) (lo := (219/2000 : ℝ)) (hi := (14989/100000 : ℝ)) (c := (8075816690698284989/8078000000000000000 : ℝ)) (alpha := (575212287709/403900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (8075816690698284989/8078000000000000000 : ℝ)*(X 0 2+X 1 2)+(575212287709/403900000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1081/256 : ℝ)) (lo := (219/2000 : ℝ)) (hi := (14989/100000 : ℝ)) (c := (8075816690698284989/8078000000000000000 : ℝ)) (alpha := (575212287709/403900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-506003687/2500000000 : ℝ)*X 0 0+(1082739083/2000000000 : ℝ)*X 0 1+(1048655687/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1365_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5349147069/10000000000 : ℝ)*X 1 0+(-2110866341/10000000000 : ℝ)*X 1 1+(5243277579/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1365_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5349146659/10000000000 : ℝ)*X 2 0+(163852449/312500000 : ℝ)*X 2 1+(-26385823/125000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1365_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4320490219/10000000000 : ℝ)*X 0 0+(4143940069/10000000000 : ℝ)*X 0 1+(11259953/25000000 : ℝ)*X 0 2+(4320490219/10000000000 : ℝ)*X 1 0+(4143940069/10000000000 : ℝ)*X 1 1+(11259953/25000000 : ℝ)*X 1 2+(4320490219/10000000000 : ℝ)*X 2 0+(4143940069/10000000000 : ℝ)*X 2 1+(11259953/25000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1365_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-253003499/1250000000 : ℝ)*X 0 0+(524390479/1000000000 : ℝ)*X 0 1+(5413065461/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1365_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2652568633/5000000000 : ℝ)*X 1 0+(-1941078659/10000000000 : ℝ)*X 1 1+(5413065317/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1365_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5305137249/10000000000 : ℝ)*X 2 0+(2706532717/5000000000 : ℝ)*X 2 1+(-970539261/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1365_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2160259139/5000000000 : ℝ)*X 0 0+(4502657881/10000000000 : ℝ)*X 0 1+(4145269483/10000000000 : ℝ)*X 0 2+(2160259139/5000000000 : ℝ)*X 1 0+(4502657881/10000000000 : ℝ)*X 1 1+(4145269483/10000000000 : ℝ)*X 1 2+(2160259139/5000000000 : ℝ)*X 2 0+(4502657881/10000000000 : ℝ)*X 2 1+(4145269483/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1365_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3918295861394786175842547309/403900000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (143280729/20000000000000 : ℝ)*(base19) + (149325823/50000000000000 : ℝ)*(base23) + (49281207/100000000000000 : ℝ)*(lower2) + (1689941/20000000000000 : ℝ)*(lower3) + (9980989/20000000000000 : ℝ)*(lower5) + (4322717948149627/100000000000000 : ℝ)*(major0) + (4322717948149627/100000000000000 : ℝ)*(major1) + (4322717948149627/100000000000000 : ℝ)*(major2) + (5867968806240933/100000000000000 : ℝ)*(sp0) + (234718362966307/4000000000000 : ℝ)*(sp1) + (586797458092909/10000000000000 : ℝ)*(sp2) + (277746069334673/10000000000000 : ℝ)*(sp3) + (6073339803/100000000000000 : ℝ)*(sp4) + (1886127427/12500000000000 : ℝ)*(sp5) + (277746069334673/10000000000000 : ℝ)*(f.failure) + (91687107493449/1562500000000 : ℝ)*(f.sum) + (217691642905407/20195000000000000000000000000 : ℝ)*base66 + (13480399704657909103/807800000000000000000000000000000 : ℝ)*base67 + (1311708435145490897/807800000000000000000000000000000 : ℝ)*base70 + (542681232963109103/807800000000000000000000000000000 : ℝ)*base71 + (21099152012299/10097500000000000000000000000 : ℝ)*base73 + (6141091991685690897/807800000000000000000000000000000 : ℝ)*base76 + (3334879193053090897/807800000000000000000000000000000 : ℝ)*base78 + (7782630282471090897/807800000000000000000000000000000 : ℝ)*base80 + (1411949906543/20195000000000000000000000000 : ℝ)*base81 + (1206281/250000000000000000000 : ℝ)*base90 + (1206281/250000000000000000000 : ℝ)*base92 + (1206281/250000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3226372367802695993588913/450781250000000000000000000000 : ℝ) := by norm_num
    linear_combination (1229460107/100000000000000 : ℝ)*(base19) + (1404063019/100000000000000 : ℝ)*(base23) + (58013813/25000000000000 : ℝ)*(upper3) + (53898787/100000000000000 : ℝ)*(lower4) + (93066937/100000000000000 : ℝ)*(upper5) + (272175375381483/6250000000000 : ℝ)*(major0) + (272175375381483/6250000000000 : ℝ)*(major1) + (272175375381483/6250000000000 : ℝ)*(major2) + (7266837651/50000000000000 : ℝ)*(sp1) + (1280890583/5000000000000 : ℝ)*(sp2) + (5911533653757269/100000000000000 : ℝ)*(sp4) + (295575894531093/5000000000000 : ℝ)*(sp5) + (591150663188259/10000000000000 : ℝ)*(sp6) + (2798078119873829/100000000000000 : ℝ)*(sp7) + (2798078119873829/100000000000000 : ℝ)*(f.failure) + (5911533653757269/100000000000000 : ℝ)*(f.sum) + (1152378645673/1442500000000000000000000000 : ℝ)*base65 + (66531863233233741/7212500000000000000000000000000 : ℝ)*base67 + (3745380628371241/7212500000000000000000000000000 : ℝ)*base69 + (20620064616478759/7212500000000000000000000000000 : ℝ)*base72 + (4168674973841/2885000000000000000000000000 : ℝ)*base73 + (107107015133208741/7212500000000000000000000000000 : ℝ)*base75 + (6119455090971241/7212500000000000000000000000000 : ℝ)*base77 + (79188744606858741/7212500000000000000000000000000 : ℝ)*base79 + (2816090614841/2885000000000000000000000000 : ℝ)*base81 + (15200413/2500000000000000000000 : ℝ)*base90 + (15200413/2500000000000000000000 : ℝ)*base92 + (15200413/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1365_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1081/256 : ℝ) ≤ p) (hpb : p ≤ (4325/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (38908903/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14989/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (219/2000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11159/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14767/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1365_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1365_s5_0 (p : ℝ) (hpa : (1081/256 : ℝ) ≤ p) (hpb : p ≤ (4325/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1012114159/5000000000 : ℝ)*x 0 + (5411838127/10000000000 : ℝ)*x 1 + (327812193/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1012114159/5000000000 : ℝ)^4325 ≤ (246652160947/2000000000000 : ℝ)^3301 := by
    have hnat : (1012114159 : ℕ)^4325*2000000000000^3301 ≤ 246652160947^3301*5000000000^4325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1012114159 5000000000 246652160947 2000000000000 4325 3301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5411838127/10000000000 : ℝ)^4325 ≤ (22366392988549/50000000000000 : ℝ)^3301 := by
    have hnat : (5411838127 : ℕ)^4325*50000000000000^3301 ≤ 22366392988549^3301*10000000000^4325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5411838127 10000000000 22366392988549 50000000000000 4325 3301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (327812193/625000000 : ℝ)^4325 ≤ (1341706436149/3125000000000 : ℝ)^3301 := by
    have hnat : (327812193 : ℕ)^4325*3125000000000^3301 ≤ 1341706436149^3301*625000000^4325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      327812193 625000000 1341706436149 3125000000000 4325 3301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4325/1024 : ℝ)) 4325 3301 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1012114159/5000000000 : ℝ), (5411838127/10000000000 : ℝ), (327812193/625000000 : ℝ)] ![(246652160947/2000000000000 : ℝ), (22366392988549/50000000000000 : ℝ), (1341706436149/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1012114159/5000000000 : ℝ)|^4325 ≤ (246652160947/2000000000000 : ℝ)^3301
        have hw : |(-1012114159/5000000000 : ℝ)|=(1012114159/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5411838127/10000000000 : ℝ)|^4325 ≤ (22366392988549/50000000000000 : ℝ)^3301
        have hw : |(5411838127/10000000000 : ℝ)|=(5411838127/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(327812193/625000000 : ℝ)|^4325 ≤ (1341706436149/3125000000000 : ℝ)^3301
        have hw : |(327812193/625000000 : ℝ)|=(327812193/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1365_s5_1 (p : ℝ) (hpa : (1081/256 : ℝ) ≤ p) (hpb : p ≤ (4325/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5348670939/10000000000 : ℝ)*x 0 + (-2109223731/10000000000 : ℝ)*x 1 + (5244995103/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5348670939/10000000000 : ℝ)^4325 ≤ (8809987544747/20000000000000 : ℝ)^3301 := by
    have hnat : (5348670939 : ℕ)^4325*20000000000000^3301 ≤ 8809987544747^3301*10000000000^4325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5348670939 10000000000 8809987544747 20000000000000 4325 3301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2109223731/10000000000 : ℝ)^4325 ≤ (13015456143937/100000000000000 : ℝ)^3301 := by
    have hnat : (2109223731 : ℕ)^4325*100000000000000^3301 ≤ 13015456143937^3301*10000000000^4325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2109223731 10000000000 13015456143937 100000000000000 4325 3301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5244995103/10000000000 : ℝ)^4325 ≤ (8586921223529/20000000000000 : ℝ)^3301 := by
    have hnat : (5244995103 : ℕ)^4325*20000000000000^3301 ≤ 8586921223529^3301*10000000000^4325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5244995103 10000000000 8586921223529 20000000000000 4325 3301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4325/1024 : ℝ)) 4325 3301 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5348670939/10000000000 : ℝ), (-2109223731/10000000000 : ℝ), (5244995103/10000000000 : ℝ)] ![(8809987544747/20000000000000 : ℝ), (13015456143937/100000000000000 : ℝ), (8586921223529/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5348670939/10000000000 : ℝ)|^4325 ≤ (8809987544747/20000000000000 : ℝ)^3301
        have hw : |(5348670939/10000000000 : ℝ)|=(5348670939/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2109223731/10000000000 : ℝ)|^4325 ≤ (13015456143937/100000000000000 : ℝ)^3301
        have hw : |(-2109223731/10000000000 : ℝ)|=(2109223731/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5244995103/10000000000 : ℝ)|^4325 ≤ (8586921223529/20000000000000 : ℝ)^3301
        have hw : |(5244995103/10000000000 : ℝ)|=(5244995103/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1365_s5_2 (p : ℝ) (hpa : (1081/256 : ℝ) ≤ p) (hpb : p ≤ (4325/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (534867091/1000000000 : ℝ)*x 0 + (5244995147/10000000000 : ℝ)*x 1 + (-210922371/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (534867091/1000000000 : ℝ)^4325 ≤ (44049937410811/100000000000000 : ℝ)^3301 := by
    have hnat : (534867091 : ℕ)^4325*100000000000000^3301 ≤ 44049937410811^3301*1000000000^4325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      534867091 1000000000 44049937410811 100000000000000 4325 3301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5244995147/10000000000 : ℝ)^4325 ≤ (2683412911847/6250000000000 : ℝ)^3301 := by
    have hnat : (5244995147 : ℕ)^4325*6250000000000^3301 ≤ 2683412911847^3301*10000000000^4325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5244995147 10000000000 2683412911847 6250000000000 4325 3301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (210922371/1000000000 : ℝ)^4325 ≤ (13015455974153/100000000000000 : ℝ)^3301 := by
    have hnat : (210922371 : ℕ)^4325*100000000000000^3301 ≤ 13015455974153^3301*1000000000^4325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      210922371 1000000000 13015455974153 100000000000000 4325 3301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4325/1024 : ℝ)) 4325 3301 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(534867091/1000000000 : ℝ), (5244995147/10000000000 : ℝ), (-210922371/1000000000 : ℝ)] ![(44049937410811/100000000000000 : ℝ), (2683412911847/6250000000000 : ℝ), (13015455974153/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(534867091/1000000000 : ℝ)|^4325 ≤ (44049937410811/100000000000000 : ℝ)^3301
        have hw : |(534867091/1000000000 : ℝ)|=(534867091/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5244995147/10000000000 : ℝ)|^4325 ≤ (2683412911847/6250000000000 : ℝ)^3301
        have hw : |(5244995147/10000000000 : ℝ)|=(5244995147/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-210922371/1000000000 : ℝ)|^4325 ≤ (13015455974153/100000000000000 : ℝ)^3301
        have hw : |(-210922371/1000000000 : ℝ)|=(210922371/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1365_s5_3 (p : ℝ) (hpa : (1081/256 : ℝ) ≤ p) (hpb : p ≤ (4325/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1080154783/2500000000 : ℝ)*x 0 + (518462357/1250000000 : ℝ)*x 1 + (4500190043/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1080154783/2500000000 : ℝ)^4325 ≤ (4162929648951/12500000000000 : ℝ)^3301 := by
    have hnat : (1080154783 : ℕ)^4325*12500000000000^3301 ≤ 4162929648951^3301*2500000000^4325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1080154783 2500000000 4162929648951 12500000000000 4325 3301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (518462357/1250000000 : ℝ)^4325 ≤ (6313607230611/20000000000000 : ℝ)^3301 := by
    have hnat : (518462357 : ℕ)^4325*20000000000000^3301 ≤ 6313607230611^3301*1250000000^4325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      518462357 1250000000 6313607230611 20000000000000 4325 3301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4500190043/10000000000 : ℝ)^4325 ≤ (35128526637663/100000000000000 : ℝ)^3301 := by
    have hnat : (4500190043 : ℕ)^4325*100000000000000^3301 ≤ 35128526637663^3301*10000000000^4325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4500190043 10000000000 35128526637663 100000000000000 4325 3301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4325/1024 : ℝ)) 4325 3301 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1080154783/2500000000 : ℝ), (518462357/1250000000 : ℝ), (4500190043/10000000000 : ℝ)] ![(4162929648951/12500000000000 : ℝ), (6313607230611/20000000000000 : ℝ), (35128526637663/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1080154783/2500000000 : ℝ)|^4325 ≤ (4162929648951/12500000000000 : ℝ)^3301
        have hw : |(1080154783/2500000000 : ℝ)|=(1080154783/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(518462357/1250000000 : ℝ)|^4325 ≤ (6313607230611/20000000000000 : ℝ)^3301
        have hw : |(518462357/1250000000 : ℝ)|=(518462357/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4500190043/10000000000 : ℝ)|^4325 ≤ (35128526637663/100000000000000 : ℝ)^3301
        have hw : |(4500190043/10000000000 : ℝ)|=(4500190043/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1365_s5_4 (p : ℝ) (hpa : (1081/256 : ℝ) ≤ p) (hpb : p ≤ (4325/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1012120183/5000000000 : ℝ)*x 0 + (5245595729/10000000000 : ℝ)*x 1 + (5411234391/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1012120183/5000000000 : ℝ)^4325 ≤ (3083176054989/25000000000000 : ℝ)^3301 := by
    have hnat : (1012120183 : ℕ)^4325*25000000000000^3301 ≤ 3083176054989^3301*5000000000^4325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1012120183 5000000000 3083176054989 25000000000000 4325 3301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5245595729/10000000000 : ℝ)^4325 ≤ (21470524015099/50000000000000 : ℝ)^3301 := by
    have hnat : (5245595729 : ℕ)^4325*50000000000000^3301 ≤ 21470524015099^3301*10000000000^4325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5245595729 10000000000 21470524015099 50000000000000 4325 3301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5411234391/10000000000 : ℝ)^4325 ≤ (1397695241579/3125000000000 : ℝ)^3301 := by
    have hnat : (5411234391 : ℕ)^4325*3125000000000^3301 ≤ 1397695241579^3301*10000000000^4325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5411234391 10000000000 1397695241579 3125000000000 4325 3301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4325/1024 : ℝ)) 4325 3301 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1012120183/5000000000 : ℝ), (5245595729/10000000000 : ℝ), (5411234391/10000000000 : ℝ)] ![(3083176054989/25000000000000 : ℝ), (21470524015099/50000000000000 : ℝ), (1397695241579/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1012120183/5000000000 : ℝ)|^4325 ≤ (3083176054989/25000000000000 : ℝ)^3301
        have hw : |(-1012120183/5000000000 : ℝ)|=(1012120183/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5245595729/10000000000 : ℝ)|^4325 ≤ (21470524015099/50000000000000 : ℝ)^3301
        have hw : |(5245595729/10000000000 : ℝ)|=(5245595729/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5411234391/10000000000 : ℝ)|^4325 ≤ (1397695241579/3125000000000 : ℝ)^3301
        have hw : |(5411234391/10000000000 : ℝ)|=(5411234391/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1365_s5_5 (p : ℝ) (hpa : (1081/256 : ℝ) ≤ p) (hpb : p ≤ (4325/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1326396049/2500000000 : ℝ)*x 0 + (-971492231/5000000000 : ℝ)*x 1 + (2705617193/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1326396049/2500000000 : ℝ)^4325 ≤ (8717118776443/20000000000000 : ℝ)^3301 := by
    have hnat : (1326396049 : ℕ)^4325*20000000000000^3301 ≤ 8717118776443^3301*2500000000^4325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1326396049 2500000000 8717118776443 20000000000000 4325 3301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (971492231/5000000000 : ℝ)^4325 ≤ (11688158426657/100000000000000 : ℝ)^3301 := by
    have hnat : (971492231 : ℕ)^4325*100000000000000^3301 ≤ 11688158426657^3301*5000000000^4325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      971492231 5000000000 11688158426657 100000000000000 4325 3301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2705617193/5000000000 : ℝ)^4325 ≤ (44726247676381/100000000000000 : ℝ)^3301 := by
    have hnat : (2705617193 : ℕ)^4325*100000000000000^3301 ≤ 44726247676381^3301*5000000000^4325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2705617193 5000000000 44726247676381 100000000000000 4325 3301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4325/1024 : ℝ)) 4325 3301 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1326396049/2500000000 : ℝ), (-971492231/5000000000 : ℝ), (2705617193/5000000000 : ℝ)] ![(8717118776443/20000000000000 : ℝ), (11688158426657/100000000000000 : ℝ), (44726247676381/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1326396049/2500000000 : ℝ)|^4325 ≤ (8717118776443/20000000000000 : ℝ)^3301
        have hw : |(1326396049/2500000000 : ℝ)|=(1326396049/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-971492231/5000000000 : ℝ)|^4325 ≤ (11688158426657/100000000000000 : ℝ)^3301
        have hw : |(-971492231/5000000000 : ℝ)|=(971492231/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2705617193/5000000000 : ℝ)|^4325 ≤ (44726247676381/100000000000000 : ℝ)^3301
        have hw : |(2705617193/5000000000 : ℝ)|=(2705617193/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1365_s5_6 (p : ℝ) (hpa : (1081/256 : ℝ) ≤ p) (hpb : p ≤ (4325/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5305584223/10000000000 : ℝ)*x 0 + (2705617173/5000000000 : ℝ)*x 1 + (-12143653/62500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305584223/10000000000 : ℝ)^4325 ≤ (43585594172827/100000000000000 : ℝ)^3301 := by
    have hnat : (5305584223 : ℕ)^4325*100000000000000^3301 ≤ 43585594172827^3301*10000000000^4325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305584223 10000000000 43585594172827 100000000000000 4325 3301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2705617173/5000000000 : ℝ)^4325 ≤ (22363123621601/50000000000000 : ℝ)^3301 := by
    have hnat : (2705617173 : ℕ)^4325*50000000000000^3301 ≤ 22363123621601^3301*5000000000^4325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2705617173 5000000000 22363123621601 50000000000000 4325 3301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (12143653/62500000 : ℝ)^4325 ≤ (11688158568527/100000000000000 : ℝ)^3301 := by
    have hnat : (12143653 : ℕ)^4325*100000000000000^3301 ≤ 11688158568527^3301*62500000^4325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      12143653 62500000 11688158568527 100000000000000 4325 3301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4325/1024 : ℝ)) 4325 3301 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305584223/10000000000 : ℝ), (2705617173/5000000000 : ℝ), (-12143653/62500000 : ℝ)] ![(43585594172827/100000000000000 : ℝ), (22363123621601/50000000000000 : ℝ), (11688158568527/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305584223/10000000000 : ℝ)|^4325 ≤ (43585594172827/100000000000000 : ℝ)^3301
        have hw : |(5305584223/10000000000 : ℝ)|=(5305584223/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2705617173/5000000000 : ℝ)|^4325 ≤ (22363123621601/50000000000000 : ℝ)^3301
        have hw : |(2705617173/5000000000 : ℝ)|=(2705617173/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-12143653/62500000 : ℝ)|^4325 ≤ (11688158568527/100000000000000 : ℝ)^3301
        have hw : |(-12143653/62500000 : ℝ)|=(12143653/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1365_s5_7 (p : ℝ) (hpa : (1081/256 : ℝ) ≤ p) (hpb : p ≤ (4325/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (864128927/2000000000 : ℝ)*x 0 + (899784223/2000000000 : ℝ)*x 1 + (829794871/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (864128927/2000000000 : ℝ)^4325 ≤ (16651847374889/50000000000000 : ℝ)^3301 := by
    have hnat : (864128927 : ℕ)^4325*50000000000000^3301 ≤ 16651847374889^3301*2000000000^4325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      864128927 2000000000 16651847374889 50000000000000 4325 3301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (899784223/2000000000 : ℝ)^4325 ≤ (35115549238799/100000000000000 : ℝ)^3301 := by
    have hnat : (899784223 : ℕ)^4325*100000000000000^3301 ≤ 35115549238799^3301*2000000000^4325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      899784223 2000000000 35115549238799 100000000000000 4325 3301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (829794871/2000000000 : ℝ)^4325 ≤ (631615119933/2000000000000 : ℝ)^3301 := by
    have hnat : (829794871 : ℕ)^4325*2000000000000^3301 ≤ 631615119933^3301*2000000000^4325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      829794871 2000000000 631615119933 2000000000000 4325 3301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4325/1024 : ℝ)) 4325 3301 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(864128927/2000000000 : ℝ), (899784223/2000000000 : ℝ), (829794871/2000000000 : ℝ)] ![(16651847374889/50000000000000 : ℝ), (35115549238799/100000000000000 : ℝ), (631615119933/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(864128927/2000000000 : ℝ)|^4325 ≤ (16651847374889/50000000000000 : ℝ)^3301
        have hw : |(864128927/2000000000 : ℝ)|=(864128927/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(899784223/2000000000 : ℝ)|^4325 ≤ (35115549238799/100000000000000 : ℝ)^3301
        have hw : |(899784223/2000000000 : ℝ)|=(899784223/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(829794871/2000000000 : ℝ)|^4325 ≤ (631615119933/2000000000000 : ℝ)^3301
        have hw : |(829794871/2000000000 : ℝ)|=(829794871/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1365_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1081/256 : ℝ) ≤ p) (hpb : p ≤ (4325/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (38908903/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14767/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11159/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (2799/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1841/12500 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14767/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11159/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14767/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11159/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14767/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11159/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14767/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11159/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14767/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11159/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14767/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11159/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11159/100000 : ℝ) ^ (1081/256 : ℝ) ≤ (9515879327532113/100000000000000000000 : ℝ) := by
    have hpowers : (11159/100000 : ℝ)^1081 ≤ (9515879327532113/100000000000000000000 : ℝ)^256 := by
      have hnat : (11159 : ℕ)^1081*100000000000000000000^256 ≤ 9515879327532113^256*100000^1081 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11159 100000 9515879327532113 100000000000000000000 1081 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11159/100000 : ℝ)) (X := (9515879327532113/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1081 256 (by norm_num) hpowers
    exact h
  have hpowhi : (14767/100000 : ℝ) ^ (1081/256 : ℝ) ≤ (6212076971409479/20000000000000000000 : ℝ) := by
    have hpowers : (14767/100000 : ℝ)^1081 ≤ (6212076971409479/20000000000000000000 : ℝ)^256 := by
      have hnat : (14767 : ℕ)^1081*20000000000000000000^256 ≤ 6212076971409479^256*100000^1081 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14767 100000 6212076971409479 20000000000000000000 1081 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14767/100000 : ℝ)) (X := (6212076971409479/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1081 256 (by norm_num) hpowers
    exact h
  have hcorner00 : (50009515879327532113/50000000000000000000 : ℝ) ≤ (2000090134623943/2000000000000000 : ℝ) ^ (1081/256 : ℝ) := by
    have hpowers : (50009515879327532113/50000000000000000000 : ℝ)^256 ≤ (2000090134623943/2000000000000000 : ℝ)^1081 := by
      have hnat : (50009515879327532113 : ℕ)^256*2000000000000000^1081 ≤ 2000090134623943^1081*50000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50009515879327532113 50000000000000000000 2000090134623943 2000000000000000 256 1081 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000090134623943/2000000000000000 : ℝ)) (X := (50009515879327532113/50000000000000000000 : ℝ)) (by norm_num) 1081 256 (by norm_num) hpowers
    exact h
  have hcorner10 : (25010144066046144877/25000000000000000000 : ℝ) ≤ (1000096076925607/1000000000000000 : ℝ) ^ (1081/256 : ℝ) := by
    have hpowers : (25010144066046144877/25000000000000000000 : ℝ)^256 ≤ (1000096076925607/1000000000000000 : ℝ)^1081 := by
      have hnat : (25010144066046144877 : ℕ)^256*1000000000000000^1081 ≤ 1000096076925607^1081*25000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25010144066046144877 25000000000000000000 1000096076925607 1000000000000000 256 1081 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000096076925607/1000000000000000 : ℝ)) (X := (25010144066046144877/25000000000000000000 : ℝ)) (by norm_num) 1081 256 (by norm_num) hpowers
    exact h
  have hcorner11 : (10006212076971409479/10000000000000000000 : ℝ) ≤ (400058834615697/400000000000000 : ℝ) ^ (1081/256 : ℝ) := by
    have hpowers : (10006212076971409479/10000000000000000000 : ℝ)^256 ≤ (400058834615697/400000000000000 : ℝ)^1081 := by
      have hnat : (10006212076971409479 : ℕ)^256*400000000000000^1081 ≤ 400058834615697^1081*10000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10006212076971409479 10000000000000000000 400058834615697 400000000000000 256 1081 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (400058834615697/400000000000000 : ℝ)) (X := (10006212076971409479/10000000000000000000 : ℝ)) (by norm_num) 1081 256 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(9515879327532113/100000000000000000000 : ℝ) ≤ ((3607024170304476083/3608000000000000000 : ℝ)+2*(102019227271/72160000000000 : ℝ)*(11159/100000 : ℝ))^(1081/256 : ℝ) := by
    rw [show (3607024170304476083/3608000000000000000 : ℝ)+2*(102019227271/72160000000000 : ℝ)*(11159/100000 : ℝ)=(2000090134623943/2000000000000000 : ℝ) by norm_num, show 1+2*(9515879327532113/100000000000000000000 : ℝ)=(50009515879327532113/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(6212076971409479/20000000000000000000 : ℝ)+(9515879327532113/100000000000000000000 : ℝ) ≤ ((3607024170304476083/3608000000000000000 : ℝ)+(102019227271/72160000000000 : ℝ)*((14767/100000 : ℝ)+(11159/100000 : ℝ)))^(1081/256 : ℝ) := by
    rw [show (3607024170304476083/3608000000000000000 : ℝ)+(102019227271/72160000000000 : ℝ)*((14767/100000 : ℝ)+(11159/100000 : ℝ))=(1000096076925607/1000000000000000 : ℝ) by norm_num, show 1+(6212076971409479/20000000000000000000 : ℝ)+(9515879327532113/100000000000000000000 : ℝ)=(25010144066046144877/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(6212076971409479/20000000000000000000 : ℝ) ≤ ((3607024170304476083/3608000000000000000 : ℝ)+2*(102019227271/72160000000000 : ℝ)*(14767/100000 : ℝ))^(1081/256 : ℝ) := by
    rw [show (3607024170304476083/3608000000000000000 : ℝ)+2*(102019227271/72160000000000 : ℝ)*(14767/100000 : ℝ)=(400058834615697/400000000000000 : ℝ) by norm_num, show 1+2*(6212076971409479/20000000000000000000 : ℝ)=(10006212076971409479/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (3607024170304476083/3608000000000000000 : ℝ)*(X 1 0+X 2 0)+(102019227271/72160000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1081/256 : ℝ)) (lo := (11159/100000 : ℝ)) (hi := (14767/100000 : ℝ)) (c := (3607024170304476083/3608000000000000000 : ℝ)) (alpha := (102019227271/72160000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (3607024170304476083/3608000000000000000 : ℝ)*(X 0 1+X 2 1)+(102019227271/72160000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1081/256 : ℝ)) (lo := (11159/100000 : ℝ)) (hi := (14767/100000 : ℝ)) (c := (3607024170304476083/3608000000000000000 : ℝ)) (alpha := (102019227271/72160000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (3607024170304476083/3608000000000000000 : ℝ)*(X 0 2+X 1 2)+(102019227271/72160000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1081/256 : ℝ)) (lo := (11159/100000 : ℝ)) (hi := (14767/100000 : ℝ)) (c := (3607024170304476083/3608000000000000000 : ℝ)) (alpha := (102019227271/72160000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1012114159/5000000000 : ℝ)*X 0 0+(5411838127/10000000000 : ℝ)*X 0 1+(327812193/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1365_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5348670939/10000000000 : ℝ)*X 1 0+(-2109223731/10000000000 : ℝ)*X 1 1+(5244995103/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1365_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((534867091/1000000000 : ℝ)*X 2 0+(5244995147/10000000000 : ℝ)*X 2 1+(-210922371/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1365_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1080154783/2500000000 : ℝ)*X 0 0+(518462357/1250000000 : ℝ)*X 0 1+(4500190043/10000000000 : ℝ)*X 0 2+(1080154783/2500000000 : ℝ)*X 1 0+(518462357/1250000000 : ℝ)*X 1 1+(4500190043/10000000000 : ℝ)*X 1 2+(1080154783/2500000000 : ℝ)*X 2 0+(518462357/1250000000 : ℝ)*X 2 1+(4500190043/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1365_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1012120183/5000000000 : ℝ)*X 0 0+(5245595729/10000000000 : ℝ)*X 0 1+(5411234391/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1365_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1326396049/2500000000 : ℝ)*X 1 0+(-971492231/5000000000 : ℝ)*X 1 1+(2705617193/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1365_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5305584223/10000000000 : ℝ)*X 2 0+(2705617173/5000000000 : ℝ)*X 2 1+(-12143653/62500000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1365_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((864128927/2000000000 : ℝ)*X 0 0+(899784223/2000000000 : ℝ)*X 0 1+(829794871/2000000000 : ℝ)*X 0 2+(864128927/2000000000 : ℝ)*X 1 0+(899784223/2000000000 : ℝ)*X 1 1+(829794871/2000000000 : ℝ)*X 1 2+(864128927/2000000000 : ℝ)*X 2 0+(899784223/2000000000 : ℝ)*X 2 1+(829794871/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1365_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (289649608571128557985228311/90200000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (693176399/100000000000000 : ℝ)*(base19) + (327483397/50000000000000 : ℝ)*(base23) + (71971301/100000000000000 : ℝ)*(upper3) + (611073/20000000000000 : ℝ)*(upper4) + (5464837/6250000000000 : ℝ)*(upper5) + (2207663279576561/50000000000000 : ℝ)*(major0) + (2207663279576561/50000000000000 : ℝ)*(major1) + (2207663279576561/50000000000000 : ℝ)*(major2) + (599367279560607/10000000000000 : ℝ)*(sp0) + (46825688601973/781250000000 : ℝ)*(sp1) + (1498422044815537/25000000000000 : ℝ)*(sp2) + (2836957399421943/100000000000000 : ℝ)*(sp3) + (16038622873/100000000000000 : ℝ)*(sp4) + (3388807793/50000000000000 : ℝ)*(sp7) + (2836964177037529/100000000000000 : ℝ)*(f.failure) + (5993688834228943/100000000000000 : ℝ)*(f.sum) + (991518489399/1804000000000000000000000000 : ℝ)*base65 + (115175196152858233/16400000000000000000000000000000 : ℝ)*base67 + (27907775650058233/16400000000000000000000000000000 : ℝ)*base69 + (64588114797941767/16400000000000000000000000000000 : ℝ)*base72 + (221184436381/360800000000000000000000000 : ℝ)*base74 + (82888697825541767/16400000000000000000000000000000 : ℝ)*base76 + (77978793032458233/16400000000000000000000000000000 : ℝ)*base77 + (66768046789258233/16400000000000000000000000000000 : ℝ)*base79 + (784975794167/360800000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (6779313/2500000000000000000000 : ℝ)*base90 + (6779313/2500000000000000000000 : ℝ)*base92 + (6779313/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (9774540419950892249391/1804000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1020527063/100000000000000 : ℝ)*(base19) + (274860959/25000000000000 : ℝ)*(base23) + (54981673/50000000000000 : ℝ)*(upper3) + (12836847/50000000000000 : ℝ)*(lower4) + (126939799/100000000000000 : ℝ)*(upper5) + (2223703873632599/50000000000000 : ℝ)*(major0) + (2223703873632599/50000000000000 : ℝ)*(major1) + (2223703873632599/50000000000000 : ℝ)*(major2) + (21373647657/100000000000000 : ℝ)*(sp1) + (266868427/1250000000000 : ℝ)*(sp2) + (1207447624882487/20000000000000 : ℝ)*(sp4) + (1207443146047543/20000000000000 : ℝ)*(sp5) + (3018607837747219/50000000000000 : ℝ)*(sp6) + (28575771895093/1000000000000 : ℝ)*(sp7) + (28575771895093/1000000000000 : ℝ)*(f.failure) + (1207447624882487/20000000000000 : ℝ)*(f.sum) + (1261404668169/1804000000000000000000000000 : ℝ)*base65 + (100396819404992753/16400000000000000000000000000000 : ℝ)*base68 + (46837600512992753/16400000000000000000000000000000 : ℝ)*base70 + (32909801752192753/16400000000000000000000000000000 : ℝ)*base72 + (2170313165683/1804000000000000000000000000 : ℝ)*base74 + (237957590440607247/16400000000000000000000000000000 : ℝ)*base75 + (1247376787407247/16400000000000000000000000000000 : ℝ)*base77 + (162511925765807247/16400000000000000000000000000000 : ℝ)*base79 + (3611364163311/1804000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (212979/25000000000000000000 : ℝ)*base89 + (212979/25000000000000000000 : ℝ)*base91 + (212979/25000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1365_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1081/256 : ℝ) ≤ p) (hpb : p ≤ (4325/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (38908903/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14767/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11159/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2799/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1841/12500 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1365_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1365_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1081/256 : ℝ) ≤ p) (hpb : p ≤ (4325/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (38908903/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1001/6250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4999/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2799/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1841/12500 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1365_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1365_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1365_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (1081/256 : ℝ) ≤ p) (hpb : p ≤ (4325/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (38908903/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1001/6250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4999/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2799/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1841/12500 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1365_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
