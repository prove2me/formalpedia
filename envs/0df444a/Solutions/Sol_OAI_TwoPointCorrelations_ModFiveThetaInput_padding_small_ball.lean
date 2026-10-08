-- Prove2me | solution 1 for OAI.TwoPointCorrelations.ModFiveThetaInput.padding_small_ball
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-08T01:45:07.460899+00:00
-- url     : https://prove2.me/submissions/a2d11cad-67ac-4f60-a433-72a9d25d5846

import Mathlib
import Definitions.Def_OAIChowlaTwoPointDefs

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.FiniteProbability
namespace OAI

/-!
# Finite weighted sampling for the random-prime rank argument

The prime labels in the rank argument have a nonuniform reciprocal law.
The corresponding finite-sum probability identities account for that law.
-/

namespace TwoPointCorrelations

open _root_.Finset


namespace FiniteLaw

variable {α β ι : Type*} [Fintype α] [Fintype β] [Fintype ι]




lemma average_mono (μ : FiniteLaw α) {f g : α → ℝ} (h : ∀ x, f x ≤ g x) :
    μ.average f ≤ μ.average g := sum_le_sum (fun x _ => mul_le_mul_of_nonneg_left (h x) (μ.nonneg x))



lemma average_mul_const (μ : FiniteLaw α) (f : α → ℝ) (c : ℝ) :
    μ.average (fun x => f x * c) = μ.average f * c := by
  simp only [average, mul_assoc, sum_mul]












end FiniteLaw

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.SieveProducts
namespace OAI

/-! Local-density products for the rough sieve. The only prime information
needed is a lower bound for the ordinary reciprocal sum. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

lemma reciprocal_square_sum_le_one (P : Finset ℕ) (hP : ∀ p ∈ P, 2 ≤ p) :
    (∑ p ∈ P, 1 / (p : ℝ) ^ 2) ≤ 1 := by
  have hsub : P ⊆ Ioo 1 (P.sup id + 1) := by
    intro p hp
    exact mem_Ioo.mpr ⟨by have := hP p hp; omega,
      Nat.lt_succ_of_le (le_sup (f := id) hp)⟩
  calc
    _ ≤ ∑ p ∈ Ioo 1 (P.sup id + 1), ((p : ℝ) ^ 2)⁻¹ := by
      simp only [one_div]
      exact sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
    _ ≤ 1 := by
      have hh := sum_Ioo_inv_sq_le (α := ℝ) 1 (P.sup id + 1)
      norm_num at hh
      exact hh






end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.PaddingCharacteristic
namespace OAI

/-! The finite characteristic product in the padding argument. The loss
from replacing `p+4` by `p` is bounded explicitly by a convergent square
sum, using only elementary estimates. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical




lemma one_sub_cos_bounds (x : ℝ) : 0 ≤ 1 - Real.cos x ∧ 1 - Real.cos x ≤ 2 := by
  constructor <;> linarith [Real.cos_le_one x, Real.neg_one_le_cos x]

lemma paddingCharacteristicFactor_bounds (p : ℕ) (hp : 2 ≤ p) (t : ℝ) :
    7 / 15 ≤ paddingCharacteristicFactor p t ∧ paddingCharacteristicFactor p t ≤ 1 := by
  have hpr : (2 : ℝ) ≤ p := by exact_mod_cast hp
  have hd : 0 < 5 * ((p : ℝ) + 4) := by positivity
  have hb := one_sub_cos_bounds (t * Real.log p)
  unfold paddingCharacteristicFactor
  constructor
  · have hh : 8 * (1 - Real.cos (t * Real.log p)) / (5 * ((p : ℝ) + 4)) ≤ 8 / 15 := by
      apply (div_le_iff₀ hd).mpr
      nlinarith
    linarith
  · have hh : 0 ≤ 8 * (1 - Real.cos (t * Real.log p)) / (5 * ((p : ℝ) + 4)) :=
      div_nonneg (mul_nonneg (by norm_num) hb.1) hd.le
    linarith

lemma padding_reciprocal_shift (p : ℕ) (hp : 2 ≤ p) (u : ℝ) (hu2 : u ≤ 2) :
    u / p - u / ((p : ℝ) + 4) ≤ 8 / (p : ℝ) ^ 2 := by
  have hpr : (0 : ℝ) < p := by exact_mod_cast (by omega : 0 < p)
  apply (mul_le_mul_iff_of_pos_right (by positivity : 0 < (p : ℝ) ^ 2 * ((p : ℝ) + 4))).mp
  field_simp
  nlinarith [mul_le_mul_of_nonneg_left hu2 hpr.le]


theorem paddingCharacteristic_exp_bound (Q : Finset ℕ) (hQ : ∀ p ∈ Q, 2 ≤ p) (t : ℝ) :
    paddingCharacteristic Q t ≤ Real.exp (64 / 5) *
      Real.exp (-(8 / 5 : ℝ) * paddingOscillation Q t) := by
  have hfirst : paddingCharacteristic Q t ≤
      Real.exp (-(8 / 5 : ℝ) * ∑ p ∈ Q, (1 - Real.cos (t * Real.log p)) / ((p : ℝ) + 4)) := by
    calc
      _ ≤ ∏ p ∈ Q, Real.exp (-(8 / 5 : ℝ) *
          ((1 - Real.cos (t * Real.log p)) / ((p : ℝ) + 4))) := by
        apply Finset.prod_le_prod
        · intro p hp
          linarith [(paddingCharacteristicFactor_bounds p (hQ p hp) t).1]
        · intro p hp
          have hh := Real.add_one_le_exp (-(8 / 5 : ℝ) *
            ((1 - Real.cos (t * Real.log p)) / ((p : ℝ) + 4)))
          unfold paddingCharacteristicFactor
          convert (preTransparency := .instances) hh using 1
          field_simp
          ring
      _ = _ := by rw [← Real.exp_sum]; congr 1; rw [mul_sum]
  have hdiff : paddingOscillation Q t -
      (∑ p ∈ Q, (1 - Real.cos (t * Real.log p)) / ((p : ℝ) + 4)) ≤ 8 := by
    unfold paddingOscillation
    rw [← sum_sub_distrib]
    calc
      _ ≤ ∑ p ∈ Q, 8 / (p : ℝ) ^ 2 := sum_le_sum (fun p hp =>
        padding_reciprocal_shift p (hQ p hp) _
          (one_sub_cos_bounds _).2)
      _ = 8 * ∑ p ∈ Q, 1 / (p : ℝ) ^ 2 := by rw [mul_sum]; apply sum_congr rfl; intros; ring
      _ ≤ 8 := by linarith [reciprocal_square_sum_le_one Q hQ]
  apply hfirst.trans
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  linarith

/-- Once the internally derived oscillatory prime estimate is supplied,
the padding Fourier decay has the exponent `6/5` required for integrability. -/
theorem paddingCharacteristic_power_bound (Q : Finset ℕ) (hQ : ∀ p ∈ Q, 2 ≤ p)
    (L C t : ℝ) (hL : 0 ≤ L)
    (hprime : (3 / 4 : ℝ) * Real.log (1 + L * |t|) - C ≤ paddingOscillation Q t) :
    paddingCharacteristic Q t ≤ Real.exp ((8 / 5 : ℝ) * C + 64 / 5) *
      (1 + L * |t|) ^ (-6 / 5 : ℝ) := by
  apply (paddingCharacteristic_exp_bound Q hQ t).trans
  have hx : 0 < 1 + L * |t| := by positivity
  rw [Real.rpow_def_of_pos hx, ← Real.exp_add, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  linarith

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.PaddingDifferenceLaw
namespace OAI

/-! The actual independent three-point padding difference law and its
characteristic product. At each prime the two nonzero atoms have the
manuscript's exact probability `4/(5(p+4))`. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical



lemma paddingDifferenceStep_zero (p : ℕ) : paddingDifferenceStep p 0 = 0 := by
  unfold paddingDifferenceStep; rw [if_pos rfl]
lemma paddingDifferenceStep_one (p : ℕ) : paddingDifferenceStep p 1 = Real.log p := by
  unfold paddingDifferenceStep; rw [if_neg (by decide), if_pos rfl]
lemma paddingDifferenceStep_two (p : ℕ) : paddingDifferenceStep p 2 = -Real.log p := by
  unfold paddingDifferenceStep; rw [if_neg (by decide), if_neg (by decide)]




lemma paddingStep_characteristic (p : ℕ) (t : ℝ) :
    (∑ e : Fin 3, (paddingDifferenceAtom p e : ℂ) *
      Complex.exp (((t * paddingDifferenceStep p e : ℝ) : ℂ) * Complex.I)) =
      (paddingCharacteristicFactor p t : ℂ) := by
  rw [Fin.sum_univ_three]
  norm_num only [paddingDifferenceAtom_zero, paddingDifferenceAtom_one, paddingDifferenceAtom_two,
    paddingDifferenceStep_zero, paddingDifferenceStep_one, paddingDifferenceStep_two, Fin.isValue,
    Fin.zero_eta, ↓reduceIte, Fin.reduceEq, mul_zero, Complex.ofReal_zero,
    zero_mul, Complex.exp_zero, mul_one]
  rw [show t * -Real.log p = -(t * Real.log p) by ring]
  rw [Complex.exp_ofReal_mul_I, Complex.exp_ofReal_mul_I]
  rw [Real.cos_neg, Real.sin_neg]
  unfold paddingCharacteristicFactor
  push_cast
  ring

/-- The complete finite-law characteristic function is the real,
nonnegative product estimated in `PaddingCharacteristic`. -/
theorem paddingDifference_characteristic (Q : Finset ℕ) (hQ : ∀ p ∈ Q, 2 ≤ p) (t : ℝ) :
    (∑ x : Q → Fin 3, ((paddingDifferenceLaw Q hQ).weight x : ℂ) *
      Complex.exp (((t * paddingDifferenceValue Q x : ℝ) : ℂ) * Complex.I)) =
        (paddingCharacteristic Q t : ℂ) := by
  have hexp (x : Q → Fin 3) :
      Complex.exp (((t * paddingDifferenceValue Q x : ℝ) : ℂ) * Complex.I) =
        ∏ p : Q, Complex.exp (((t * paddingDifferenceStep p (x p) : ℝ) : ℂ) * Complex.I) := by
    unfold paddingDifferenceValue
    rw [mul_sum, Complex.ofReal_sum, sum_mul, Complex.exp_sum]
  simp only [paddingDifferenceLaw, FiniteLaw.independent, paddingStepLaw,
    Complex.ofReal_prod, hexp, ← prod_mul_distrib]
  rw [← Fintype.prod_sum (fun (p : Q) (e : Fin 3) =>
    (paddingDifferenceAtom p e : ℂ) *
      Complex.exp (((t * paddingDifferenceStep p e : ℝ) : ℂ) * Complex.I))]
  simp only [paddingStep_characteristic]
  unfold paddingCharacteristic
  rw [Complex.ofReal_prod]
  exact (prod_subtype (p := fun p : ℕ => p ∈ Q) Q (fun _ => Iff.rfl)
    (fun p => (paddingCharacteristicFactor p t : ℂ))).symm

lemma paddingDifference_cosine (Q : Finset ℕ) (hQ : ∀ p ∈ Q, 2 ≤ p) (t : ℝ) :
    (paddingDifferenceLaw Q hQ).average (fun x => Real.cos (t * paddingDifferenceValue Q x)) =
      paddingCharacteristic Q t := by
  have hh := congrArg Complex.re (paddingDifference_characteristic Q hQ t)
  simpa [FiniteLaw.average, Complex.mul_re, Complex.exp_re] using hh

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.TriangleKernel
namespace OAI

/-! A direct finite-law small-ball inequality using a nonnegative triangular
Fourier kernel. This replaces any need for an external concentration theorem. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.MeasureTheory
open scoped _root_.Classical


lemma triangleKernel_zero : triangleKernel 0 = 1 / 2 := by
  unfold triangleKernel
  simp only [mul_zero, Real.cos_zero, mul_one]
  rw [intervalIntegral.integral_sub (f := fun _ : ℝ => 1) (g := fun t : ℝ => t)
    intervalIntegrable_const (continuous_id.intervalIntegrable _ _)]
  norm_num [integral_id]

lemma triangleKernel_eq {x : ℝ} (hx : x ≠ 0) : triangleKernel x = (1 - Real.cos x) / x ^ 2 := by
  let F : ℝ → ℝ := fun t => (1 - t) * Real.sin (t * x) / x - Real.cos (t * x) / x ^ 2
  have hF (t : ℝ) : HasDerivAt F ((1 - t) * Real.cos (t * x)) t := by
    have hs := (Real.hasDerivAt_sin (t * x)).comp t ((hasDerivAt_id t).mul_const x)
    have hc := (Real.hasDerivAt_cos (t * x)).comp t ((hasDerivAt_id t).mul_const x)
    have hh := ((((hasDerivAt_id t).const_sub 1).mul hs).div_const x).sub (hc.div_const (x ^ 2))
    convert (preTransparency := .instances) hh using 1
    · rfl
    · simp only [Function.comp_apply, id_eq]
      field_simp
      ring
  have hh := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t (_ : t ∈ Set.uIcc (0 : ℝ) 1) => hF t)
    ((by fun_prop : Continuous (fun t : ℝ => (1 - t) * Real.cos (t * x))).intervalIntegrable _ _)
  change triangleKernel x = _ at hh
  simp [F] at hh
  rw [hh]
  ring

lemma triangleKernel_nonneg (x : ℝ) : 0 ≤ triangleKernel x := by
  by_cases hx : x = 0
  · rw [hx, triangleKernel_zero]; norm_num
  · rw [triangleKernel_eq hx]
    exact div_nonneg (sub_nonneg.mpr (Real.cos_le_one x)) (sq_nonneg x)

lemma triangleKernel_unit_lower (x : ℝ) (hx : |x| ≤ 1) : 1 / 4 ≤ triangleKernel x := by
  have hmono : (∫ t in (0 : ℝ)..1, (1 - t) / 2) ≤ triangleKernel x := by
    apply intervalIntegral.integral_mono_on (by norm_num)
      ((by fun_prop : Continuous (fun t : ℝ => (1 - t) / 2)).intervalIntegrable _ _)
      ((by fun_prop : Continuous (fun t : ℝ => (1 - t) * Real.cos (t * x))).intervalIntegrable _ _)
    intro t ht
    have htx : |t * x| ≤ 1 := by
      rw [abs_mul, abs_of_nonneg ht.1]
      simpa using mul_le_mul ht.2 hx (abs_nonneg x) (by norm_num : (0 : ℝ) ≤ 1)
    have htx' := abs_le.mp htx
    have hsq : (t * x) ^ 2 ≤ 1 := by
      nlinarith [mul_nonneg (by linarith : 0 ≤ 1 - t * x) (by linarith : 0 ≤ 1 + t * x)]
    have hcos : 1 / 2 ≤ Real.cos (t * x) := by
      have hh := Real.one_sub_sq_div_two_le_cos (x := t * x)
      linarith
    have hh := mul_le_mul_of_nonneg_left hcos (sub_nonneg.mpr ht.2)
    nlinarith
  have hi : (∫ t in (0 : ℝ)..1, (1 - t) / 2) = 1 / 4 := by
    rw [intervalIntegral.integral_div, intervalIntegral.integral_sub
      (f := fun _ : ℝ => 1) (g := fun t : ℝ => t)
      intervalIntegrable_const (continuous_id.intervalIntegrable _ _)]
    norm_num [integral_id]
  rwa [hi] at hmono

lemma FiniteLaw.average_triangleKernel {Ω : Type*} [Fintype Ω]
    (μ : FiniteLaw Ω) (Z : Ω → ℝ) :
    μ.average (fun x => triangleKernel (Z x)) =
      ∫ t in (0 : ℝ)..1, (1 - t) * μ.average (fun x => Real.cos (t * Z x)) := by
  unfold FiniteLaw.average triangleKernel
  calc
    _ = ∑ x, ∫ t in (0 : ℝ)..1, μ.weight x * ((1 - t) * Real.cos (t * Z x)) := by
      apply sum_congr rfl
      intro x _
      rw [intervalIntegral.integral_const_mul]
    _ = ∫ t in (0 : ℝ)..1, ∑ x, μ.weight x * ((1 - t) * Real.cos (t * Z x)) := by
      exact (intervalIntegral.integral_finsetSum (fun x _ =>
        (by fun_prop : Continuous (fun t : ℝ => μ.weight x * ((1 - t) * Real.cos (t * Z x)))).intervalIntegrable _ _)).symm
    _ = _ := by
      apply intervalIntegral.integral_congr
      intro t _
      change (∑ x, μ.weight x * ((1 - t) * Real.cos (t * Z x))) =
        (1 - t) * ∑ x, μ.weight x * Real.cos (t * Z x)
      rw [mul_sum]
      apply sum_congr rfl
      intro x _
      ring

/-- The exact finite-law small-ball reduction. The characteristic function
can now be bounded inside a compact ordinary integral. -/
theorem FiniteLaw.unit_small_ball_le {Ω : Type*} [Fintype Ω]
    (μ : FiniteLaw Ω) (Z : Ω → ℝ) :
    μ.probability (fun x => |Z x| ≤ 1) ≤
      4 * (∫ t in (0 : ℝ)..1, (1 - t) * μ.average (fun x => Real.cos (t * Z x))) := by
  calc
    _ ≤ μ.average (fun x => triangleKernel (Z x) * 4) := by
      apply μ.average_mono
      intro x
      by_cases hx : |Z x| ≤ 1
      · simp only [hx, ↓reduceIte]
        linarith [triangleKernel_unit_lower (Z x) hx]
      · simp only [hx, ↓reduceIte]
        exact mul_nonneg (triangleKernel_nonneg _) (by norm_num)
    _ = _ := by rw [μ.average_mul_const, μ.average_triangleKernel]; ring

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.PowerSmallBall
namespace OAI

/-! Integrating the `6/5` Fourier decay gives the required reciprocal-scale
small-ball bound, directly for a finite probability law. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.MeasureTheory
open scoped _root_.Classical

lemma padding_power_integral (L : ℝ) (hL : 0 < L) :
    (∫ t in (0 : ℝ)..1, (1 + L * t) ^ (-6 / 5 : ℝ)) ≤ 5 / L := by
  have hs := intervalIntegral.integral_comp_mul_add
    (a := (0 : ℝ)) (b := 1) (fun x : ℝ => x ^ (-6 / 5 : ℝ)) hL.ne' 1
  have he := integral_rpow (a := (1 : ℝ)) (b := L + 1) (r := (-6 / 5 : ℝ))
    (Or.inr ⟨by norm_num, by
      rw [Set.uIcc_of_le (by linarith : (1 : ℝ) ≤ L + 1)]
      simp only [Set.mem_Icc, not_and_or]
      left
      norm_num⟩)
  have he' : (∫ x in (1 : ℝ)..L + 1, x ^ (-6 / 5 : ℝ)) =
      5 * (1 - (L + 1) ^ (-1 / 5 : ℝ)) := by
    rw [he]
    norm_num
    ring
  have hi : (∫ t in (0 : ℝ)..1, (1 + L * t) ^ (-6 / 5 : ℝ)) =
      L⁻¹ * (5 * (1 - (L + 1) ^ (-1 / 5 : ℝ))) := by
    have hs' : (∫ t in (0 : ℝ)..1, (L * t + 1) ^ (-6 / 5 : ℝ)) =
        L⁻¹ * (∫ x in (1 : ℝ)..L + 1, x ^ (-6 / 5 : ℝ)) := by
      simpa only [mul_zero, zero_add, mul_one, smul_eq_mul] using hs
    rw [he'] at hs'
    simpa only [add_comm] using hs'
  have hp : 0 ≤ (L + 1) ^ (-1 / 5 : ℝ) := Real.rpow_nonneg (by linarith) _
  rw [hi]
  calc
    _ ≤ L⁻¹ * 5 := mul_le_mul_of_nonneg_left (by linarith) (inv_nonneg.mpr hL.le)
    _ = _ := by ring

theorem FiniteLaw.unit_small_ball_of_decay {Ω : Type*} [Fintype Ω]
    (μ : FiniteLaw Ω) (Z : Ω → ℝ) (L C : ℝ) (hL : 0 < L) (hC : 0 ≤ C)
    (hchar : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      μ.average (fun x => Real.cos (t * Z x)) ≤ C * (1 + L * t) ^ (-6 / 5 : ℝ)) :
    μ.probability (fun x => |Z x| ≤ 1) ≤ 20 * C / L := by
  have hp (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) : 0 < 1 + L * t := by
    have ht0 := ht.1
    positivity
  have hg : IntervalIntegrable (fun t : ℝ => C * (1 + L * t) ^ (-6 / 5 : ℝ)) volume 0 1 := by
    apply ContinuousOn.intervalIntegrable_of_Icc (h := by norm_num)
    intro t ht
    have hpt := hp t ht
    have hc : ContinuousAt (fun t : ℝ => 1 + L * t) t := by fun_prop
    exact ((hc.rpow_const (Or.inl hpt.ne')).const_mul C).continuousWithinAt
  have hf : IntervalIntegrable
      (fun t : ℝ => (1 - t) * μ.average (fun x => Real.cos (t * Z x))) volume 0 1 := by
    unfold FiniteLaw.average
    exact (by fun_prop : Continuous
      (fun t : ℝ => (1 - t) * ∑ x, μ.weight x * Real.cos (t * Z x))).intervalIntegrable _ _
  have hm : (∫ t in (0 : ℝ)..1, (1 - t) * μ.average (fun x => Real.cos (t * Z x))) ≤
      C * (5 / L) := by
    calc
      _ ≤ ∫ t in (0 : ℝ)..1, C * (1 + L * t) ^ (-6 / 5 : ℝ) := by
        apply intervalIntegral.integral_mono_on (by norm_num) hf hg
        intro t ht
        have hh := mul_le_mul_of_nonneg_left (hchar t ht) (sub_nonneg.mpr ht.2)
        have hn : 0 ≤ C * (1 + L * t) ^ (-6 / 5 : ℝ) :=
          mul_nonneg hC (Real.rpow_nonneg (hp t ht).le _)
        nlinarith [mul_nonneg ht.1 hn]
      _ = C * (∫ t in (0 : ℝ)..1, (1 + L * t) ^ (-6 / 5 : ℝ)) :=
        intervalIntegral.integral_const_mul _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left (padding_power_integral L hL) hC
  apply (μ.unit_small_ball_le Z).trans
  calc
    _ ≤ 4 * (C * (5 / L)) := mul_le_mul_of_nonneg_left hm (by norm_num)
    _ = _ := by ring

theorem paddingDifference_small_ball (Q : Finset ℕ) (hQ : ∀ p ∈ Q, 2 ≤ p)
    (L C : ℝ) (hL : 0 < L)
    (hprime : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      (3 / 4 : ℝ) * Real.log (1 + L * |t|) - C ≤ paddingOscillation Q t) :
    (paddingDifferenceLaw Q hQ).probability (fun x => |paddingDifferenceValue Q x| ≤ 1) ≤
      20 * Real.exp ((8 / 5 : ℝ) * C + 64 / 5) / L := by
  apply FiniteLaw.unit_small_ball_of_decay _ _ L _ hL (Real.exp_pos _).le
  intro t ht
  rw [paddingDifference_cosine]
  have hh := paddingCharacteristic_power_bound Q hQ L C t hL.le (hprime t ht)
  simpa only [abs_of_nonneg ht.1] using hh

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Fourier.ModFivePrimes
namespace OAI

/-! The fixed modulus-five prime-number input used by the manuscript.

Published source: D. Koukoulopoulos, *The Distribution of Prime Numbers*,
AMS, 2019, Theorem 12.1 (Siegel--Walfisz), with modulus 5 fixed. That theorem
is stated for the prime-counting function. `ModFiveThetaInput` is its standard
partial-summation consequence for the logarithmically weighted prime count,
specialized to the two selections needed here. The complementary selection
includes the single prime 5, which changes the error by a bounded amount.
Source: https://dms.umontreal.ca/~koukoulo/documents/publications/primes.pdf

The estimate includes every prime in the selected classes. Removing a finite
exceptional prime set contributes an explicit finite-deletion correction.
-/

namespace TwoPointCorrelations

open _root_.Finset _root_.Filter
open scoped _root_.Classical _root_.Topology









lemma modFiveTheta_eq_sum (one : Bool) (x : ℝ) :
    modFiveTheta one x = ∑ p ∈ modFivePrimesUpTo one x, Real.log p := by
  simp [modFiveTheta, modFivePrimesUpTo, modFiveLogWeight, sum_filter]





lemma log_nat_nonneg (p : ℕ) : 0 ≤ Real.log (p : ℝ) := by
  by_cases hp : p = 0
  · simp [hp]
  · exact Real.log_nonneg (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hp)

/-- The entire cost of removing a finite exceptional prime set is explicit. -/
lemma deletedModFiveTheta_error (E : Finset ℕ) (one : Bool) (x : ℝ) :
    |deletedModFiveTheta E one x - modFiveTheta one x| ≤
      ∑ p ∈ E, Real.log p := by
  rw [modFiveTheta_eq_sum]
  have he : deletedModFiveTheta E one x -
      (∑ p ∈ modFivePrimesUpTo one x, Real.log p) =
      -(∑ p ∈ modFivePrimesUpTo one x ∩ E, Real.log p) := by
    unfold deletedModFiveTheta deletedModFivePrimes
    have hs := sum_sdiff (f := fun p : ℕ => Real.log (p : ℝ))
      (inter_subset_left : modFivePrimesUpTo one x ∩ E ⊆ modFivePrimesUpTo one x)
    rw [sdiff_inter_self_left] at hs
    linarith
  rw [he, abs_neg, abs_of_nonneg (sum_nonneg (fun p _ => log_nat_nonneg p))]
  exact sum_le_sum_of_subset_of_nonneg inter_subset_right (fun p _ _ => log_nat_nonneg p)


end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.PrimePartialSummation
namespace OAI

/-! Exact partial summation, with the prime-count error retained inside the
integral. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.MeasureTheory
open scoped _root_.Classical


theorem centered_partial_summation (c : ℕ → ℝ) (α a b : ℝ) (ha : 0 ≤ a)
    (hab : a ≤ b) (f : ℝ → ℝ)
    (hf : ∀ x ∈ Set.Icc a b, DifferentiableAt ℝ f x)
    (hdf : ContinuousOn (deriv f) (Set.Icc a b)) :
    (∑ n ∈ Ioc ⌊a⌋₊ ⌊b⌋₊, f n * c n) - α * (∫ t in a..b, f t) =
      f b * (partialCoefficientSum c b - α * b) -
      f a * (partialCoefficientSum c a - α * a) -
      ∫ t in a..b, deriv f t * (partialCoefficientSum c t - α * t) := by
  have hfc : ContinuousOn f (Set.Icc a b) :=
    fun x hx => (hf x hx).continuousAt.continuousWithinAt
  have hfi : IntervalIntegrable f volume a b := hfc.intervalIntegrable_of_Icc hab
  have hdfi : IntervalIntegrable (deriv f) volume a b :=
    hdf.intervalIntegrable_of_Icc hab
  have hdmain : IntervalIntegrable (fun t => deriv f t * t) volume a b :=
    hdfi.mul_continuousOn continuous_id.continuousOn
  have hsum : IntervalIntegrable
      (fun t => deriv f t * partialCoefficientSum c t) volume a b := by
    apply (intervalIntegrable_iff_integrableOn_Icc_of_le hab).mpr
    exact integrableOn_mul_sum_Icc c ha
      (hdf.integrableOn_Icc)
  have hAbel := sum_mul_eq_sub_sub_integral_mul c ha hab hf hdf.integrableOn_Icc
  rw [← intervalIntegral.integral_of_le hab] at hAbel
  change (∑ n ∈ Ioc ⌊a⌋₊ ⌊b⌋₊, f n * c n) =
    f b * partialCoefficientSum c b - f a * partialCoefficientSum c a -
      ∫ t in a..b, deriv f t * partialCoefficientSum c t at hAbel
  have hparts := intervalIntegral.integral_deriv_mul_eq_sub
    (fun x hx => (hf x (by simpa [Set.uIcc_of_le hab] using hx)).hasDerivAt)
    (fun x (_ : x ∈ Set.uIcc a b) => hasDerivAt_id x) hdfi intervalIntegrable_const
  simp only [id_eq] at hparts
  have hsplit : (∫ t in a..b, deriv f t * t + f t * 1) =
      (∫ t in a..b, deriv f t * t) + ∫ t in a..b, f t := by
    simp only [mul_one]
    exact intervalIntegral.integral_add hdmain hfi
  rw [hsplit] at hparts
  have herr : (∫ t in a..b, deriv f t * (partialCoefficientSum c t - α * t)) =
      (∫ t in a..b, deriv f t * partialCoefficientSum c t) -
        α * (∫ t in a..b, deriv f t * t) := by
    simp only [mul_sub, show ∀ t, deriv f t * (α * t) = α * (deriv f t * t) by
      intro t; ring]
    rw [intervalIntegral.integral_sub hsum (hdmain.const_mul α),
      intervalIntegral.integral_const_mul]
  rw [herr, hAbel]
  linear_combination -α * hparts


end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.ThetaLogError
namespace OAI

/-! An integrable logarithmic error bound obtained from the stated exponential
prime-number error. It also pays exactly for finite exceptional prime sets. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

lemma exp_neg_sqrt_log_le (c x : ℝ) (hc : 0 < c) (hx : 1 < x) :
    Real.exp (-c * Real.sqrt (Real.log x)) ≤ 24 / (c ^ 4 * Real.log x ^ 2) := by
  have hl : 0 < Real.log x := Real.log_pos hx
  have hsq := Real.sq_sqrt hl.le
  have hpow : (c * Real.sqrt (Real.log x)) ^ 4 = c ^ 4 * Real.log x ^ 2 := by
    calc
      _ = c ^ 4 * ((Real.sqrt (Real.log x)) ^ 2) ^ 2 := by ring
      _ = _ := by rw [hsq]
  have he := Real.pow_div_factorial_le_exp (c * Real.sqrt (Real.log x))
    (mul_nonneg hc.le (Real.sqrt_nonneg (Real.log x))) 4
  norm_num at he
  rw [hpow] at he
  have hmul := mul_le_mul_of_nonneg_right he
    (Real.exp_pos (-c * Real.sqrt (Real.log x))).le
  have hexp : Real.exp (c * Real.sqrt (Real.log x)) *
      Real.exp (-c * Real.sqrt (Real.log x)) = 1 := by
    rw [← Real.exp_add]
    ring_nf
    exact Real.exp_zero
  rw [hexp] at hmul
  apply (le_div_iff₀ (by positivity : 0 < c ^ 4 * Real.log x ^ 2)).mpr
  nlinarith [hmul]

lemma log_sq_le_two_mul (x : ℝ) (hx : 1 ≤ x) : Real.log x ^ 2 ≤ 2 * x := by
  have hh := Real.pow_div_factorial_le_exp (Real.log x) (Real.log_nonneg hx) 2
  norm_num at hh
  rw [Real.exp_log (zero_lt_one.trans_le hx)] at hh
  linarith

/-- A single constant controls the logarithmic PNT error for both residue
selections and every real endpoint at least two. -/
theorem ModFiveThetaInput.log_error (hP : ModFiveThetaInput) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (one : Bool) (x : ℝ), 2 ≤ x →
      |modFiveTheta one x - modFiveDensity one * x| ≤ K * x / Real.log x ^ 2 := by
  obtain ⟨c, C, hc, hC, h⟩ := hP
  refine ⟨24 * C / c ^ 4, by positivity, fun one x hx => ?_⟩
  apply (h one x hx).trans
  have hh := mul_le_mul_of_nonneg_left (exp_neg_sqrt_log_le c x hc (by linarith))
    (mul_nonneg hC (by linarith : 0 ≤ x))
  convert (preTransparency := .instances) hh using 1
  ring

theorem ModFiveThetaInput.deleted_log_error (hP : ModFiveThetaInput) (E : Finset ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (one : Bool) (x : ℝ), 2 ≤ x →
      |deletedModFiveTheta E one x - modFiveDensity one * x| ≤
        K * x / Real.log x ^ 2 := by
  obtain ⟨K, hK, h⟩ := hP.log_error
  let D : ℝ := ∑ p ∈ E, Real.log p
  have hD : 0 ≤ D := sum_nonneg (fun p _ => log_nat_nonneg p)
  refine ⟨K + 2 * D, by positivity, fun one x hx => ?_⟩
  have hl : 0 < Real.log x := Real.log_pos (by linarith)
  have hd : D ≤ 2 * D * x / Real.log x ^ 2 := by
    apply (le_div_iff₀ (sq_pos_of_pos hl)).mpr
    have hh := mul_le_mul_of_nonneg_left (log_sq_le_two_mul x (by linarith)) hD
    nlinarith [hh]
  calc
    _ ≤ |modFiveTheta one x - modFiveDensity one * x| + D := by
      calc
        _ = |(modFiveTheta one x - modFiveDensity one * x) +
            (deletedModFiveTheta E one x - modFiveTheta one x)| := by congr 1; ring
        _ ≤ _ := abs_add_le _ _
        _ ≤ _ := add_le_add (le_refl _) (deletedModFiveTheta_error E one x)
    _ ≤ K * x / Real.log x ^ 2 + 2 * D * x / Real.log x ^ 2 :=
      add_le_add (h one x hx) hd
    _ = _ := by ring

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.ReciprocalPrimeBands
namespace OAI

/-! Quantitative reciprocal-prime bands from the actual theta error.
Partial summation gives the reciprocal-prime estimates. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.MeasureTheory
open scoped _root_.Classical


lemma reciprocalLog_hasDerivAt {x : ℝ} (hx : 1 < x) :
    HasDerivAt reciprocalLog
      (-(Real.log x + 1) / (x ^ 2 * Real.log x ^ 2)) x := by
  have hx0 : x ≠ 0 := (zero_lt_one.trans hx).ne'
  have hl0 : Real.log x ≠ 0 := (Real.log_pos hx).ne'
  have hh := (hasDerivAt_inv hx0).div (Real.hasDerivAt_log hx0) hl0
  convert (preTransparency := .instances) hh using 1
  · rfl
  · field_simp
    ring




end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.WeightedThetaError
namespace OAI

/-! The bounded-error form of partial summation needed for the padding
oscillation. The constants retain the uniform derivative bounds explicitly. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.MeasureTheory
open scoped _root_.Classical

theorem weighted_theta_error (c : ℕ → ℝ) (α K F D a b : ℝ)
    (hK : 0 ≤ K) (hF : 0 ≤ F) (hD : 0 ≤ D)
    (ha : Real.exp 1 ≤ a) (hab : a ≤ b) (f : ℝ → ℝ)
    (hf : ∀ x ∈ Set.Icc a b, DifferentiableAt ℝ f x)
    (hdf : ContinuousOn (deriv f) (Set.Icc a b))
    (hsize : ∀ x ∈ Set.Icc a b, |f x| ≤ F / x)
    (hdsize : ∀ x ∈ Set.Icc a b, |deriv f x| ≤ D / x ^ 2)
    (hE : ∀ x ∈ Set.Icc a b,
      |partialCoefficientSum c x - α * x| ≤ K * x / Real.log x ^ 2) :
    |(∑ n ∈ Ioc ⌊a⌋₊ ⌊b⌋₊, f n * c n) - α * (∫ x in a..b, f x)| ≤
      (2 * F + D) * K / Real.log a := by
  have ha1 : 1 < a := (Real.one_lt_exp_iff.mpr (by norm_num : (0 : ℝ) < 1)).trans_le ha
  have ha0 : 0 < a := zero_lt_one.trans ha1
  have hb1 : 1 < b := ha1.trans_le hab
  have hla : 1 ≤ Real.log a := by simpa using Real.log_le_log (Real.exp_pos 1) ha
  have hlap : 0 < Real.log a := Real.log_pos ha1
  have hxp (x : ℝ) (hx : x ∈ Set.Icc a b) : 0 < x := ha0.trans_le hx.1
  have hlx (x : ℝ) (hx : x ∈ Set.Icc a b) : 1 ≤ Real.log x :=
    hla.trans (Real.log_le_log ha0 hx.1)
  have hln (x : ℝ) (hx : x ∈ Set.Icc a b) : Real.log x ≠ 0 :=
    (zero_lt_one.trans_le (hlx x hx)).ne'
  have hbound (x : ℝ) (hx : x ∈ Set.Icc a b) :
      |f x * (partialCoefficientSum c x - α * x)| ≤ F * K / Real.log a := by
    have hx0 := hxp x hx
    have hl0 := hln x hx
    rw [abs_mul]
    calc
      _ ≤ (F / x) * (K * x / Real.log x ^ 2) :=
        mul_le_mul (hsize x hx) (hE x hx) (abs_nonneg _) (by positivity)
      _ = F * K / Real.log x ^ 2 := by field_simp
      _ ≤ F * K / Real.log a := by
        apply div_le_div_of_nonneg_left (mul_nonneg hF hK) hlap
        have hm := Real.log_le_log ha0 hx.1
        nlinarith [sq_nonneg (Real.log x - 1), hlx x hx]
  have hderror (x : ℝ) (hx : x ∈ Set.Icc a b) :
      |deriv f x * (partialCoefficientSum c x - α * x)| ≤
        (D * K) * (x⁻¹ / Real.log x ^ 2) := by
    have hx0 := hxp x hx
    have hl0 := hln x hx
    rw [abs_mul]
    calc
      _ ≤ (D / x ^ 2) * (K * x / Real.log x ^ 2) :=
        mul_le_mul (hdsize x hx) (hE x hx) (abs_nonneg _) (by positivity)
      _ = _ := by field_simp
  have hclog : ContinuousOn Real.log (Set.Icc a b) :=
    fun x hx => (Real.continuousAt_log (hxp x hx).ne').continuousWithinAt
  have hg : IntervalIntegrable (fun x : ℝ => (D * K) * (x⁻¹ / Real.log x ^ 2)) volume a b := by
    apply ContinuousOn.intervalIntegrable_of_Icc (h := hab)
    exact ((continuousOn_id.inv₀ (fun x hx => (hxp x hx).ne')).div
      (hclog.pow 2) (fun x hx => pow_ne_zero 2 (hln x hx))).const_mul (D * K)
  have hi : |∫ x in a..b, deriv f x * (partialCoefficientSum c x - α * x)| ≤
      D * K / Real.log a := by
    have hh := intervalIntegral.norm_integral_le_of_norm_le hab
      (Filter.Eventually.of_forall (fun x hx => by
        rw [Real.norm_eq_abs]
        exact hderror x ⟨hx.1.le, hx.2⟩)) hg
    rw [Real.norm_eq_abs, intervalIntegral.integral_const_mul,
      integral_inv_div_log_sq ha1 hb1] at hh
    apply hh.trans
    have hbnonneg : 0 ≤ (Real.log b)⁻¹ := inv_nonneg.mpr (Real.log_pos hb1).le
    simp only [div_eq_mul_inv]
    nlinarith [mul_nonneg (mul_nonneg hD hK) hbnonneg]
  rw [centered_partial_summation c α a b ha0.le hab f hf hdf]
  calc
    _ ≤ |f b * (partialCoefficientSum c b - α * b)| +
        |f a * (partialCoefficientSum c a - α * a)| +
        |∫ t in a..b, deriv f t * (partialCoefficientSum c t - α * t)| :=
      (abs_sub _ _).trans (add_le_add (abs_sub _ _) (le_refl _))
    _ ≤ F * K / Real.log a + F * K / Real.log a + D * K / Real.log a :=
      add_le_add (add_le_add (hbound b ⟨hab, le_rfl⟩) (hbound a ⟨le_rfl, hab⟩)) hi
    _ = _ := by ring

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.OscillatoryThetaError
namespace OAI

/-! Uniform partial summation for `(1-cos(t log p))/p`, with `|t|≤2`.
The oscillatory prime estimate is deduced from the theta error. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.MeasureTheory
open scoped _root_.Classical


lemma reciprocalLog_size {x : ℝ} (hx : 1 < x) (hl : 1 ≤ Real.log x) :
    |reciprocalLog x| ≤ 1 / x := by
  have hx0 : 0 < x := zero_lt_one.trans hx
  have hl0 : 0 < Real.log x := zero_lt_one.trans_le hl
  unfold reciprocalLog
  rw [abs_of_nonneg (by positivity)]
  apply (div_le_iff₀ hl0).mpr
  have hh := mul_le_mul_of_nonneg_left hl (inv_nonneg.mpr hx0.le)
  simpa only [mul_one, one_div] using hh

lemma reciprocalLog_deriv_size {x : ℝ} (hx : 1 < x) (hl : 1 ≤ Real.log x) :
    |deriv reciprocalLog x| ≤ 2 / x ^ 2 := by
  have hx0 : 0 < x := zero_lt_one.trans hx
  have hl0 : 0 < Real.log x := zero_lt_one.trans_le hl
  rw [(reciprocalLog_hasDerivAt hx).deriv, abs_div, abs_neg,
    abs_of_pos (by positivity : 0 < Real.log x + 1),
    abs_of_pos (by positivity : 0 < x ^ 2 * Real.log x ^ 2)]
  calc
    _ ≤ (2 * Real.log x ^ 2) / (x ^ 2 * Real.log x ^ 2) := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      nlinarith [sq_nonneg (Real.log x - 1)]
    _ = _ := by field_simp

lemma oscillatoryReciprocalLog_hasDerivAt (t x : ℝ) (hx : 1 < x) :
    HasDerivAt (oscillatoryReciprocalLog t)
      ((t * Real.sin (t * Real.log x) / x) * reciprocalLog x +
        (1 - Real.cos (t * Real.log x)) * deriv reciprocalLog x) x := by
  have hx0 : x ≠ 0 := (zero_lt_one.trans hx).ne'
  have hg := ((Real.hasDerivAt_cos (t * Real.log x)).comp x
    ((Real.hasDerivAt_log hx0).const_mul t)).const_sub 1
  have hh := hg.mul (reciprocalLog_hasDerivAt hx)
  convert (preTransparency := .instances) hh using 1
  · rfl
  · rw [(reciprocalLog_hasDerivAt hx).deriv]
    simp only [div_eq_mul_inv, Function.comp_def]
    ring

lemma oscillatoryReciprocalLog_bounds (t x : ℝ) (ht : |t| ≤ 2)
    (hx : 1 < x) (hl : 1 ≤ Real.log x) :
    |oscillatoryReciprocalLog t x| ≤ 2 / x ∧
      |deriv (oscillatoryReciprocalLog t) x| ≤ 6 / x ^ 2 := by
  have hx0 : 0 < x := zero_lt_one.trans hx
  have hg : |1 - Real.cos (t * Real.log x)| ≤ 2 :=
    (abs_of_nonneg (one_sub_cos_bounds _).1).trans_le (one_sub_cos_bounds _).2
  have hs : |t * Real.sin (t * Real.log x) / x| ≤ 2 / x := by
    rw [abs_div, abs_mul, abs_of_pos hx0]
    apply div_le_div_of_nonneg_right _ hx0.le
    exact (mul_le_mul ht (Real.abs_sin_le_one _) (abs_nonneg _) (by norm_num)).trans_eq (mul_one 2)
  have hrec := reciprocalLog_size hx hl
  have hdrec := reciprocalLog_deriv_size hx hl
  constructor
  · unfold oscillatoryReciprocalLog
    rw [abs_mul]
    calc
      _ ≤ 2 * (1 / x) := mul_le_mul hg hrec (abs_nonneg _) (by norm_num)
      _ = _ := by ring
  · rw [(oscillatoryReciprocalLog_hasDerivAt t x hx).deriv]
    apply (abs_add_le _ _).trans
    rw [abs_mul, abs_mul]
    calc
      _ ≤ (2 / x) * (1 / x) + 2 * (2 / x ^ 2) :=
        add_le_add (mul_le_mul hs hrec (abs_nonneg _) (by positivity))
          (mul_le_mul hg hdrec (abs_nonneg _) (by norm_num))
      _ = _ := by field_simp; ring

theorem oscillatory_theta_error (c : ℕ → ℝ) (α K a b t : ℝ)
    (hK : 0 ≤ K) (ha : Real.exp 1 ≤ a) (hab : a ≤ b) (ht : |t| ≤ 2)
    (hE : ∀ x ∈ Set.Icc a b,
      |partialCoefficientSum c x - α * x| ≤ K * x / Real.log x ^ 2) :
    |(∑ n ∈ Ioc ⌊a⌋₊ ⌊b⌋₊, oscillatoryReciprocalLog t n * c n) -
      α * (∫ x in a..b, oscillatoryReciprocalLog t x)| ≤ 10 * K / Real.log a := by
  have ha1 : 1 < a := (Real.one_lt_exp_iff.mpr (by norm_num : (0 : ℝ) < 1)).trans_le ha
  have hx1 (x : ℝ) (hx : x ∈ Set.Icc a b) : 1 < x := ha1.trans_le hx.1
  have hl (x : ℝ) (hx : x ∈ Set.Icc a b) : 1 ≤ Real.log x := by
    calc
      1 = Real.log (Real.exp 1) := (Real.log_exp 1).symm
      _ ≤ _ := Real.log_le_log (Real.exp_pos _) (ha.trans hx.1)
  suffices hh : |(∑ n ∈ Ioc ⌊a⌋₊ ⌊b⌋₊, oscillatoryReciprocalLog t n * c n) -
      α * (∫ x in a..b, oscillatoryReciprocalLog t x)| ≤ (2 * 2 + 6) * K / Real.log a by
    norm_num at hh
    exact hh
  apply weighted_theta_error c α K 2 6 a b hK (by norm_num) (by norm_num) ha hab
  · intro x hx
    exact (oscillatoryReciprocalLog_hasDerivAt t x (hx1 x hx)).differentiableAt
  · intro x hx
    have hxn : x ≠ 0 := (zero_lt_one.trans (hx1 x hx)).ne'
    have hln : Real.log x ≠ 0 := (Real.log_pos (hx1 x hx)).ne'
    have hc : ContDiffAt ℝ 2 (oscillatoryReciprocalLog t) x := by
      unfold oscillatoryReciprocalLog reciprocalLog
      fun_prop (disch := assumption)
    exact (hc.derivWithin (m := 0) (by norm_num)).continuousAt.continuousWithinAt
  · exact fun x hx => (oscillatoryReciprocalLog_bounds t x ht (hx1 x hx) (hl x hx)).1
  · exact fun x hx => (oscillatoryReciprocalLog_bounds t x ht (hx1 x hx) (hl x hx)).2
  · exact hE

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.CosineLogIntegral
namespace OAI

/-! The elementary logarithmic oscillatory integral behind the padding
prime estimate. All constants are absolute. -/

namespace TwoPointCorrelations

open _root_.MeasureTheory
open scoped _root_.Classical

lemma integral_inverse_square (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) :
    (∫ y in a..b, (y ^ 2)⁻¹) = a⁻¹ - b⁻¹ := by
  have hderiv : ∀ y ∈ Set.uIcc a b, HasDerivAt (fun y : ℝ => -y⁻¹) ((y ^ 2)⁻¹) y := by
    intro y hy
    have hy' : y ∈ Set.Icc a b := by simpa only [Set.uIcc_of_le hab] using hy
    have hy0 : y ≠ 0 := (ha.trans_le hy'.1).ne'
    convert! (preTransparency := .instances) (hasDerivAt_inv hy0).neg using 1
    simp
  have hc : ContinuousOn (fun y : ℝ => (y ^ 2)⁻¹) (Set.Icc a b) := by
    intro y hy
    have hy0 : y ≠ 0 := (ha.trans_le hy.1).ne'
    exact ((continuousAt_id.pow 2).inv₀ (pow_ne_zero 2 hy0)).continuousWithinAt
  have hh := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    (hc.intervalIntegrable_of_Icc hab)
  linarith

lemma cosine_log_tail (T a b : ℝ) (hT : 0 < T) (ha : 0 < a) (hab : a ≤ b)
    (hTa : 1 ≤ T * a) :
    |∫ y in a..b, Real.cos (T * y) / y| ≤ 3 := by
  have hb : 0 < b := ha.trans_le hab
  have hpos (y : ℝ) (hy : y ∈ Set.Icc a b) : 0 < y := ha.trans_le hy.1
  have hu (y : ℝ) : HasDerivAt (fun y => Real.sin (T * y) / T) (Real.cos (T * y)) y := by
    have hh := ((Real.hasDerivAt_sin (T * y)).comp y ((hasDerivAt_id y).const_mul T)).div_const T
    convert (preTransparency := .instances) hh using 1
    · simp only [Function.comp_def, mul_comm T]
    · field_simp
  have hv (y : ℝ) (hy : y ∈ Set.uIcc a b) :
      HasDerivAt (fun y : ℝ => y⁻¹) (-(y ^ 2)⁻¹) y := by
    apply hasDerivAt_inv
    have hy' : y ∈ Set.Icc a b := by simpa only [Set.uIcc_of_le hab] using hy
    exact (ha.trans_le hy'.1).ne'
  have hcos : IntervalIntegrable (fun y => Real.cos (T * y) / y) volume a b := by
    apply ContinuousOn.intervalIntegrable_of_Icc (h := hab)
    intro y hy
    exact (by fun_prop (disch := exact (hpos y hy).ne') :
      ContinuousAt (fun y => Real.cos (T * y) / y) y).continuousWithinAt
  have htail : IntervalIntegrable (fun y => Real.sin (T * y) / (T * y ^ 2)) volume a b := by
    apply ContinuousOn.intervalIntegrable_of_Icc (h := hab)
    intro y hy
    have hy0 := (hpos y hy).ne'
    exact (by fun_prop (disch := positivity) :
      ContinuousAt (fun y => Real.sin (T * y) / (T * y ^ 2)) y).continuousWithinAt
  have hvin : IntervalIntegrable (fun y : ℝ => -(y ^ 2)⁻¹) volume a b := by
    apply ContinuousOn.intervalIntegrable_of_Icc (h := hab)
    intro y hy
    exact (((continuousAt_id.pow 2).inv₀ (pow_ne_zero 2 (hpos y hy).ne')).neg).continuousWithinAt
  have hparts := intervalIntegral.integral_deriv_mul_eq_sub
    (fun y (_ : y ∈ Set.uIcc a b) => hu y) hv
    ((by fun_prop : Continuous (fun y => Real.cos (T * y))).intervalIntegrable a b) hvin
  have heq : (∫ y in a..b, Real.cos (T * y) / y) -
      (∫ y in a..b, Real.sin (T * y) / (T * y ^ 2)) =
      Real.sin (T * b) / (T * b) - Real.sin (T * a) / (T * a) := by
    rw [← intervalIntegral.integral_sub hcos htail]
    convert (preTransparency := .instances) hparts using 1
    · apply intervalIntegral.integral_congr
      intro y _
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring
    · field_simp
  have hendpoint (y : ℝ) (hy : a ≤ y) : |Real.sin (T * y) / (T * y)| ≤ 1 := by
    have hy0 : 0 < y := ha.trans_le hy
    rw [abs_div, abs_of_pos (mul_pos hT hy0)]
    apply (div_le_one (mul_pos hT hy0)).mpr
    exact (Real.abs_sin_le_one _).trans (hTa.trans (mul_le_mul_of_nonneg_left hy hT.le))
  have hg : IntervalIntegrable (fun y : ℝ => T⁻¹ * (y ^ 2)⁻¹) volume a b := by
    apply ContinuousOn.intervalIntegrable_of_Icc (h := hab)
    intro y hy
    exact (((continuousAt_id.pow 2).inv₀ (pow_ne_zero 2 (hpos y hy).ne')).const_mul _).continuousWithinAt
  have hi : |∫ y in a..b, Real.sin (T * y) / (T * y ^ 2)| ≤ 1 := by
    have hh := intervalIntegral.norm_integral_le_of_norm_le
      (f := fun y : ℝ => Real.sin (T * y) / (T * y ^ 2))
      (g := fun y : ℝ => T⁻¹ * (y ^ 2)⁻¹) hab
      (Filter.Eventually.of_forall (fun y hy => by
        rw [Real.norm_eq_abs, abs_div, abs_of_pos (mul_pos hT (sq_pos_of_pos (hpos y ⟨hy.1.le, hy.2⟩)))]
        calc
          _ ≤ 1 / (T * y ^ 2) := div_le_div_of_nonneg_right (Real.abs_sin_le_one _)
            (mul_nonneg hT.le (sq_nonneg y))
          _ = _ := by simp [div_eq_mul_inv, mul_inv_rev, mul_comm])) hg
    rw [Real.norm_eq_abs, intervalIntegral.integral_const_mul, integral_inverse_square a b ha hab] at hh
    have hsmall : T⁻¹ * a⁻¹ ≤ 1 := by
      rw [← mul_inv_rev]
      exact (inv_le_one₀ (mul_pos ha hT)).mpr (by nlinarith)
    have hnonneg : 0 ≤ T⁻¹ * b⁻¹ := by positivity
    nlinarith
  have htriangle := abs_sub (Real.sin (T * b) / (T * b)) (Real.sin (T * a) / (T * a))
  have htriangle' := abs_add_le
    (Real.sin (T * b) / (T * b) - Real.sin (T * a) / (T * a))
    (∫ y in a..b, Real.sin (T * y) / (T * y ^ 2))
  have hformula : (∫ y in a..b, Real.cos (T * y) / y) =
      (Real.sin (T * b) / (T * b) - Real.sin (T * a) / (T * a)) +
      (∫ y in a..b, Real.sin (T * y) / (T * y ^ 2)) := by linarith
  rw [hformula]
  linarith [hendpoint a le_rfl, hendpoint b hab]

lemma logarithmic_oscillation_nonneg (t a b : ℝ) (ha : 0 < a) (hab : a ≤ b) :
    0 ≤ ∫ y in a..b, (1 - Real.cos (t * y)) / y := by
  apply intervalIntegral.integral_nonneg hab
  intro y hy
  exact div_nonneg (sub_nonneg.mpr (Real.cos_le_one _)) (ha.trans_le hy.1).le

lemma logarithmic_oscillation_lower_pos (T L : ℝ) (hT : 0 < T) (hT2 : T ≤ 2)
    (hL : 1 ≤ L) :
    Real.log (1 + L * T) - 5 ≤ ∫ y in (1 : ℝ)..L, (1 - Real.cos (T * y)) / y := by
  let A := max 1 T⁻¹
  have hA1 : 1 ≤ A := le_max_left _ _
  have hA : 0 < A := zero_lt_one.trans_le hA1
  have hLp : 0 < L := zero_lt_one.trans_le hL
  have hTA : 1 ≤ T * A := by
    calc
      1 = T * T⁻¹ := (mul_inv_cancel₀ hT.ne').symm
      _ ≤ _ := mul_le_mul_of_nonneg_left (le_max_right _ _) hT.le
  have hAT : A * T ≤ 2 := by
    by_cases hh : 1 ≤ T⁻¹
    · simp only [A, max_eq_right hh]
      rw [inv_mul_cancel₀ hT.ne']
      norm_num
    · simpa only [A, max_eq_left (le_of_not_ge hh), one_mul] using hT2
  by_cases hLA : L < A
  · have hsmall : L * T < 1 := by
      rcases lt_max_iff.mp hLA with hh | hh
      · exact False.elim (not_lt_of_ge hL hh)
      · have hm := mul_lt_mul_of_pos_right hh hT
        simpa only [inv_mul_cancel₀ hT.ne'] using hm
    have hlog := Real.log_le_sub_one_of_pos (by positivity : 0 < 1 + L * T)
    have hnonneg := logarithmic_oscillation_nonneg T 1 L (by norm_num) hL
    linarith
  have hAL : A ≤ L := le_of_not_gt hLA
  have hcont (a b : ℝ) (ha : 0 < a) :
      ContinuousOn (fun y => (1 - Real.cos (T * y)) / y) (Set.Icc a b) := by
    intro y hy
    have hy0 := (ha.trans_le hy.1).ne'
    exact (by fun_prop (disch := assumption) :
      ContinuousAt (fun y => (1 - Real.cos (T * y)) / y) y).continuousWithinAt
  have hhead : IntervalIntegrable (fun y => (1 - Real.cos (T * y)) / y) volume 1 A :=
    (hcont 1 A (by norm_num)).intervalIntegrable_of_Icc hA1
  have htail : IntervalIntegrable (fun y => (1 - Real.cos (T * y)) / y) volume A L :=
    (hcont A L hA).intervalIntegrable_of_Icc hAL
  have hrestrict : (∫ y in A..L, (1 - Real.cos (T * y)) / y) ≤
      ∫ y in (1 : ℝ)..L, (1 - Real.cos (T * y)) / y := by
    rw [← intervalIntegral.integral_add_adjacent_intervals hhead htail]
    have hh := logarithmic_oscillation_nonneg T 1 A (by norm_num) hA1
    linarith
  have hi : (∫ y in A..L, (1 - Real.cos (T * y)) / y) =
      Real.log (L / A) - ∫ y in A..L, Real.cos (T * y) / y := by
    have hi₁ : IntervalIntegrable (fun y : ℝ => 1 / y) volume A L := by
      apply ContinuousOn.intervalIntegrable_of_Icc (h := hAL)
      intro y hy
      exact (continuousAt_const.div continuousAt_id (hA.trans_le hy.1).ne').continuousWithinAt
    have hi₂ : IntervalIntegrable (fun y : ℝ => Real.cos (T * y) / y) volume A L := by
      apply ContinuousOn.intervalIntegrable_of_Icc (h := hAL)
      intro y hy
      have hy0 := (hA.trans_le hy.1).ne'
      exact (by fun_prop (disch := assumption) :
        ContinuousAt (fun y => Real.cos (T * y) / y) y).continuousWithinAt
    rw [← integral_one_div_of_pos hA hLp, ← intervalIntegral.integral_sub hi₁ hi₂]
    apply intervalIntegral.integral_congr
    intro y _
    ring
  have hcos := (abs_le.mp (cosine_log_tail T A L hT hA hAL hTA)).2
  have hratio : 1 ≤ L / A := (le_div_iff₀ hA).mpr (by simpa using hAL)
  have hsize : 1 + L * T ≤ 3 * (L / A) := by
    have hh := mul_le_mul_of_nonneg_right hAT (div_nonneg hLp.le hA.le)
    have he : (A * T) * (L / A) = L * T := by field_simp
    rw [he] at hh
    linarith
  have hlog : Real.log (1 + L * T) ≤ Real.log (L / A) + 2 := by
    have hh := Real.log_le_log (by positivity : 0 < 1 + L * T) hsize
    rw [Real.log_mul (by norm_num : (3 : ℝ) ≠ 0) (div_pos hLp hA).ne'] at hh
    have hc := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3)
    linarith
  rw [hi] at hrestrict
  linarith

theorem logarithmic_oscillation_lower (t L : ℝ) (ht : |t| ≤ 2) (hL : 1 ≤ L) :
    Real.log (1 + L * |t|) - 5 ≤ ∫ y in (1 : ℝ)..L, (1 - Real.cos (t * y)) / y := by
  by_cases ht0 : t = 0
  · subst t
    simp
  have hh := logarithmic_oscillation_lower_pos |t| L (abs_pos.mpr ht0) ht hL
  have hcos (y : ℝ) : Real.cos (|t| * y) = Real.cos (t * y) := by
    rcases le_or_gt 0 t with ht' | ht'
    · rw [abs_of_nonneg ht']
    · rw [abs_of_neg ht', neg_mul, Real.cos_neg]
  simpa only [hcos] using hh

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Fourier.ModFivePrimeBands
namespace OAI

/-! Concrete modulus-five supplies and their reciprocal masses. We use
half-open bands `(exp A, exp B]`; this harmless endpoint convention makes
adjacent supplies exactly disjoint and matches finite Abel summation. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.Filter
open scoped _root_.Classical


lemma partialSum_deletedModFive (E : Finset ℕ) (one : Bool) (x : ℝ) :
    partialCoefficientSum (deletedModFiveLogWeight E one) x =
      deletedModFiveTheta E one x := by
  unfold partialCoefficientSum deletedModFiveTheta deletedModFivePrimes
    modFivePrimesUpTo deletedModFiveLogWeight
  rw [sdiff_eq_filter, sum_filter, sum_filter]
  apply sum_congr rfl
  intro p hp
  by_cases h : ModFivePrime one p <;> by_cases he : p ∈ E <;> simp [h, he]






end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.PaddingPrimeOscillation
namespace OAI

/-! The fixed-modulus prime input implies the padding oscillation and the
reciprocal-scale small-ball bound for the actual independent padding law. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.MeasureTheory
open scoped _root_.Classical

lemma oscillatory_log_substitution (t L : ℝ) (hL : 1 ≤ L) :
    (∫ x in Real.exp 1..Real.exp L, oscillatoryReciprocalLog t x) =
      ∫ y in (1 : ℝ)..L, (1 - Real.cos (t * y)) / y := by
  have hab : Real.exp 1 ≤ Real.exp L := Real.exp_le_exp.mpr hL
  have hxn (x : ℝ) (hx : x ∈ Set.uIcc (Real.exp 1) (Real.exp L)) : 0 < x := by
    have hx' : x ∈ Set.Icc (Real.exp 1) (Real.exp L) := by
      simpa only [Set.uIcc_of_le hab] using hx
    exact (Real.exp_pos 1).trans_le hx'.1
  have hderiv (x : ℝ) (hx : x ∈ Set.uIcc (Real.exp 1) (Real.exp L)) :
      HasDerivAt Real.log x⁻¹ x := Real.hasDerivAt_log (hxn x hx).ne'
  have hdcont : ContinuousOn (fun x : ℝ => x⁻¹) (Set.uIcc (Real.exp 1) (Real.exp L)) :=
    continuousOn_id.inv₀ (fun x hx => (hxn x hx).ne')
  have hg : ContinuousOn (fun y : ℝ => (1 - Real.cos (t * y)) / y)
      (Real.log '' Set.uIcc (Real.exp 1) (Real.exp L)) := by
    rintro y ⟨x, hx, rfl⟩
    have hx' : x ∈ Set.Icc (Real.exp 1) (Real.exp L) := by
      simpa only [Set.uIcc_of_le hab] using hx
    have hl : 1 ≤ Real.log x := by
      simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 1) hx'.1
    have hn : Real.log x ≠ 0 := (zero_lt_one.trans_le hl).ne'
    exact (by fun_prop (disch := assumption) :
      ContinuousAt (fun y : ℝ => (1 - Real.cos (t * y)) / y) (Real.log x)).continuousWithinAt
  have hh := intervalIntegral.integral_comp_mul_deriv' hderiv hdcont hg
  rw [Real.log_exp, Real.log_exp] at hh
  rw [← hh]
  apply intervalIntegral.integral_congr
  intro x _
  unfold oscillatoryReciprocalLog reciprocalLog
  simp only [Function.comp_def, div_eq_mul_inv]
  ring

lemma modFivePrimeBand_oscillation (E : Finset ℕ) (one : Bool) (a b t : ℝ) :
    (∑ p ∈ modFivePrimeBand E one a b, (1 - Real.cos (t * Real.log p)) / p) =
      ∑ p ∈ Ioc ⌊a⌋₊ ⌊b⌋₊, oscillatoryReciprocalLog t p * deletedModFiveLogWeight E one p := by
  rw [modFivePrimeBand, sum_filter]
  apply sum_congr rfl
  intro p hp
  by_cases hs : ModFivePrime one p ∧ p ∉ E
  · rw [if_pos hs]
    unfold deletedModFiveLogWeight
    rw [if_pos hs]
    have hl : Real.log (p : ℝ) ≠ 0 :=
      (Real.log_pos (by exact_mod_cast hs.1.1.one_lt)).ne'
    unfold oscillatoryReciprocalLog reciprocalLog
    field_simp
  · simp [deletedModFiveLogWeight, hs]

lemma padding_band_subset (E : Finset ℕ) (a L : ℝ) :
    modFivePrimeBand E false a (Real.exp L) ⊆ paddingPrimeSupply E L := by
  intro p hp
  obtain ⟨hpi, hs, he⟩ := mem_filter.mp hp
  apply mem_sdiff.mpr
  refine ⟨?_, he⟩
  apply mem_filter.mpr
  exact ⟨mem_Icc.mpr ⟨Nat.zero_le _, (mem_Ioc.mp hpi).2⟩, hs⟩

theorem ModFiveThetaInput.padding_oscillation (hP : ModFiveThetaInput) (E : Finset ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (L t : ℝ), 1 ≤ L → |t| ≤ 2 →
      (3 / 4 : ℝ) * Real.log (1 + L * |t|) - C ≤
        paddingOscillation (paddingPrimeSupply E L) t := by
  obtain ⟨K, hK, herror⟩ := hP.deleted_log_error E
  refine ⟨10 * K + 15 / 4, by positivity, fun L t hL ht => ?_⟩
  have hh := oscillatory_theta_error (deletedModFiveLogWeight E false)
    (modFiveDensity false) K (Real.exp 1) (Real.exp L) t hK le_rfl
      (Real.exp_le_exp.mpr hL) ht (fun x hx => by
        rw [partialSum_deletedModFive]
        apply herror false x
        have h2 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
        exact h2.trans hx.1)
  rw [← modFivePrimeBand_oscillation, oscillatory_log_substitution t L hL, Real.log_exp] at hh
  have hlower := (abs_le.mp hh).1
  have hmain := logarithmic_oscillation_lower t L ht hL
  have hsubset :
      (∑ p ∈ modFivePrimeBand E false (Real.exp 1) (Real.exp L),
        (1 - Real.cos (t * Real.log p)) / p) ≤ paddingOscillation (paddingPrimeSupply E L) t := by
    apply sum_le_sum_of_subset_of_nonneg (padding_band_subset E (Real.exp 1) L)
    intro p _ _
    exact div_nonneg (sub_nonneg.mpr (Real.cos_le_one _)) (Nat.cast_nonneg p)
  norm_num [modFiveDensity] at hlower
  linarith


/-- The precise padding difference law has `O_E(1/L)` mass in every
unit interval centered at zero. Its bound is uniform in all centered tuples. -/
theorem ModFiveThetaInput.padding_small_ball (hP : ModFiveThetaInput) (E : Finset ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ L : ℝ, 1 ≤ L →
      (paddingDifferenceLaw (paddingPrimeSupply E L)
        (fun _ hp => (paddingPrimeSupply_prime hp).two_le)).probability
          (fun x => |paddingDifferenceValue (paddingPrimeSupply E L) x| ≤ 1) ≤ C / L := by
  obtain ⟨C, _, hC⟩ := hP.padding_oscillation E
  refine ⟨20 * Real.exp ((8 / 5 : ℝ) * C + 64 / 5), by positivity, fun L hL => ?_⟩
  apply paddingDifference_small_ball _ _ L C (zero_lt_one.trans_le hL)
  intro t ht
  apply hC L t hL
  rw [abs_of_nonneg ht.1]
  linarith [ht.2]

end TwoPointCorrelations

end OAI

end

theorem solution : type_of% @OAI.TwoPointCorrelations.ModFiveThetaInput.padding_small_ball := @OAI.TwoPointCorrelations.ModFiveThetaInput.padding_small_ball
