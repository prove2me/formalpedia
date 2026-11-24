-- Prove2me | solution 1 for GlobalTheory.polarised_schur_relations
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:29:04.396272+00:00
-- url     : https://prove2.me/submissions/8c903d52-62af-4a7f-8a39-3f34a249472e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SesqEqZeroOfDiagEqZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open MeasureTheory
open scoped InnerProductSpace
namespace GlobalTheory
open MeasureTheory in
open scoped InnerProductSpace in
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] in
variable {G : Type} [Group G] [MeasurableSpace G] {μ : Measure G} {σ : G →* (H →L[ℂ] H)} {d : ℝ} in
private lemma integrable_matrixCoeff_mul_star
    (hmeas : ∀ x y : H, AEStronglyMeasurable (fun g => ⟪y, σ g x⟫_ℂ) μ)
    (hsq : ∀ x y : H, Integrable (fun g => ‖⟪y, σ g x⟫_ℂ‖ ^ 2) μ) (x y x' y' : H) :
    Integrable (fun g => ⟪y, σ g x⟫_ℂ * star ⟪y', σ g x'⟫_ℂ) μ := by
  refine Integrable.mono' ((hsq x y).add (hsq x' y'))
    ((hmeas x y).mul (hmeas x' y').star) (Filter.Eventually.of_forall fun g => ?_)
  simp only [norm_mul, norm_star, Pi.add_apply]
  nlinarith [sq_nonneg (‖⟪y, σ g x⟫_ℂ‖ - ‖⟪y', σ g x'⟫_ℂ‖),
    mul_nonneg (norm_nonneg ⟪y, σ g x⟫_ℂ) (norm_nonneg ⟪y', σ g x'⟫_ℂ)]
open MeasureTheory in
open scoped InnerProductSpace in
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] in
variable {G : Type} [Group G] [MeasurableSpace G] {μ : Measure G} {σ : G →* (H →L[ℂ] H)} {d : ℝ} in
private lemma integral_matrixCoeff_mul_star_self
    (hsq : ∀ x y : H, ∫ g, ‖⟪y, σ g x⟫_ℂ‖ ^ 2 ∂μ = ‖x‖ ^ 2 * ‖y‖ ^ 2 / d) (x y : H) :
    ∫ g, ⟪y, σ g x⟫_ℂ * star ⟪y, σ g x⟫_ℂ ∂μ = ⟪x, x⟫_ℂ * ⟪y, y⟫_ℂ / d := by
  have h : (fun g => ⟪y, σ g x⟫_ℂ * star ⟪y, σ g x⟫_ℂ) =
      fun g => ((‖⟪y, σ g x⟫_ℂ‖ ^ 2 : ℝ) : ℂ) := by
    funext g
    rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  rw [h, integral_complex_ofReal, hsq x y, inner_self_eq_norm_sq_to_K,
    inner_self_eq_norm_sq_to_K]
  first
    | (push_cast; rfl)
    | simp
open scoped ComplexConjugate in
private lemma mul_conj_eq_polarization (a b : ℂ) :
    a * conj b = 1 / 4 * ((a + b) * conj (a + b) - (a - b) * conj (a - b)
      + Complex.I * ((a + Complex.I * b) * conj (a + Complex.I * b))
      - Complex.I * ((a - Complex.I * b) * conj (a - Complex.I * b))) := by
  simp only [map_add, map_sub, map_mul, Complex.conj_I]
  ring_nf
  simp only [Complex.I_sq, Complex.I_pow_three]
  ring
open MeasureTheory in
open scoped InnerProductSpace in
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] in
private lemma inner_swap_eq_polarization (x x' : H) :
    ⟪x', x⟫_ℂ = 1 / 4 * (⟪x + x', x + x'⟫_ℂ - ⟪x - x', x - x'⟫_ℂ
      + Complex.I * ⟪x + Complex.I • x', x + Complex.I • x'⟫_ℂ
      - Complex.I * ⟪x - Complex.I • x', x - Complex.I • x'⟫_ℂ) := by
  simp only [inner_add_left, inner_sub_left, inner_smul_left, inner_add_right,
    inner_sub_right, inner_smul_right, Complex.conj_I]
  ring_nf
  simp only [Complex.I_sq, Complex.I_pow_three]
  ring
open MeasureTheory in
open scoped InnerProductSpace in
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] in
variable {G : Type} [Group G] [MeasurableSpace G] {μ : Measure G} {σ : G →* (H →L[ℂ] H)} {d : ℝ} in
private lemma integral_matrixCoeff_mul_star_same_left
    (hmeas : ∀ x y : H, AEStronglyMeasurable (fun g => ⟪y, σ g x⟫_ℂ) μ)
    (hsq : ∀ x y : H, Integrable (fun g => ‖⟪y, σ g x⟫_ℂ‖ ^ 2) μ ∧
      ∫ g, ‖⟪y, σ g x⟫_ℂ‖ ^ 2 ∂μ = ‖x‖ ^ 2 * ‖y‖ ^ 2 / d) (x x' y : H) :
    ∫ g, ⟪y, σ g x⟫_ℂ * star ⟪y, σ g x'⟫_ℂ ∂μ = ⟪x', x⟫_ℂ * ⟪y, y⟫_ℂ / d := by
  have hint := integrable_matrixCoeff_mul_star hmeas (fun x y => (hsq x y).1)
  have hdiag := integral_matrixCoeff_mul_star_self (fun x y => (hsq x y).2)
  have hpt : ∀ g, ⟪y, σ g x⟫_ℂ * star ⟪y, σ g x'⟫_ℂ =
      (1 / 4 : ℂ) * (⟪y, σ g (x + x')⟫_ℂ * star ⟪y, σ g (x + x')⟫_ℂ
        - ⟪y, σ g (x - x')⟫_ℂ * star ⟪y, σ g (x - x')⟫_ℂ
        + Complex.I * (⟪y, σ g (x + Complex.I • x')⟫_ℂ * star ⟪y, σ g (x + Complex.I • x')⟫_ℂ)
        - Complex.I * (⟪y, σ g (x - Complex.I • x')⟫_ℂ * star ⟪y, σ g (x - Complex.I • x')⟫_ℂ)) := by
    intro g
    rw [Complex.star_def, mul_conj_eq_polarization ⟪y, σ g x⟫_ℂ ⟪y, σ g x'⟫_ℂ]
    simp only [map_add, map_sub, map_smul, inner_add_right, inner_sub_right, inner_smul_right,
      Complex.star_def]
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt), integral_const_mul,
    integral_sub, integral_add, integral_sub, integral_const_mul, integral_const_mul,
    hdiag, hdiag, hdiag, hdiag, inner_swap_eq_polarization x x']
  · ring
  all_goals first
    | exact hint _ _ _ _
    | exact (hint _ _ _ _).const_mul _
    | exact (hint _ _ _ _).sub (hint _ _ _ _)
    | exact ((hint _ _ _ _).sub (hint _ _ _ _)).add ((hint _ _ _ _).const_mul _)
open scoped ComplexConjugate in
private lemma mul_conj_eq_polarization_four (a a' b b' : ℂ) :
    a * conj b' = 1 / 4 * ((a + a') * conj (b + b') - (a - a') * conj (b - b')
      - Complex.I * ((a - Complex.I * a') * conj (b - Complex.I * b'))
      + Complex.I * ((a + Complex.I * a') * conj (b + Complex.I * b'))) := by
  simp only [map_add, map_sub, map_mul, Complex.conj_I]
  ring_nf
  simp only [Complex.I_sq, Complex.I_pow_three]
  ring
open MeasureTheory in
open scoped InnerProductSpace in
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] in
private lemma inner_eq_polarization (w w' : H) :
    ⟪w, w'⟫_ℂ = 1 / 4 * (⟪w + w', w + w'⟫_ℂ - ⟪w - w', w - w'⟫_ℂ
      - Complex.I * ⟪w + Complex.I • w', w + Complex.I • w'⟫_ℂ
      + Complex.I * ⟪w - Complex.I • w', w - Complex.I • w'⟫_ℂ) := by
  simp only [inner_add_left, inner_sub_left, inner_smul_left, inner_add_right,
    inner_sub_right, inner_smul_right, Complex.conj_I]
  ring_nf
  simp only [Complex.I_sq, Complex.I_pow_three]
  ring
end GlobalTheory
end

set_option autoImplicit false
open MeasureTheory
open scoped InnerProductSpace
open GlobalTheory
open MeasureTheory
open scoped InnerProductSpace
namespace GlobalTheory
namespace _root_.GlobalTheory
theorem _root_.solution :
    ∀ (G : Type) [Group G] [MeasurableSpace G] (μ : Measure G) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : G →* (H →L[ℂ] H)) (d : ℝ), (∀ x y : H, AEStronglyMeasurable (fun g => ⟪y, σ g x⟫_ℂ) μ) → (∀ x y : H, Integrable (fun g => ‖⟪y, σ g x⟫_ℂ‖ ^ 2) μ ∧ ∫ g, ‖⟪y, σ g x⟫_ℂ‖ ^ 2 ∂μ = ‖x‖ ^ 2 * ‖y‖ ^ 2 / d) → ∀ v w v' w' : H, Integrable (fun g => ⟪w, σ g v⟫_ℂ * star ⟪w', σ g v'⟫_ℂ) μ ∧ ∫ g, ⟪w, σ g v⟫_ℂ * star ⟪w', σ g v'⟫_ℂ ∂μ = ⟪v', v⟫_ℂ * ⟪w, w'⟫_ℂ / (d : ℂ) := by
  intro G _ _ μ H _ _ _ σ d hmeas hsq v w v' w'
  have hint := integrable_matrixCoeff_mul_star hmeas (fun x y => (hsq x y).1)
  have hone := integral_matrixCoeff_mul_star_same_left hmeas hsq
  refine ⟨hint v w v' w', ?_⟩
  have hpt : ∀ g, ⟪w, σ g v⟫_ℂ * star ⟪w', σ g v'⟫_ℂ =
      (1 / 4 : ℂ) * (⟪w + w', σ g v⟫_ℂ * star ⟪w + w', σ g v'⟫_ℂ
        - ⟪w - w', σ g v⟫_ℂ * star ⟪w - w', σ g v'⟫_ℂ
        - Complex.I * (⟪w + Complex.I • w', σ g v⟫_ℂ * star ⟪w + Complex.I • w', σ g v'⟫_ℂ)
        + Complex.I * (⟪w - Complex.I • w', σ g v⟫_ℂ * star ⟪w - Complex.I • w', σ g v'⟫_ℂ)) := by
    intro g
    rw [Complex.star_def, mul_conj_eq_polarization_four ⟪w, σ g v⟫_ℂ ⟪w', σ g v⟫_ℂ
      ⟪w, σ g v'⟫_ℂ ⟪w', σ g v'⟫_ℂ]
    simp only [inner_add_left, inner_sub_left, inner_smul_left, Complex.conj_I, Complex.star_def,
      neg_mul, ← sub_eq_add_neg, sub_neg_eq_add]
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt), integral_const_mul,
    integral_add, integral_sub, integral_sub, integral_const_mul, integral_const_mul,
    hone, hone, hone, hone, inner_eq_polarization w w']
  · ring
  all_goals first
    | exact hint _ _ _ _
    | exact (hint _ _ _ _).const_mul _
    | exact (hint _ _ _ _).sub (hint _ _ _ _)
    | exact ((hint _ _ _ _).sub (hint _ _ _ _)).sub ((hint _ _ _ _).const_mul _)
end _root_.GlobalTheory
end GlobalTheory
