-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.FourierPi.fubini_box
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T13:15:13.187666+00:00
-- url     : https://prove2.me/submissions/f3af895a-b6ab-4277-9117-ebf398069993

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_HarrisTaylorCardKilledByIdealEqAbsNormPow
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_FourierPi_continuous_psi_dot

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.FourierPi
variable {R : Type} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
  [LocallyCompactSpace R] [SecondCountableTopology R] [T2Space R] [MeasurableSpace R] [BorelSpace R]
  {ψ : R → ℂ} {ι : Type} [Fintype ι]
namespace GlobalTheory.CompanionTheory.SW.FourierPi
theorem _root_.solution (hc : Continuous ψ) (ha : ∀ x y, ψ (x + y) = ψ x * ψ y) (hn : ∀ x, ‖ψ x‖ = 1)
    (μ : Measure (ι → R)) [SFinite μ] (B : Set (ι → R)) (hBf : μ B < ⊤) (Φ : (ι → R) → ℂ)
    (Φc : Continuous Φ) (hi : Integrable Φ μ) (z : ι → R) :
    ∫ y in B, (∫ x, Φ x * ψ (x ⬝ᵥ y) ∂μ) * ψ (y ⬝ᵥ z) ∂μ =
      ∫ x, Φ x * ∫ y in B, ψ ((x + z) ⬝ᵥ y) ∂μ ∂μ := by
  haveI : IsFiniteMeasure (μ.restrict B) := ⟨by rwa [Measure.restrict_apply_univ]⟩
  have e1 : ∀ y, (∫ x, Φ x * ψ (x ⬝ᵥ y) ∂μ) * ψ (y ⬝ᵥ z) = ∫ x, Φ x * ψ ((x + z) ⬝ᵥ y) ∂μ := by
    intro y
    rw [← integral_mul_const]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    change Φ x * ψ (x ⬝ᵥ y) * ψ (y ⬝ᵥ z) = Φ x * ψ ((x + z) ⬝ᵥ y)
    rw [add_dotProduct, ha, dotProduct_comm z y, mul_assoc]
  simp_rw [e1]
  rw [integral_integral_swap]
  · simp_rw [integral_const_mul]
  · have h0 : Integrable (fun p : (ι → R) × (ι → R) => (1 : ℂ) * Φ p.2) ((μ.restrict B).prod μ) :=
      (integrable_const (1 : ℂ)).mul_prod hi
    refine h0.mono ?_ (Filter.Eventually.of_forall fun p => ?_)
    · refine Continuous.aestronglyMeasurable ?_
      exact (Φc.comp continuous_snd).mul
        (continuous_psi_dot hc (continuous_snd.add continuous_const) continuous_fst)
    · simp [Function.uncurry, hn]
end GlobalTheory.CompanionTheory.SW.FourierPi
