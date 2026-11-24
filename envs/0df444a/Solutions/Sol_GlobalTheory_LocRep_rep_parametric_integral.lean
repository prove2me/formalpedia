-- Prove2me | solution 1 for GlobalTheory.LocRep.rep_parametric_integral
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T18:48:58.517799+00:00
-- url     : https://prove2.me/submissions/80d22b24-6df7-40c4-891d-53b7ea93f364

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LocallyIntegrableRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RepresentativeParametricIntegralContinuousFamily
import Theorems.Thm_GlobalTheory_LocRep_exists_pairing
import Theorems.Thm_GlobalTheory_LocRep_rep_of_pairing


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
open scoped ContDiff
open GlobalTheory GlobalTheory.LocRep
namespace GlobalTheory.LocRep
theorem _root_.solution : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure] (K : Type) [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K] (ι : K → G → ℂ), (∀ C, IsCompact C → ∃ M : ℝ, ∀ v, IntegrableOn (ι v) C μ ∧ ∫ x in C, ‖ι v x‖ ∂μ ≤ M * ‖v‖) → (∀ (a : ℂ) v w, ι (a • v + w) =ᵐ[μ] fun x => a * ι v x + ι w x) → ∀ (T : Type) [TopologicalSpace T] [SecondCountableTopology T] [T2Space T] [MeasurableSpace T] [BorelSpace T] (ν : Measure T) [IsLocallyFiniteMeasure ν] (Q : Set T) (w : T → K) (φ : T → G → ℂ), IsCompact Q → Continuous w → Continuous (Function.uncurry φ) → (∀ t, ι (w t) =ᵐ[μ] φ t) → (Continuous fun x => ∫ t in Q, φ t x ∂ν) ∧ ι (∫ t in Q, w t ∂ν) =ᵐ[μ] fun x => ∫ t in Q, φ t x ∂ν := by
  intro G _ _ _ _ _ _ _ _ μ _ K _ _ _ ι hloc hlin T _ _ _ _ _ ν _ Q w φ hQ hw hφ hrep
  have hcont : Continuous fun x => ∫ t in Q, φ t x ∂ν :=
    continuous_parametric_integral_of_continuous (f := fun x t => φ t x)
      (hφ.comp continuous_swap) hQ
  refine ⟨hcont, rep_of_pairing hloc hcont.locallyIntegrable fun C hC => ?_⟩
  obtain ⟨Λ, hΛ⟩ := exists_pairing hloc hlin hC
  have hwi : IntegrableOn w Q ν := hw.continuousOn.integrableOn_compact hQ
  have hint : Integrable (Function.uncurry φ) ((ν.restrict Q).prod (μ.restrict C)) := by
    rw [Measure.prod_restrict]
    exact hφ.continuousOn.integrableOn_compact (hQ.prod hC)
  rw [← hΛ, ← Λ.integral_comp_comm hwi, ← integral_integral_swap hint]
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  simp only
  rw [hΛ]
  exact integral_congr_ae (ae_restrict_of_ae (hrep t))
end GlobalTheory.LocRep
