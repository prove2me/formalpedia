-- Prove2me | solution 1 for GlobalTheory.T.exists_continuous_representative_average
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T21:06:28.471973+00:00
-- url     : https://prove2.me/submissions/b7444fe1-d4bd-44b1-8ca8-e6306efd6fbd

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsContinuousRepresentativeAverage
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LocallyIntegrableRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsContinuousRepresentativeAverageStatement
import Theorems.Thm_GlobalTheory_LocRep_exists_continuous_rep_average


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
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure] (K : Type) [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K] (ι : K → G → ℂ), (∀ C, IsCompact C → ∃ M : ℝ, ∀ v, IntegrableOn (ι v) C μ ∧ ∫ x in C, ‖ι v x‖ ∂μ ≤ M * ‖v‖) → (∀ (a : ℂ) v w, ι (a • v + w) =ᵐ[μ] fun x => a * ι v x + ι w x) → ∀ (ρ : G →* (K →L[ℂ] K)), (∀ g v, ‖ρ g v‖ = ‖v‖) → (∀ v, Continuous fun g => ρ g v) → (∀ g v, ι (ρ g v) =ᵐ[μ] fun x => ι v (x * g)) → ∀ (η : G → ℂ) (v : K), Continuous η → HasCompactSupport η → ∃ φ : G → ℂ, Continuous φ ∧ ι (∫ y, η y • ρ y v ∂μ) =ᵐ[μ] φ := by
  first | exact @GlobalTheory.LocRep.exists_continuous_rep_average | exact GlobalTheory.LocRep.exists_continuous_rep_average | (intros; apply GlobalTheory.LocRep.exists_continuous_rep_average <;> assumption)
end _root_.GlobalTheory.T
