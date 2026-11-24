-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.Core.Density.dens_continuous
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T13:14:04.05361+00:00
-- url     : https://prove2.me/submissions/2605c61c-fba1-40e1-9f39-6188eb289a4e

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_CountData
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_FourierInversionSchwartzBruhatStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_PositiveDefiniteDensity

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core
open scoped ENNReal NNReal MatrixGroups
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.Core GlobalTheory.CompanionTheory.SW.Core.Density
variable {V : Type} [AddCommGroup V] [TopologicalSpace V] [MeasurableSpace V]
variable [IsTopologicalAddGroup V]
namespace GlobalTheory.CompanionTheory.SW.Core.Density
theorem _root_.solution [SecondCountableTopology V] [BorelSpace V] {χ : V → V → ℂ} {μ m : Measure V}
    (hc : Continuous (fun p : V × V => χ p.1 p.2)) (hn : ∀ x y, ‖χ x y‖ = 1)
    (hint : Integrable (mhat χ m) μ) : Continuous (dens χ μ m) := by
  refine continuous_of_dominated (bound := fun y => ‖mhat χ m y‖) ?_ ?_ hint.norm ?_
  · intro x
    exact hint.aestronglyMeasurable.mul
      (hc.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  · intro x
    exact Filter.Eventually.of_forall fun y => by simp [hn]
  · exact Filter.Eventually.of_forall fun y =>
      continuous_const.mul (hc.comp (continuous_neg.prodMk continuous_const))
end GlobalTheory.CompanionTheory.SW.Core.Density
