-- Prove2me | solution 1 for GlobalTheory.T.fourier_transform_lattice_indicator
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T21:09:39.107771+00:00
-- url     : https://prove2.me/submissions/4e84ed73-53af-4553-b869-cb1ca9c64641

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_FourierTransformLatticeIndicator
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_CountData
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_FourierTransformLatticeIndicatorStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_Core_fou_indicator_coset


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
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (V : Type) [AddCommGroup V] [TopologicalSpace V] [MeasurableSpace V] (χ : V → V → ℂ) (μ : Measure V), NADual V χ μ → ∀ L : AddSubgroup V, IsCompact (L : Set V) → IsOpen (L : Set V) → ∀ a y : V, fou χ μ (Set.indicator {x | x - a ∈ L} (fun _ => (1 : ℂ))) y = ((μ L).toReal : ℂ) * χ a y * Set.indicator (perp χ L) (fun _ => (1 : ℂ)) y := by
  first | exact @GlobalTheory.CompanionTheory.SW.Core.fou_indicator_coset | exact GlobalTheory.CompanionTheory.SW.Core.fou_indicator_coset | (intros; apply GlobalTheory.CompanionTheory.SW.Core.fou_indicator_coset <;> assumption)
end _root_.GlobalTheory.T
