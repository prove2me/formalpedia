-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.Core.Density.coset_isCompact
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T13:33:50.054832+00:00
-- url     : https://prove2.me/submissions/435138f8-0030-4a77-8815-25acc1b75331

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_CountData
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_FourierInversionSchwartzBruhatStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_PositiveDefiniteDensity
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_Core_Density_coset_eq_image

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
theorem _root_.solution {L : AddSubgroup V} (hL : IsCompact (L : Set V)) (a : V) :
    IsCompact (coset L a) := by
  rw [coset_eq_image]
  exact hL.image (continuous_id.add continuous_const)
end GlobalTheory.CompanionTheory.SW.Core.Density
