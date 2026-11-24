-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.Core.Density.coset_sb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T13:54:50.334858+00:00
-- url     : https://prove2.me/submissions/3e1f503a-2c44-4052-8ffb-347ef95e046c

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_CountData
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_FourierInversionSchwartzBruhatStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_PositiveDefiniteDensity
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_Core_Density_coset_isOpen
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_Core_Density_coset_isCompact

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
theorem _root_.solution [T2Space V] {L : AddSubgroup V} (hK : IsCompact (L : Set V)) (hO : IsOpen (L : Set V))
    (a : V) : SB (Set.indicator (coset L a) (fun _ => (1 : ℂ))) := by
  have hc := coset_isCompact hK a
  have ho := coset_isOpen hO a
  refine ⟨?_, .intro hc fun x hx => Set.indicator_of_notMem hx _⟩
  exact (LocallyConstant.indicator (1 : LocallyConstant V ℂ) ⟨hc.isClosed, ho⟩).isLocallyConstant
end GlobalTheory.CompanionTheory.SW.Core.Density
