-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.CofinalDual.relIndex_ne_zero_of_isOpen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T13:12:18.162947+00:00
-- url     : https://prove2.me/submissions/afb4e397-3a23-4376-882c-1292ba312cf2

import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_CountData
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_AnnihilatorOfAnnihilatorLe

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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.CofinalDual
namespace GlobalTheory.CompanionTheory.SW.CofinalDual
theorem _root_.solution {V : Type} [AddCommGroup V] [TopologicalSpace V]
    [IsTopologicalAddGroup V] (S T : AddSubgroup V) (hS : IsOpen (S : Set V))
    (hT : IsCompact (T : Set V)) : S.relIndex T ≠ 0 := by
  haveI : CompactSpace T := isCompact_iff_compactSpace.1 hT
  have ho : IsOpen ((S.addSubgroupOf T : AddSubgroup T) : Set T) :=
    hS.preimage continuous_subtype_val
  haveI := AddSubgroup.quotient_finite_of_isOpen _ ho
  have : (S.addSubgroupOf T).FiniteIndex := AddSubgroup.finiteIndex_of_finite_quotient
  exact this.index_ne_zero
end GlobalTheory.CompanionTheory.SW.CofinalDual
