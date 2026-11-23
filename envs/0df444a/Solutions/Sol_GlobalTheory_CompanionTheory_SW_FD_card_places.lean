-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.FD.card_places
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:28:49.495802+00:00
-- url     : https://prove2.me/submissions/a858b19a-64b1-4806-a765-76f9241bb7e2

import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_CountData
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_LatticeFundamentalDomainVolume

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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.FD
open scoped Pointwise
variable {F : Type} [Field F] [NumberField F]
namespace GlobalTheory.CompanionTheory.SW.FD
theorem _root_.solution (hF : IsTotallyReal F) :
    Fintype.card (InfinitePlace F) = Module.finrank ℚ F := by
  rw [Fintype.card_congr (placeEquiv hF), AlgHom.card]
end GlobalTheory.CompanionTheory.SW.FD
