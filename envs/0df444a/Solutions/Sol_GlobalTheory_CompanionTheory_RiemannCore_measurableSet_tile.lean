-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.RiemannCore.measurableSet_tile
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T13:29:27.372165+00:00
-- url     : https://prove2.me/submissions/34329da8-05db-4c51-bd5c-fb4993b752da

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CosetOff
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_LatticePointCountScaling
import Theorems.Thm_GlobalTheory_CompanionTheory_RiemannCore_measurableSet_cell

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter GlobalTheory.CompanionTheory.Equi
open scoped Classical
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.RiemannCore
variable {G : Type} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
variable [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G]
  [BorelSpace G]
namespace GlobalTheory.CompanionTheory.RiemannCore
theorem _root_.solution {D : Set G} (hD : MeasurableSet D) (R : Finset G) (l : G) :
    MeasurableSet (tile D R l) :=
  (measurable_const_add (-l)) (measurableSet_cell hD R)
end GlobalTheory.CompanionTheory.RiemannCore
