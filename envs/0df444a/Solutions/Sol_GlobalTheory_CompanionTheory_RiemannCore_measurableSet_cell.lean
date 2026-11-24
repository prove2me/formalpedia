-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.RiemannCore.measurableSet_cell
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T13:09:38.984232+00:00
-- url     : https://prove2.me/submissions/60bfaaf6-922d-44fe-ad8d-f2d30ad9a6cd

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CosetOff
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_LatticePointCountScaling

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
theorem _root_.solution {D : Set G} (hD : MeasurableSet D) (R : Finset G) :
    MeasurableSet (cell D R) :=
  Finset.measurableSet_biUnion _ fun r _ => (measurable_const_add (-r)) hD
end GlobalTheory.CompanionTheory.RiemannCore
