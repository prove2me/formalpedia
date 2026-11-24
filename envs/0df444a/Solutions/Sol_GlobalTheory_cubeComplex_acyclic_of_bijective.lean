-- Prove2me | solution 1 for GlobalTheory.cubeComplex_acyclic_of_bijective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T14:37:15.62381+00:00
-- url     : https://prove2.me/submissions/d2c99c3a-3bbd-4187-b5a1-094e065ac9da

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_IsIsoTermComparisonRestrictScalars
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_CubeComplexAcyclicIffQuasiIsoCechAug
import Theorems.Thm_GlobalTheory_cubeComplex_exactAt_of_bijective


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits HomologicalComplex
universe v u
open GlobalTheory
variable {ι : Type} [LinearOrder ι] {R : Type u} [Ring R]
namespace GlobalTheory
theorem _root_.solution (A : Cube.{v} ι R) (i : ι)
    (hA : ∀ s : Finset ι, i ∉ s → Function.Bijective (Cube.res A (Finset.subset_insert i s))) :
    (cubeComplex A).Acyclic :=
  cubeComplex_exactAt_of_bijective A i hA
end GlobalTheory
