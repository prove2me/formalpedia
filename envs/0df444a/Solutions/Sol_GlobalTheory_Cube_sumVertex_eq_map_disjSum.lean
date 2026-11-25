-- Prove2me | solution 1 for GlobalTheory.Cube.sumVertex_eq_map_disjSum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T06:13:27.09939+00:00
-- url     : https://prove2.me/submissions/f1fc1cb6-6366-4180-b7fc-15ed2fac375c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_CubeComplexAcyclicIffQuasiIsoCechAug
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_CubeTotalComplexAcyclicOfSlicesInductionOnCard

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
open GlobalTheory.Cube
variable {ι κ : Type} [LinearOrder ι] [LinearOrder κ] {R : Type u} [Ring R]
namespace GlobalTheory.Cube
theorem _root_.solution (s : Finset ι) (t : Finset κ) :
    sumVertex s t = (s.disjSum t).map toLex.toEmbedding := by
  ext j
  obtain ⟨j, rfl⟩ := toLex.surjective j
  cases j <;> simp
end GlobalTheory.Cube
