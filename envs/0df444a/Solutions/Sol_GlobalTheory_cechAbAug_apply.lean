-- Prove2me | solution 1 for GlobalTheory.cechAbAug_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:29:55.873704+00:00
-- url     : https://prove2.me/submissions/1bbe0170-34ac-49af-a50f-33af7833113c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_ExistsPowMulPowEqOfIsZeroCechH
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_CubeComplexAcyclicIffQuasiIsoCechAug
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_PresheafCubeExactAtSuccOfSurjective

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace Opposite
universe w v u
noncomputable section
open GlobalTheory
variable {T : TopCat.{w}} {ι : Type}
namespace GlobalTheory
theorem _root_.solution (P : (Opens T)ᵒᵖ ⥤ AddCommGrpCat.{v}) (V : Opens T) (U : ι → Opens T)
    (x : P.obj (op V)) (s : {s : Finset ι // s.card = 1}) :
    cechAbAug P V U x s = P.map (homOfLE (cechOpen_le V U s.1)).op x := rfl
end GlobalTheory
