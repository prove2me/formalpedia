-- Prove2me | solution 1 for GlobalTheory.CuspGL.extZero_toLin_injective
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:34:15.089794+00:00
-- url     : https://prove2.me/submissions/9f5f340f-3c88-4d49-bb42-525ee6939211

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_AbByPOfComm
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_GeneralLinearFunctionExtendZeroEndProperties

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI
open GlobalTheory GlobalTheory.CuspGL
variable {F : Type} [Field F] {d : ℕ}
namespace GlobalTheory.CuspGL
theorem _root_.solution :
    Function.Injective fun x : GL (Fin d) F => Matrix.toLin' (x : Matrix (Fin d) (Fin d) F) := fun _ _ h => Units.ext (Matrix.toLin'.injective h)
end GlobalTheory.CuspGL
