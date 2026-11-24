-- Prove2me | solution 1 for GlobalTheory.CuspGL.ipGL_eq_finsum_GL
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T14:05:09.471586+00:00
-- url     : https://prove2.me/submissions/93ece4a0-1bc3-4c30-8df7-2acc0bce35b2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_AbByPOfComm
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_GeneralLinearFunctionExtendZeroEndProperties
import Theorems.Thm_GlobalTheory_CuspGL_extZero_toLin_injective
import Theorems.Thm_GlobalTheory_CuspGL_extZero_isUnit_iff

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
theorem _root_.solution (φ φ' : Module.End F (Fin d → F) → ℂ) :
    ipGL φ φ' = ∑ᶠ x : GL (Fin d) F, φ (Matrix.toLin' (x : Matrix (Fin d) (Fin d) F)) *
      star (φ' (Matrix.toLin' (x : Matrix (Fin d) (Fin d) F))) := by
  unfold ipGL
  have hs : {g : Module.End F (Fin d → F) | IsUnit g} =
      Set.range fun x : GL (Fin d) F => Matrix.toLin' (x : Matrix (Fin d) (Fin d) F) := by
    ext g
    exact extZero_isUnit_iff g
  rw [hs, finsum_mem_range extZero_toLin_injective]
end GlobalTheory.CuspGL
