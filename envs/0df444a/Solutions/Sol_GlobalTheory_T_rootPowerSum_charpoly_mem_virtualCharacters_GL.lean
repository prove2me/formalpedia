-- Prove2me | solution 1 for GlobalTheory.T.rootPowerSum_charpoly_mem_virtualCharacters_GL
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T06:13:22.635927+00:00
-- url     : https://prove2.me/submissions/22ac9678-d43f-4e99-8a70-c81294cbf7f9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_RootPowerSumCharpolyMemVirtualCharactersGL
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_AbByPOfComm
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_RootPowerSumCharpolyMemVirtualCharactersGLStatement
import Theorems.Thm_GlobalTheory_CuspGL_rootSum_charpoly_mem_virt


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (F : Type) [Field F] [Finite F] (θ : AlgebraicClosure F →* ℂ), (∀ x y : AlgebraicClosure F, x ≠ 0 → y ≠ 0 → θ x = θ y → x = y) → ∀ n k : ℕ, (fun x : GL (Fin n) F => rootSum θ k (Matrix.charpoly (x : Matrix (Fin n) (Fin n) F))) ∈ Virt ℂ ℂ (GL (Fin n) F) := by
  first | exact @GlobalTheory.CuspGL.rootSum_charpoly_mem_virt | exact GlobalTheory.CuspGL.rootSum_charpoly_mem_virt | (intros; apply GlobalTheory.CuspGL.rootSum_charpoly_mem_virt <;> assumption)
end _root_.GlobalTheory.T
