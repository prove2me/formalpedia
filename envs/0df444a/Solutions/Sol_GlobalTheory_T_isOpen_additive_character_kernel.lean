-- Prove2me | solution 1 for GlobalTheory.T.isOpen_additive_character_kernel
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T21:16:01.525639+00:00
-- url     : https://prove2.me/submissions/93afbc71-88eb-49cd-ba0e-3bf52d25c058

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_IsOpenAdditiveCharacterKernel
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_IsOpenAdditiveCharacterKernelStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_LocalFieldChar_isOpen_addChar_ker


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle), Continuous ψ → IsOpen {x : k | ψ x = 1} := by
  first | exact @GlobalTheory.CompanionTheory.LocalFieldChar.isOpen_addChar_ker | exact GlobalTheory.CompanionTheory.LocalFieldChar.isOpen_addChar_ker | (intros; apply GlobalTheory.CompanionTheory.LocalFieldChar.isOpen_addChar_ker <;> assumption)
end _root_.GlobalTheory.T
