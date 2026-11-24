-- Prove2me | solution 1 for GlobalTheory.CuspGL.PrimOrth.add_preserves_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T14:04:07.129543+00:00
-- url     : https://prove2.me/submissions/7a35b3b5-2dc9-4523-8b0f-a43d064fd717

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_InvertibleEndomorphismInnerProductPrimitiveMobiu
import Theorems.Thm_GlobalTheory_CuspGL_PrimOrth_neg_mem_nilRad
import Theorems.Thm_GlobalTheory_CuspGL_PrimOrth_add_preserves

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial GlobalTheory.CuspGL
open GlobalTheory GlobalTheory.CuspGL GlobalTheory.CuspGL.PrimOrth
variable {F : Type} [Field F] {V : Type} [AddCommGroup V] [Module F V]
namespace GlobalTheory.CuspGL.PrimOrth
theorem _root_.solution {A : Submodule F V} {g h : Module.End F V} (hh : h ∈ nilRad A) :
    (∀ x ∈ A, (g + h) x ∈ A) ↔ ∀ x ∈ A, g x ∈ A := by
  refine ⟨fun H => ?_, add_preserves hh⟩
  have := add_preserves (neg_mem_nilRad hh) H
  simpa using this
end GlobalTheory.CuspGL.PrimOrth
