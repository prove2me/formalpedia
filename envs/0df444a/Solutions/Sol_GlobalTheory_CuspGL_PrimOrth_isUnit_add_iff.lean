-- Prove2me | solution 1 for GlobalTheory.CuspGL.PrimOrth.isUnit_add_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T14:22:11.650143+00:00
-- url     : https://prove2.me/submissions/efaf8793-da0a-4978-86e7-9f622aad9de4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_InvertibleEndomorphismInnerProductPrimitiveMobiu
import Theorems.Thm_GlobalTheory_CuspGL_PrimOrth_neg_mem_nilRad
import Theorems.Thm_GlobalTheory_CuspGL_PrimOrth_add_preserves
import Theorems.Thm_GlobalTheory_CuspGL_PrimOrth_isUnit_add

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
theorem _root_.solution [FiniteDimensional F V] {A : Submodule F V} {g h : Module.End F V} (hh : h ∈ nilRad A)
    (hg : ∀ x ∈ A, g x ∈ A) : IsUnit (g + h) ↔ IsUnit g := by
  refine ⟨fun H => ?_, isUnit_add hh hg⟩
  have := isUnit_add (neg_mem_nilRad hh) (add_preserves hh hg) H
  simpa using this
end GlobalTheory.CuspGL.PrimOrth
