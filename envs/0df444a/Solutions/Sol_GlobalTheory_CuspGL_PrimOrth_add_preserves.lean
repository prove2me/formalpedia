-- Prove2me | solution 1 for GlobalTheory.CuspGL.PrimOrth.add_preserves
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:11:14.8551+00:00
-- url     : https://prove2.me/submissions/a5867874-06c6-418e-b7ce-9d5de26c3380

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_InvertibleEndomorphismInnerProductPrimitiveMobiu

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
theorem _root_.solution {A : Submodule F V} {g h : Module.End F V} (hh : h ∈ nilRad A)
    (hg : ∀ x ∈ A, g x ∈ A) : ∀ x ∈ A, (g + h) x ∈ A :=
  fun x hx => A.add_mem (hg x hx) (hh.1 x)
end GlobalTheory.CuspGL.PrimOrth
