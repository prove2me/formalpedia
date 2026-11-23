-- Prove2me | solution 1 for GlobalTheory.CuspGL.PrimOrth.neg_mem_nilRad
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:34:14.418952+00:00
-- url     : https://prove2.me/submissions/8c9e4c04-35ed-494c-92de-139d9e7815c0

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
theorem _root_.solution {A : Submodule F V} {h : Module.End F V} (hh : h ∈ nilRad A) : -h ∈ nilRad A :=
  ⟨fun x => by simpa using hh.1 x, fun x hx => by simpa using hh.2 x hx⟩
end GlobalTheory.CuspGL.PrimOrth
