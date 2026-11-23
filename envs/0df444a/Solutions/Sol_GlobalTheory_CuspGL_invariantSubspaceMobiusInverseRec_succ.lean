-- Prove2me | solution 1 for GlobalTheory.CuspGL.invariantSubspaceMobiusInverseRec_succ
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:05:35.835121+00:00
-- url     : https://prove2.me/submissions/f07ff0ea-03a7-440c-8baa-f47f573ad647

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
noncomputable section
open GlobalTheory GlobalTheory.CuspGL
variable {F : Type} [Field F]
namespace GlobalTheory.CuspGL
theorem _root_.solution (s : F[X] → ℂ) (n : ℕ) (V : Type) [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (g : Module.End F V) : invariantSubspaceMobiusInverseRec s (n + 1) V g = s (LinearMap.charpoly g) -
      ∑ᶠ W : {W : Submodule F V // W ≠ ⊤ ∧ ∀ x ∈ W, g x ∈ W}, invariantSubspaceMobiusInverseRec s n W.1 (g.restrict W.2.2) := rfl
end GlobalTheory.CuspGL
