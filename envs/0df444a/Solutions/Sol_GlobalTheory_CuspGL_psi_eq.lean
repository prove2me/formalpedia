-- Prove2me | solution 1 for GlobalTheory.CuspGL.psi_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T14:23:39.670953+00:00
-- url     : https://prove2.me/submissions/0083ecd5-5af1-4d1d-b7c1-5517fb483dc8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Theorems.Thm_GlobalTheory_CuspGL_invariantSubspaceMobiusInverseRec_succ
import Theorems.Thm_GlobalTheory_CuspGL_invariantSubspaceMobiusInverseRec_eq_of_finrank_lt

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
theorem _root_.solution (s : F[X] → ℂ) (V : Type) [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (g : Module.End F V) :
    psi s V g = s (LinearMap.charpoly g) -
      ∑ᶠ W : {W : Submodule F V // W ≠ ⊤ ∧ ∀ x ∈ W, g x ∈ W}, psi s W.1 (g.restrict W.2.2) := by
  rw [psi, invariantSubspaceMobiusInverseRec_succ]
  congr 1
  refine finsum_congr fun W => ?_
  have := Submodule.finrank_lt W.2.1
  exact invariantSubspaceMobiusInverseRec_eq_of_finrank_lt s _ (Module.finrank F W.1 + 1) _ _ (by omega) (by omega)
end GlobalTheory.CuspGL
