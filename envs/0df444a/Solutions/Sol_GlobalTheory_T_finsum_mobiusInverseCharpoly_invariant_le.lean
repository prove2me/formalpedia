-- Prove2me | solution 1 for GlobalTheory.T.finsum_mobiusInverseCharpoly_invariant_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T21:09:35.332457+00:00
-- url     : https://prove2.me/submissions/7eae2fa7-ed0a-43bd-9684-4a722cfb985d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_FinsumMobiusInverseCharpolyInvariantLe
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_FinsumMobiusInverseCharpolyInvariantLeStatement
import Theorems.Thm_GlobalTheory_CuspGL_finsum_psi_le


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial GlobalTheory.CuspGL
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (F : Type) [Field F] [Finite F] (V : Type) [AddCommGroup V] [Module F V] [FiniteDimensional F V] (s : F[X] → ℂ) (A : Submodule F V) (g : Module.End F V) (hg : ∀ x ∈ A, g x ∈ A), ∑ᶠ W : {W : Submodule F V // W ≤ A ∧ ∀ x ∈ W, g x ∈ W}, psi s W.1 (g.restrict W.2.2) = s (LinearMap.charpoly (g.restrict hg)) := by
  first | exact @GlobalTheory.CuspGL.finsum_psi_le | exact GlobalTheory.CuspGL.finsum_psi_le | (intros; apply GlobalTheory.CuspGL.finsum_psi_le <;> assumption)
end _root_.GlobalTheory.T
