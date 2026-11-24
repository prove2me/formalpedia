-- Prove2me | solution 1 for GlobalTheory.T.apply_charpoly_eq_finsum_psi_invariant_submodules
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T15:27:10.205578+00:00
-- url     : https://prove2.me/submissions/a519af5e-423a-4565-bcb8-91c50e1c39a6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_CharpolyEqFinsumPsi
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_CharpolyEqFinsumPsiStatement
import Theorems.Thm_GlobalTheory_CuspGL_charpoly_eq_finsum_psi


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
theorem _root_.solution : ∀ (F : Type) [Field F] [Finite F] (V : Type) [AddCommGroup V] [Module F V] [FiniteDimensional F V] (s : F[X] → ℂ) (g : Module.End F V), s (LinearMap.charpoly g) = ∑ᶠ W : {W : Submodule F V // ∀ x ∈ W, g x ∈ W}, psi s W.1 (g.restrict W.2) := by
  first | exact @GlobalTheory.CuspGL.charpoly_eq_finsum_psi | exact GlobalTheory.CuspGL.charpoly_eq_finsum_psi | (intros; apply GlobalTheory.CuspGL.charpoly_eq_finsum_psi <;> assumption)
end _root_.GlobalTheory.T
