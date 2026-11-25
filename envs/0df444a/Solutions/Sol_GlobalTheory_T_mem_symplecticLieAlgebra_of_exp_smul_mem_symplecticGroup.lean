-- Prove2me | solution 1 for GlobalTheory.T.mem_symplecticLieAlgebra_of_exp_smul_mem_symplecticGroup
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T18:23:20.386637+00:00
-- url     : https://prove2.me/submissions/8d0c7a54-3219-4b93-8b1f-56eb886edcb1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_MemSymplecticLieAlgebraOfExpSmulMemSymplecticGro
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_MemSymplecticLieAlgebraOfExpSmulMemSymplecticGroStatement
import Theorems.Thm_GlobalTheory_RealWeil_mem_sp_of_exp_mem_symplecticGroup


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped Matrix
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (l : Type) [Fintype l] [DecidableEq l] (X : Matrix (l ⊕ l) (l ⊕ l) ℝ), (∀ t : ℝ, NormedSpace.exp (t • X) ∈ Matrix.symplecticGroup l ℝ) → X ∈ LieAlgebra.Symplectic.sp l ℝ := by
  first | exact @GlobalTheory.RealWeil.mem_sp_of_exp_mem_symplecticGroup | exact GlobalTheory.RealWeil.mem_sp_of_exp_mem_symplecticGroup | (intros; apply GlobalTheory.RealWeil.mem_sp_of_exp_mem_symplecticGroup <;> assumption)
end _root_.GlobalTheory.T
