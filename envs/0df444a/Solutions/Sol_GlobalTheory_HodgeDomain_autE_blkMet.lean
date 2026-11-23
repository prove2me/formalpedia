-- Prove2me | solution 1 for GlobalTheory.HodgeDomain.autE_blkMet
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:08:25.016741+00:00
-- url     : https://prove2.me/submissions/e964aca8-8a09-409b-815f-373d49a18ed4

import Mathlib
import Definitions.Def_Formalism_DegreeFormula_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_HPInvEqForm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Formalism.DegreeFormula Formalism.MJ Formalism.UG
open scoped ComplexOrder
open GlobalTheory GlobalTheory.HodgeDomain
variable {p q : ℕ}
namespace GlobalTheory.HodgeDomain
theorem _root_.solution (g : GL (Fin p ⊕ Fin q) ℂ) (z : Matrix (Fin p) (Fin q) ℂ)
    (A : Matrix (Fin p) (Fin p) ℂ) (B : Matrix (Fin q) (Fin q) ℂ) :
    (autE g z)ᴴ * blkMet A B * autE g z =
      blkMet ((jW g z)ᴴ * A * jW g z) ((kapQ g z)ᴴ * B * kapQ g z) := by
  unfold autE blkMet
  rw [fromBlocks_conjTranspose, fromBlocks_multiply, fromBlocks_multiply]
  simp [Matrix.mul_assoc]
end GlobalTheory.HodgeDomain
