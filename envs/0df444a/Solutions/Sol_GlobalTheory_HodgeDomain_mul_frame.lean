-- Prove2me | solution 1 for GlobalTheory.HodgeDomain.mul_frame
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:49:45.541957+00:00
-- url     : https://prove2.me/submissions/15028931-6634-49a2-bf54-d7747c623b6c

import Mathlib
import Definitions.Def_Formalism_DegreeFormula_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_HPInvEqForm
import Theorems.Thm_GlobalTheory_HodgeDomain_moeb_mul_kapQ

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
theorem _root_.solution {g : GL (Fin p ⊕ Fin q) ℂ} (hg : g ∈ Upq p q) {z : Matrix (Fin p) (Fin q) ℂ}
    (hz : z ∈ hcDom p q) :
    (g : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) * fromBlocks 1 z 0 1 =
      fromBlocks 1 (moeb (g : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) z) 0 1 *
        fromBlocks (jW g z) 0 (g : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ).toBlocks₂₁ (kapQ g z) := by
  have e := moeb_mul_kapQ hg hz
  unfold jW
  conv_lhs => rw [← fromBlocks_toBlocks (g : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ)]
  rw [fromBlocks_multiply, fromBlocks_multiply]
  simp only [Matrix.one_mul, Matrix.mul_one, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, e, sub_add_cancel]
  rfl
end GlobalTheory.HodgeDomain
