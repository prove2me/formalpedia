-- Prove2me | solution 1 for GlobalTheory.HodgeDomain.upq_right
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T17:54:00.37073+00:00
-- url     : https://prove2.me/submissions/6869031b-dd46-4b93-90c1-5b508fd2e64b

import Mathlib
import Definitions.Def_Formalism_DegreeFormula_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_HPInvEqForm
import Theorems.Thm_GlobalTheory_HodgeDomain_upq_iff
import Theorems.Thm_GlobalTheory_HodgeDomain_Jpq_sq

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
theorem _root_.solution {g : GL (Fin p ⊕ Fin q) ℂ} (hg : g ∈ Upq p q) :
    (g : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) * Jpq p q * (g : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ)ᴴ =
      Jpq p q := by
  have h := upq_iff.mp hg
  generalize (g : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) = G at h ⊢
  have h1 : (Jpq p q * Gᴴ * Jpq p q) * G = 1 := by
    rw [show Jpq p q * Gᴴ * Jpq p q * G = Jpq p q * (Gᴴ * Jpq p q * G) by simp only [Matrix.mul_assoc], h, Jpq_sq]
  have h2 : G * (Jpq p q * Gᴴ * Jpq p q) = 1 := by
    rw [← Matrix.inv_eq_left_inv h1]
    exact Matrix.mul_nonsing_inv _ (Matrix.isUnit_det_of_left_inverse h1)
  calc G * Jpq p q * Gᴴ = G * (Jpq p q * Gᴴ * Jpq p q) * Jpq p q := by
        simp only [Matrix.mul_assoc, Jpq_sq, Matrix.mul_one]
    _ = Jpq p q := by rw [h2, Matrix.one_mul]
end GlobalTheory.HodgeDomain
