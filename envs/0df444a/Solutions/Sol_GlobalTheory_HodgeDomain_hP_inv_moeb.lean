-- Prove2me | solution 1 for GlobalTheory.HodgeDomain.hP_inv_moeb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T18:43:51.027357+00:00
-- url     : https://prove2.me/submissions/57479477-0222-4d75-b73f-9c96cdf3f158

import Mathlib
import Definitions.Def_Formalism_DegreeFormula_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_HPInvEqForm
import Theorems.Thm_GlobalTheory_HodgeDomain_hP_moeb
import Theorems.Thm_GlobalTheory_HodgeDomain_jW_isUnit

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
    (jW g z)ᴴ * (hP (moeb (g : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) z))⁻¹ * jW g z = (hP z)⁻¹ := by
  have hu := jW_isUnit hg hz
  have hu' : IsUnit (jW g z)ᴴ.det := by rw [det_conjTranspose]; exact hu.star
  rw [← hP_moeb hg hz, Matrix.mul_inv_rev, Matrix.mul_inv_rev, Matrix.mul_nonsing_inv_cancel_left _ _ hu',
    Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hu, Matrix.mul_one]
end GlobalTheory.HodgeDomain
