-- Prove2me | solution 1 for GlobalTheory.HodgeDomain.jW_isUnit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T18:28:25.394808+00:00
-- url     : https://prove2.me/submissions/fc1c1ad5-caef-4332-a6dd-b12806019561

import Mathlib
import Definitions.Def_Formalism_DegreeFormula_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_HPInvEqForm
import Theorems.Thm_GlobalTheory_HodgeDomain_moeb_mem
import Theorems.Thm_GlobalTheory_HodgeDomain_hP_moeb
import Theorems.Thm_GlobalTheory_HodgeDomain_hP_posDef

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
    (hz : z ∈ hcDom p q) : IsUnit (jW g z).det := by
  rw [isUnit_iff_ne_zero]
  intro h0
  have h := (hP_posDef (moeb_mem hg hz)).det_pos
  rw [← hP_moeb hg hz, det_mul, det_mul, det_conjTranspose, h0] at h
  simp at h
end GlobalTheory.HodgeDomain
