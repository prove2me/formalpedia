-- Prove2me | solution 1 for GlobalTheory.HodgeDomain.autE_isUnit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T18:43:51.068642+00:00
-- url     : https://prove2.me/submissions/9d99e415-cebf-41e5-8b9e-5d5bb8add51b

import Mathlib
import Definitions.Def_Formalism_DegreeFormula_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_HPInvEqForm
import Theorems.Thm_GlobalTheory_HodgeDomain_kapQ_isUnit
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
    (hz : z ∈ hcDom p q) : IsUnit (autE g z).det := by
  unfold autE
  rw [det_fromBlocks_zero₁₂]
  exact (jW_isUnit hg hz).mul (kapQ_isUnit hg hz)
end GlobalTheory.HodgeDomain
