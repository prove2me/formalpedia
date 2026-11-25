-- Prove2me | solution 1 for GlobalTheory.HodgeDomain.hodge_posDef
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:49:41.951001+00:00
-- url     : https://prove2.me/submissions/bbc57f3e-6f1b-4a5d-b31d-d46d9f37ca7d

import Mathlib
import Definitions.Def_Formalism_DegreeFormula_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_HPInvEqForm
import Theorems.Thm_GlobalTheory_HodgeDomain_hP_inv_posDef
import Theorems.Thm_GlobalTheory_HodgeDomain_blkMet_posDef

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
theorem _root_.solution {c : ℝ} (hc : 0 < c) {z : Matrix (Fin p) (Fin q) ℂ} (hz : z ∈ hcDom p q) :
    (hodge c z).PosDef := by
  unfold hodge
  have hc' : (0 : ℂ) < (c : ℂ) := Complex.zero_lt_real.mpr hc
  exact blkMet_posDef ((hP_inv_posDef hz).smul hc') ((show (hQ z).PosDef from hz).smul hc')
end GlobalTheory.HodgeDomain
