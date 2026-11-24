-- Prove2me | solution 1 for GlobalTheory.HodgeDomain.hodge_moeb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T18:59:25.005969+00:00
-- url     : https://prove2.me/submissions/adbc3db1-421b-4463-81d8-884148007a3c

import Mathlib
import Definitions.Def_Formalism_DegreeFormula_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_HPInvEqForm
import Theorems.Thm_GlobalTheory_HodgeDomain_hQ_moeb
import Theorems.Thm_GlobalTheory_HodgeDomain_hP_inv_moeb
import Theorems.Thm_GlobalTheory_HodgeDomain_autE_blkMet

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
theorem _root_.solution (c : ℝ) {g : GL (Fin p ⊕ Fin q) ℂ} (hg : g ∈ Upq p q) {z : Matrix (Fin p) (Fin q) ℂ}
    (hz : z ∈ hcDom p q) :
    (autE g z)ᴴ * hodge c (moeb (g : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) z) * autE g z = hodge c z := by
  unfold hodge
  rw [autE_blkMet]
  simp only [Matrix.mul_smul, Matrix.smul_mul]
  rw [hP_inv_moeb hg hz, hQ_moeb hg hz]
end GlobalTheory.HodgeDomain
