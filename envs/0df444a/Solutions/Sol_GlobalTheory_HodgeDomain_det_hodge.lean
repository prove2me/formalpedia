-- Prove2me | solution 1 for GlobalTheory.HodgeDomain.det_hodge
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T17:36:07.385556+00:00
-- url     : https://prove2.me/submissions/696dbf9b-7bc3-4cc6-a0e0-7dbbdca9b33b

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
theorem _root_.solution (c : ℝ) {z : Matrix (Fin p) (Fin q) ℂ} (hz : z ∈ hcDom p q) :
    (hodge c z).det = (c : ℂ) ^ (p + q) := by
  unfold hodge blkMet
  have hdet : (hP z).det = (hQ z).det := Matrix.det_one_sub_mul_comm z zᴴ
  have hne : (hQ z).det ≠ 0 := (show (hQ z).PosDef from hz).det_pos.ne'
  rw [det_fromBlocks_zero₁₂, det_smul, det_smul, det_nonsing_inv, Fintype.card_fin, Fintype.card_fin, hdet,
    Ring.inverse_eq_inv', pow_add]
  field_simp
end GlobalTheory.HodgeDomain
