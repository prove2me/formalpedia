-- Prove2me | solution 1 for GlobalTheory.HodgeDomain.hP_inv_posDef
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:08:23.004845+00:00
-- url     : https://prove2.me/submissions/2beedd35-a0b6-47f7-b244-2c4fff885b2b

import Mathlib
import Definitions.Def_Formalism_DegreeFormula_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_HPInvEqForm
import Theorems.Thm_GlobalTheory_HodgeDomain_hP_mul_eq_one

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
theorem _root_.solution {z : Matrix (Fin p) (Fin q) ℂ} (hz : z ∈ hcDom p q) : (hP z)⁻¹.PosDef := by
  have e : (hP z)⁻¹ = 1 + z * (hQ z)⁻¹ * zᴴ := Matrix.inv_eq_right_inv (hP_mul_eq_one hz)
  rw [e]
  have hq : (hQ z).PosDef := hz
  exact Matrix.PosDef.one.add_posSemidef (hq.inv.posSemidef.mul_mul_conjTranspose_same z)
end GlobalTheory.HodgeDomain
