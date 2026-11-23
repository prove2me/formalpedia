-- Prove2me | solution 1 for GlobalTheory.HodgeDomain.hP_posDef
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:10:28.294799+00:00
-- url     : https://prove2.me/submissions/1b5aa664-933d-4bba-a36e-3550c4babd8a

import Mathlib
import Definitions.Def_Formalism_DegreeFormula_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_HPInvEqForm
import Theorems.Thm_GlobalTheory_HodgeDomain_hP_mul_eq_one
import Theorems.Thm_GlobalTheory_HodgeDomain_hP_inv_posDef

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
theorem _root_.solution {z : Matrix (Fin p) (Fin q) ℂ} (hz : z ∈ hcDom p q) : (hP z).PosDef := by
  have hu : IsUnit (hP z).det := Matrix.isUnit_det_of_right_inverse (hP_mul_eq_one hz)
  have h := (hP_inv_posDef hz).inv
  rwa [Matrix.nonsing_inv_nonsing_inv _ hu] at h
end GlobalTheory.HodgeDomain
