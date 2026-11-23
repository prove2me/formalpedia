-- Prove2me | solution 1 for GlobalTheory.HodgeDomain.hP_mul_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:03:35.56536+00:00
-- url     : https://prove2.me/submissions/4f3d676f-a974-4ffb-994d-269a006866df

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
theorem _root_.solution {z : Matrix (Fin p) (Fin q) ℂ} (hz : z ∈ hcDom p q) :
    hP z * (1 + z * (hQ z)⁻¹ * zᴴ) = 1 := by
  have hpd : (hQ z).PosDef := hz
  have hu : IsUnit (hQ z).det := isUnit_iff_ne_zero.mpr hpd.det_pos.ne'
  have key : z * (hQ z * (hQ z)⁻¹) * zᴴ = z * zᴴ := by rw [Matrix.mul_nonsing_inv _ hu, Matrix.mul_one]
  generalize (hQ z)⁻¹ = R at key ⊢
  unfold hQ at key
  unfold hP
  simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one,
    Matrix.mul_assoc] at key ⊢
  rw [← key]
  abel
end GlobalTheory.HodgeDomain
