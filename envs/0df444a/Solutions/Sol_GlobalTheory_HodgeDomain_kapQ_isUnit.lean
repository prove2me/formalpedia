-- Prove2me | solution 1 for GlobalTheory.HodgeDomain.kapQ_isUnit
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:13:47.411798+00:00
-- url     : https://prove2.me/submissions/b99c118d-5887-4b8b-b59a-6ec478e26bd7

import Mathlib
import Definitions.Def_Formalism_DegreeFormula_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_HPInvEqForm
import Theorems.Thm_GlobalTheory_HodgeDomain_kapQ_gram

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
    (hz : z ∈ hcDom p q) : IsUnit (kapQ g z).det := by
  have h1 := kapQ_gram hg z
  have hpd : ((kapQ g z)ᴴ * kapQ g z).PosDef := by
    rw [eq_add_of_sub_eq h1]
    exact Matrix.PosDef.add_posSemidef (by exact hz) (posSemidef_conjTranspose_mul_self _)
  rw [isUnit_iff_ne_zero]
  intro h0
  have := hpd.det_pos
  rw [det_mul, det_conjTranspose, h0, mul_zero] at this
  exact lt_irrefl _ this
end GlobalTheory.HodgeDomain
