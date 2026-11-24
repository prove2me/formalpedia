-- Prove2me | solution 1 for GlobalTheory.JR.HermInv.unit_form
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T17:59:53.463805+00:00
-- url     : https://prove2.me/submissions/f881dd19-738f-4ab8-92c1-de009306bf52

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FourierMatch
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnitaryActionHermitianInvariantsTransitive
import Theorems.Thm_GlobalTheory_JR_HermInv_starU_mul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.HermInv
variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]
variable {r : ℕ}
namespace GlobalTheory.JR.HermInv
theorem _root_.solution (g : Matrix.unitaryGroup (Fin r) E) (v w : Fin r → E) :
    star (g.1 *ᵥ v) ⬝ᵥ (g.1 *ᵥ w) = star v ⬝ᵥ w := by
  rw [Matrix.star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, ← Matrix.star_eq_conjTranspose,
    starU_mul g, one_mulVec]
end GlobalTheory.JR.HermInv
