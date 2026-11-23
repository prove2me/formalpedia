-- Prove2me | solution 1 for GlobalTheory.MultiHilbert.eval_aeval_coord
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:23:04.98445+00:00
-- url     : https://prove2.me/submissions/87b1779f-7f3a-47a8-914d-da22fcd5ba1d

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsMultigradedHilbertPoly
import Theorems.Thm_GlobalTheory_MultiHilbert_EventuallyPoly_add

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.MultiHilbert
open MvPolynomial
variable {r : ℕ}
namespace GlobalTheory.MultiHilbert
theorem _root_.solution (x : Fin r → ℚ) (p : Fin r → MvPolynomial (Fin r) ℚ)
    (Φ : MvPolynomial (Fin r) ℚ) :
    eval x (aeval p Φ) = eval (fun k => eval x (p k)) Φ := by
  induction Φ using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p n hp => simp only [map_mul, hp, aeval_X, eval_X]
end GlobalTheory.MultiHilbert
