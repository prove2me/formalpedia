-- Prove2me | solution 1 for GlobalTheory.MultiHilbert.eval_monomial_erase
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T19:00:45.740081+00:00
-- url     : https://prove2.me/submissions/a0f3f0ad-11fd-4dd9-b4b0-8fffc492cd60

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsMultigradedHilbertPoly

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
theorem _root_.solution (x : Fin r → ℚ) (k : Fin r) (t : ℚ) (d : Fin r →₀ ℕ) (c : ℚ) :
    eval (Function.update x k t) (monomial (d.erase k) c) = eval x (monomial (d.erase k) c) := by
  rw [eval_monomial, eval_monomial]
  congr 1
  refine Finsupp.prod_congr fun j hj => ?_
  have : j ≠ k := by
    rintro rfl
    simp at hj
  rw [Function.update_of_ne this]
end GlobalTheory.MultiHilbert
