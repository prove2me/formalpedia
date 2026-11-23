-- Prove2me | solution 1 for GlobalTheory.BoundedBasis.herm_vecMul_left
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:25:28.85987+00:00
-- url     : https://prove2.me/submissions/4fbc0f50-c13b-4019-8341-fa324fbd3c37

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_IntegerApproximationCountHolds
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ExistsFinsetTypesOfBoundedBases
import Theorems.Thm_GlobalTheory_BoundedBasis_herm_eq_dotProduct
import Theorems.Thm_GlobalTheory_BoundedBasis_gramOf_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Matrix Module
open ReciprocityTheory.ChartRestriction.G.FD
open GlobalTheory
open GlobalTheory.BoundedBasis
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
namespace GlobalTheory.BoundedBasis
theorem _root_.solution (G : Matrix (Fin r) (Fin r) E) (v : Fin r → Fin r → E) (c : Fin r → E)
    (k : Fin r) : herm G (c ᵥ* Matrix.of v) (v k) = (c ᵥ* gramOf G v) k := by
  rw [gramOf_eq, ← vecMul_vecMul, ← vecMul_vecMul, herm_eq_dotProduct]
  rfl
end GlobalTheory.BoundedBasis
