-- Prove2me | solution 1 for GlobalTheory.RiemannRel.of_cols_mulVec
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:17:04.687382+00:00
-- url     : https://prove2.me/submissions/d9849f25-cb31-4797-88bc-6b5a57950573

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_DifferentiableOnLeftInverse

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Matrix
open scoped nonZeroDivisors
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.RiemannRel
variable {g : ℕ}
open NumberField Matrix
open scoped nonZeroDivisors
variable {g : ℕ}
namespace GlobalTheory.RiemannRel
namespace _root_.GlobalTheory.RiemannRel
theorem _root_.solution (c : Fin g → Fin g → ℂ) (k : Fin g) :
    (Matrix.of fun i j => c j i) *ᵥ Pi.single k 1 = c k := by
  ext i; simp [mulVec, dotProduct, Pi.single_apply]
end _root_.GlobalTheory.RiemannRel
end GlobalTheory.RiemannRel
