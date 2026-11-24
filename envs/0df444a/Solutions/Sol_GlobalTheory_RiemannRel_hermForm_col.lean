-- Prove2me | solution 1 for GlobalTheory.RiemannRel.hermForm_col
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:07:19.342941+00:00
-- url     : https://prove2.me/submissions/d34dcf5a-47b8-470f-96a7-ca64674a5a88

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_DifferentiableOnLeftInverse
import Theorems.Thm_GlobalTheory_RiemannRel_hermForm_mulVec

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
theorem _root_.solution (G A B : Matrix (Fin g) (Fin g) ℂ) (j k : Fin g) :
    _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm G (A *ᵥ Pi.single j 1) (B *ᵥ Pi.single k 1) = (Aᵀ * G * B.map (starRingEnd ℂ)) j k := by
  rw [_root_.GlobalTheory.RiemannRel.hermForm_mulVec]; simp [Pi.star_single]
end _root_.GlobalTheory.RiemannRel
end GlobalTheory.RiemannRel
