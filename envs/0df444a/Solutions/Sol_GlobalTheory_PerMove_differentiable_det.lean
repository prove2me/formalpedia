-- Prove2me | solution 1 for GlobalTheory.PerMove.differentiable_det
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T19:19:59.296059+00:00
-- url     : https://prove2.me/submissions/e6041575-21ac-4a48-8967-7e03dd0289da

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_DetSubUpper
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_DetOfTriangular

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
open GlobalTheory GlobalTheory.PerMove
open scoped ComplexConjugate
open NumberField Matrix
open scoped nonZeroDivisors
open scoped ComplexConjugate
namespace GlobalTheory.PerMove
namespace _root_.GlobalTheory.PerMove
theorem _root_.solution {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X] {r : ℕ}
    (M : X → Matrix (Fin r) (Fin r) ℂ) (hM : ∀ a b, Differentiable ℂ fun x => M x a b) :
    Differentiable ℂ fun x => (M x).det := by
  simp only [Matrix.det_apply]
  fun_prop
end _root_.GlobalTheory.PerMove
end GlobalTheory.PerMove
