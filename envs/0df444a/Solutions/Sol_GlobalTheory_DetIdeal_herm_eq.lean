-- Prove2me | solution 1 for GlobalTheory.DetIdeal.herm_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T14:23:39.426727+00:00
-- url     : https://prove2.me/submissions/c2d1d587-3322-4be2-9bbd-3188ea51cbd6

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_FinrankEqOfInjectiveOfSpan
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_DetMulVolMulConj

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
open GlobalTheory GlobalTheory.DetIdeal
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
namespace GlobalTheory.DetIdeal
theorem _root_.solution (G : Matrix (Fin r) (Fin r) E) (x y : Fin r → E) :
    FD.herm G x y = x ⬝ᵥ G *ᵥ (fun b => FD.cc (y b)) := by
  simp [FD.herm, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]
end GlobalTheory.DetIdeal
