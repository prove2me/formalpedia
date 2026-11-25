-- Prove2me | solution 1 for GlobalTheory.PerMove.hermC_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T18:03:08.156981+00:00
-- url     : https://prove2.me/submissions/387c4c41-38ea-40e8-aea3-f20df36f34c5

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
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
omit [NumberField E] [IsCMField E]
namespace GlobalTheory.PerMove
theorem _root_.solution (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (u w : Fin r → ℂ) :
    FD.hermC τ G u w = u ⬝ᵥ (G.map τ *ᵥ star w) := by
  simp [FD.hermC, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]
end GlobalTheory.PerMove
