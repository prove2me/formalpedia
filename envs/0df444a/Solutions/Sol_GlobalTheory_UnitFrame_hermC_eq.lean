-- Prove2me | solution 1 for GlobalTheory.UnitFrame.hermC_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T21:49:59.237872+00:00
-- url     : https://prove2.me/submissions/9d06c67f-008d-4070-a1bb-a903c94b0d8c

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_MemIffConjugateNotMem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Matrix
open scoped nonZeroDivisors ComplexConjugate
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.UnitFrame
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
open NumberField Matrix
open scoped nonZeroDivisors ComplexConjugate
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
omit [NumberField E] [IsCMField E]
namespace GlobalTheory.UnitFrame
namespace _root_.GlobalTheory.UnitFrame
theorem _root_.solution {r : ℕ} (τ : E →+* ℂ)
    (G : Matrix (Fin r) (Fin r) E) (u v : Fin r → ℂ) :
    _root_.ReciprocityTheory.ChartRestriction.G.FD.hermC τ G u v = u ⬝ᵥ (G.map τ) *ᵥ (star v) := by
  simp [_root_.ReciprocityTheory.ChartRestriction.G.FD.hermC, dotProduct, mulVec, Finset.mul_sum, mul_assoc]
end _root_.GlobalTheory.UnitFrame
end GlobalTheory.UnitFrame
