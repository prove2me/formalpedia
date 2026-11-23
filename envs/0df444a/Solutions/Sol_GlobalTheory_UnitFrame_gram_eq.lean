-- Prove2me | solution 1 for GlobalTheory.UnitFrame.gram_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:17:05.083707+00:00
-- url     : https://prove2.me/submissions/ed86f919-1d5c-47b5-b15e-74d17bdbd56d

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
theorem _root_.solution {r : ℕ} (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E)
    (x : Matrix (Fin r) (Fin r) ℂ) :
    _root_.ReciprocityTheory.ChartRestriction.G.FD.gram τ G x = xᵀ * (G.map τ * x.map conj) := by
  ext a b
  simp [_root_.ReciprocityTheory.ChartRestriction.G.FD.gram, _root_.ReciprocityTheory.ChartRestriction.G.FD.hermC, _root_.ReciprocityTheory.ChartRestriction.G.FD.col, mul_apply, Finset.mul_sum, mul_assoc]
end _root_.GlobalTheory.UnitFrame
end GlobalTheory.UnitFrame
