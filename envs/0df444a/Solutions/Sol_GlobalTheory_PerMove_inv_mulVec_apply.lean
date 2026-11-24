-- Prove2me | solution 1 for GlobalTheory.PerMove.inv_mulVec_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T19:21:18.592584+00:00
-- url     : https://prove2.me/submissions/471510fe-0aa5-439a-81d4-34161acf88a8

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
theorem _root_.solution {r : ℕ} (A : Matrix (Fin r) (Fin r) ℂ) (w : Fin r → ℂ) (a : Fin r) :
    (A⁻¹ *ᵥ w) a = (A.det)⁻¹ * (A.updateCol a w).det := by
  rw [Matrix.inv_def, Matrix.smul_mulVec, Pi.smul_apply, smul_eq_mul, Ring.inverse_eq_inv',
    ← Matrix.cramer_eq_adjugate_mulVec, Matrix.cramer_apply]
end _root_.GlobalTheory.PerMove
end GlobalTheory.PerMove
