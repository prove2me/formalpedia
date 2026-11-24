-- Prove2me | solution 1 for GlobalTheory.FrameFibre.eq_zero_of_trace
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:11:57.545359+00:00
-- url     : https://prove2.me/submissions/7e170230-171f-4510-9c67-2ee5a535450b

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_HermFormConjDiag
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_FrameOfPeriodLinear
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_DetOfTriangular
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsEqNsmulOfDvdPairing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsLevelBlockOfEq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory NumberField Matrix
open scoped nonZeroDivisors
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.FrameFibre
variable {E : Type} [Field E] [NumberField E] {r : ℕ}
namespace GlobalTheory.FrameFibre
theorem _root_.solution (t : E) (ht : ∀ a : 𝓞 E, Algebra.trace ℚ E ((a : E) * t) = 0) : t = 0 := by
  refine (traceForm_nondegenerate ℚ E).1 t fun e => ?_
  have halg : IsAlgebraic ℤ e :=
    (IsFractionRing.isAlgebraic_iff ℤ ℚ E).2 (Algebra.IsAlgebraic.isAlgebraic _)
  obtain ⟨k, hk, hki⟩ := halg.exists_integral_multiple
  have h : Algebra.trace ℚ E ((k • e) * t) = 0 := ht ⟨k • e, hki⟩
  rw [smul_mul_assoc, map_zsmul, smul_eq_zero] at h
  rw [Algebra.traceForm_apply, mul_comm]
  exact h.resolve_left hk
end GlobalTheory.FrameFibre
