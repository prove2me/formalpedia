-- Prove2me | solution 1 for GlobalTheory.AdaptedDet.norm_one_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T11:54:16.622549+00:00
-- url     : https://prove2.me/submissions/24b3eaeb-1e2e-4d9d-bab0-a4815d4c800f

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_IsIntegralDetSubOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsHermCoordOfDatum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_FinrankEqOfInjectiveOfSpan
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_CmUnitPowFourIdempotentModEight

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
open GlobalTheory GlobalTheory.AdaptedDet
namespace GlobalTheory.AdaptedDet
theorem _root_.solution {E : Type} [Field E] [NumberField E] (n : ℕ) (y : 𝓞 E) :
    ((Algebra.norm ℤ (1 + n * y : 𝓞 E) : ℤ) : ZMod n) = 1 := by
  classical
  rw [Algebra.norm_eq_matrix_det (RingOfIntegers.basis E), map_add, map_one, ← nsmul_eq_mul,
    map_nsmul, ← eq_intCast (Int.castRingHom (ZMod n)), RingHom.map_det, map_add, map_one,
    map_nsmul]
  have : n • (Int.castRingHom (ZMod n)).mapMatrix
      (Algebra.leftMulMatrix (RingOfIntegers.basis E) y) = 0 := by
    ext i j
    simp
  rw [this, add_zero, det_one]
end GlobalTheory.AdaptedDet
