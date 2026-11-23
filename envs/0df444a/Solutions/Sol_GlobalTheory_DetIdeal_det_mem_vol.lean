-- Prove2me | solution 1 for GlobalTheory.DetIdeal.det_mem_vol
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:08:39.07202+00:00
-- url     : https://prove2.me/submissions/d687aa8e-321a-4397-a8c1-1f77624ae788

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
variable {R K : Type} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K] {r : ℕ}
namespace GlobalTheory.DetIdeal
theorem _root_.solution {R : Type} [CommRing R] {r : ℕ} {L : Set (Fin r → R)} {Y : Matrix (Fin r) (Fin r) R}
    (hY : ∀ i, Y i ∈ L) : Y.det ∈ vol L :=
  Ideal.subset_span ⟨Y, hY, rfl⟩
end GlobalTheory.DetIdeal
