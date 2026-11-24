-- Prove2me | solution 1 for GlobalTheory.DetIdeal.map_vol
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T14:23:40.286301+00:00
-- url     : https://prove2.me/submissions/014e6bbc-3e93-4280-99d4-de9f5b63f283

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
theorem _root_.solution {R : Type} [CommRing R] {r : ℕ} (L : Set (Fin r → R)) (f : R →+* R) :
    (vol L).map f = vol ((fun x => f ∘ x) '' L) := by
  unfold vol
  rw [Ideal.map_span]
  congr 1
  ext d
  constructor
  · rintro ⟨_, ⟨Y, hY, rfl⟩, rfl⟩
    exact ⟨Y.map f, fun i => ⟨Y i, hY i, rfl⟩, (RingHom.map_det f Y).symm⟩
  · rintro ⟨Y, hY, rfl⟩
    choose X hX hXY using hY
    refine ⟨(Matrix.of X).det, ⟨Matrix.of X, hX, rfl⟩, ?_⟩
    rw [RingHom.map_det]
    congr 1
    ext i j
    exact congrFun (hXY i) j
end GlobalTheory.DetIdeal
