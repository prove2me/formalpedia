-- Prove2me | solution 1 for GlobalTheory.DetIdeal.exists_denominator
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T14:19:28.903793+00:00
-- url     : https://prove2.me/submissions/b6b5a859-341e-49ae-b66f-998011c6aab9

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
variable {R K : Type} [CommRing R] [IsDomain R] [Field K] [Algebra R K] [IsFractionRing R K] {r : ℕ}
omit [IsDomain R]
namespace GlobalTheory.DetIdeal
theorem _root_.solution (M : Submodule R (Fin r → K)) (hM : M.FG) :
    ∃ n ∈ R⁰, ∀ v ∈ M, ∃ x : Fin r → R, algebraMap R K ∘ x = algebraMap R K n • v := by
  have hN : (⨆ i : Fin r, M.map (LinearMap.proj i : (Fin r → K) →ₗ[R] K)).FG :=
    Submodule.fg_iSup _ fun i => hM.map _
  obtain ⟨n, hn, hint⟩ := FractionalIdeal.isFractional_of_fg (S := R⁰) hN
  refine ⟨n, hn, fun v hv => ?_⟩
  have : ∀ i, ∃ x : R, algebraMap R K x = n • v i := fun i =>
    hint (v i) (Submodule.mem_iSup_of_mem i ⟨v, hv, rfl⟩)
  choose x hx using this
  exact ⟨x, funext fun i => by simp [hx, Algebra.smul_def]⟩
end GlobalTheory.DetIdeal
