-- Prove2me | solution 1 for GlobalTheory.RootExchangeFixed.vol_ball
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T20:07:15.544414+00:00
-- url     : https://prove2.me/submissions/a044910b-0ecb-4125-b4a2-8e81849d12d1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_NonarchimedeanLocalFieldSecondCountableT2Space
import Theorems.Thm_GlobalTheory_RootExchangeFixed_nonarchimedeanLocalField_secondCountable_t2Space
import Theorems.Thm_GlobalTheory_RootExchangeFixed_ball_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx
open scoped Pointwise
open GlobalTheory GlobalTheory.RootExchangeFixed
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable [MeasurableSpace k] [BorelSpace k]
namespace GlobalTheory.RootExchangeFixed
theorem _root_.solution (ν : Measure k) (hν : IsUnitVol ν) (s : kˣ) :
    ν {x : k | valuation k x ≤ valuation k (s : k)} = ENNReal.ofReal (nabs k s) := by
  haveI := hν.1
  obtain ⟨_, _⟩ := nonarchimedeanLocalField_secondCountable_t2Space (k := k)
  rw [ball_eq, ← distribHaarChar_mul ν s, hν.2, nabs]
  simp
end GlobalTheory.RootExchangeFixed
