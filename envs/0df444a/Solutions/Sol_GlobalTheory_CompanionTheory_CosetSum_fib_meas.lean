-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.CosetSum.fib_meas
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T12:26:12.054662+00:00
-- url     : https://prove2.me/submissions/611fe061-6b03-4b92-9233-1a010edc01b2

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CosetIntegralUnramified
import Theorems.Thm_GlobalTheory_CompanionTheory_CosetSum_fib_mk

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Set
open scoped ENNReal NNReal
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.CosetSum
variable {G : Type} [AddCommGroup G] [MeasurableSpace G] [MeasurableAdd G]
namespace GlobalTheory.CompanionTheory.CosetSum
theorem _root_.solution (H : AddSubgroup G) (hm : ∀ g : G, MeasurableSet {x | x - g ∈ H})
    (c : G ⧸ H) : MeasurableSet (fib H c) := by
  obtain ⟨g, rfl⟩ := QuotientAddGroup.mk_surjective c
  rw [fib_mk]
  exact hm g
end GlobalTheory.CompanionTheory.CosetSum
