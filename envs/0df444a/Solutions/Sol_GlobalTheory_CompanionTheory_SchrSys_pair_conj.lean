-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SchrSys.pair_conj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T13:35:09.695805+00:00
-- url     : https://prove2.me/submissions/cfd1ae85-b91e-4f46-a5f7-9386b66e86a8

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_MembershipCriteria_GoodChar
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MembershipProofs_GoodCharIsLocallyConstant
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MembershipProofs_IntegrablePair

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.CompanionTheory.VacLoc GlobalTheory.CompanionTheory.FinHeis GlobalTheory.WeilM MeasureTheory Matrix
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SchrSys
variable {R : Type} [TopologicalSpace R] {κ : Type}
namespace GlobalTheory.CompanionTheory.SchrSys
theorem _root_.solution (μ : @Measure (κ → R) (borel _)) (φ φ' : (κ → R) → ℂ) :
    (starRingEnd ℂ) (pair μ φ φ') = pair μ φ' φ := by
  letI : MeasurableSpace (κ → R) := borel _
  unfold pair
  rw [← integral_conj]
  congr 1
  funext x
  simp [mul_comm]
end GlobalTheory.CompanionTheory.SchrSys
