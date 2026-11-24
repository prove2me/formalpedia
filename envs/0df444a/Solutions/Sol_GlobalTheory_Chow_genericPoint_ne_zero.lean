-- Prove2me | solution 1 for GlobalTheory.Chow.genericPoint_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T12:43:17.613867+00:00
-- url     : https://prove2.me/submissions/6d480ca2-dd98-4875-a922-cd0e195135f5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsWeaklyRegularMapCAppendMapLinForm
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_WeightedHomogeneousComponentMemElimIdeal
import Theorems.Thm_GlobalTheory_Chow_aeval_genericPoint_eq_zero_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
noncomputable section
open GlobalTheory GlobalTheory.Chow
variable {σ β : Type*} [Fintype σ]
variable {K : Type*} [CommRing K]
omit [Fintype σ]
namespace GlobalTheory.Chow
theorem _root_.solution {p : Ideal (MvPolynomial σ K)} (hp : ∃ j, X j ∉ p) :
    genericPoint p ≠ 0 := by
  obtain ⟨j, hj⟩ := hp
  intro h
  exact hj ((aeval_genericPoint_eq_zero_iff p _).1 (by rw [aeval_X, h]; rfl))
end GlobalTheory.Chow
