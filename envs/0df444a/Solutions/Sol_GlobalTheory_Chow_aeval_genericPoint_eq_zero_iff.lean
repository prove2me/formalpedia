-- Prove2me | solution 1 for GlobalTheory.Chow.aeval_genericPoint_eq_zero_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T12:26:13.582665+00:00
-- url     : https://prove2.me/submissions/0f3cc1a4-e316-4ebf-955d-399b8e451639

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsWeaklyRegularMapCAppendMapLinForm
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_WeightedHomogeneousComponentMemElimIdeal
import Theorems.Thm_GlobalTheory_Chow_aeval_genericPoint

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
theorem _root_.solution (p : Ideal (MvPolynomial σ K)) (g : MvPolynomial σ K) :
    aeval (genericPoint p) g = 0 ↔ g ∈ p := by
  rw [aeval_genericPoint, IsFractionRing.to_map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem]
end GlobalTheory.Chow
