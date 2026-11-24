-- Prove2me | solution 1 for GlobalTheory.Chow.exists_eq_C_mul_of_dvd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T12:10:46.864894+00:00
-- url     : https://prove2.me/submissions/da640874-2016-466d-8ec1-8ee279f75188

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsWeaklyRegularMapCAppendMapLinForm
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_WeightedHomogeneousComponentMemElimIdeal

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
variable {K : Type*} [Field K] {τ M : Type*} [AddCommMonoid M]
namespace GlobalTheory.Chow
theorem _root_.solution {f g : MvPolynomial τ K} (hg : g ≠ 0) (h : f ∣ g)
    (hd : g.totalDegree ≤ f.totalDegree) : ∃ c : K, c ≠ 0 ∧ g = C c * f := by
  obtain ⟨q, rfl⟩ := h
  have hf := left_ne_zero_of_mul hg
  have hq := right_ne_zero_of_mul hg
  rw [totalDegree_mul_of_isDomain hf hq] at hd
  have h0 : q.totalDegree = 0 := by omega
  rw [totalDegree_eq_zero_iff_eq_C] at h0
  refine ⟨coeff 0 q, fun hc => hq ?_, ?_⟩
  · rw [h0, hc, C_0]
  · rw [← h0, mul_comm]
end GlobalTheory.Chow
