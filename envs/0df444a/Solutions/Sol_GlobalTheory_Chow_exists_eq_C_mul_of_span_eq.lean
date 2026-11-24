-- Prove2me | solution 1 for GlobalTheory.Chow.exists_eq_C_mul_of_span_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T12:10:47.783614+00:00
-- url     : https://prove2.me/submissions/0f0822b8-b2e1-4e8e-90c2-582bc755ac11

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
theorem _root_.solution {f g : MvPolynomial τ K}
    (h : Ideal.span {f} = Ideal.span {g}) : ∃ c : K, c ≠ 0 ∧ g = C c * f := by
  obtain ⟨u, rfl⟩ := Ideal.span_singleton_eq_span_singleton.1 h
  obtain ⟨c, hc, hu⟩ := isUnit_iff_eq_C_of_isReduced.1 u.isUnit
  exact ⟨c, hc.ne_zero, by rw [hu, mul_comm]⟩
end GlobalTheory.Chow
