-- Prove2me | solution 1 for GlobalTheory.Chow.exists_isWeightedHomogeneous_of_dvd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:30:57.013334+00:00
-- url     : https://prove2.me/submissions/eacde647-5341-4b9a-92c3-c429037cea13

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsWeaklyRegularMapCAppendMapLinForm
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_WeightedHomogeneousComponentMemElimIdeal
import Theorems.Thm_GlobalTheory_Chow_exists_eq_C_mul_of_dvd
import Theorems.Thm_GlobalTheory_quotientMapCSupSpanLinFormEquiv_mk
import Theorems.Thm_GlobalTheory_quotientSpanLinFormEquiv_mk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.quotientMapCSupSpanLinFormEquiv_mk
attribute [local simp] GlobalTheory.quotientSpanLinFormEquiv_mk



set_option autoImplicit false
open MvPolynomial
noncomputable section
open GlobalTheory GlobalTheory.Chow
variable {K : Type*} [Field K] {τ M : Type*} [AddCommMonoid M]
namespace GlobalTheory.Chow
theorem _root_.solution (w : τ → M) {f : MvPolynomial τ K}
    (h : ∀ a, f ∣ weightedHomogeneousComponent w a f) : ∃ a, IsWeightedHomogeneous w f a := by
  classical
  by_cases hf : f = 0
  · exact ⟨0, hf ▸ isWeightedHomogeneous_zero K w 0⟩
  obtain ⟨d, hd⟩ := exists_coeff_ne_zero hf
  have hne : weightedHomogeneousComponent w (Finsupp.weight w d) f ≠ 0 := by
    intro h0
    have := coeff_weightedHomogeneousComponent (w := w) (Finsupp.weight w d) f d
    rw [h0, if_pos rfl, coeff_zero] at this
    exact hd this.symm
  have hle : (weightedHomogeneousComponent w (Finsupp.weight w d) f).totalDegree ≤
      f.totalDegree := by
    refine totalDegree_le_of_support_subset fun e he => ?_
    rw [mem_support_iff, coeff_weightedHomogeneousComponent] at he
    rw [mem_support_iff]
    intro h0
    simp [h0] at he
  obtain ⟨c, hc, hcf⟩ := exists_eq_C_mul_of_dvd hne (h _) hle
  refine ⟨Finsupp.weight w d, ?_⟩
  have := (weightedHomogeneousComponent_isWeightedHomogeneous (w := w)
    (Finsupp.weight w d) f).C_mul c⁻¹
  rwa [hcf, ← mul_assoc, ← C_mul, inv_mul_cancel₀ hc, C_1, one_mul] at this
end GlobalTheory.Chow
