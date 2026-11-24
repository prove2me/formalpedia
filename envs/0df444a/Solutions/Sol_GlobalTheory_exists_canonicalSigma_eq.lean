-- Prove2me | solution 1 for GlobalTheory.exists_canonicalSigma_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:39:04.559127+00:00
-- url     : https://prove2.me/submissions/6a516653-6a85-4f36-9407-12c1ab816b19

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_HasSumLocallyUniformlyWeierstrassZetaExcept
import Theorems.Thm_GlobalTheory_exists_eq_add_sq_mul_of_even

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Filter Complex PeriodPair
open scoped Topology ComplexConjugate Real
open GlobalTheory
variable (L : PeriodPair)
namespace GlobalTheory
theorem _root_.solution : ∃ h : ℂ → ℂ, AnalyticAt ℂ h 0 ∧
    ∀ z, canonicalSigma L z = z + z ^ 3 * h z := by
  obtain ⟨h, hh, e⟩ := exists_eq_add_sq_mul_of_even
    (f := fun z => sigmaProd L z * cexp (-(sTwo L * z ^ 2 / 2)))
    (Differentiable.analyticAt (by fun_prop) 0) (by simp)
  refine ⟨h, hh, fun z => ?_⟩
  rw [canonicalSigma, weierstrassSigma, mul_assoc, e z]
  simp
  ring
end GlobalTheory
