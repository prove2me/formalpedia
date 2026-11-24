-- Prove2me | solution 1 for GlobalTheory.exists_eq_mul_canonicalSigma
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:45:38.928062+00:00
-- url     : https://prove2.me/submissions/57266b65-ef21-4a9b-b767-eca4d6245b96

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_HasSumLocallyUniformlyWeierstrassZetaExcept
import Theorems.Thm_GlobalTheory_sigmaSign_ne_zero
import Theorems.Thm_GlobalTheory_canonicalSigma_eq_zero_iff
import Theorems.Thm_GlobalTheory_canonicalSigma_add
import Theorems.Thm_GlobalTheory_exists_eq_const_of_periodic_of_simple_pole

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
theorem _root_.solution {F : ℂ → ℂ} (hF : Differentiable ℂ F)
    (hlaw : ∀ w ∈ L.lattice, ∀ z, F (z + w) =
      sigmaSign L w * cexp (π * latticeForm L z w + π * latticeForm L w w / 2) * F z) :
    ∃ c : ℂ, ∀ z, F z = c * canonicalSigma L z := by
  have hne : ∀ z ∉ L.lattice, canonicalSigma L z ≠ 0 := fun z hz =>
    (canonicalSigma_eq_zero_iff L).not.2 hz
  obtain ⟨c, hc⟩ := exists_eq_const_of_periodic_of_simple_pole L
    (f := fun z => F z / canonicalSigma L z)
    (N := fun z => F z / (sigmaProd L z * cexp (-(sTwo L * z ^ 2 / 2))))
    (.div hF.differentiableOn (differentiable_canonicalSigma L).differentiableOn hne)
    (fun z hz w hw => by
      beta_reduce
      rw [hlaw w hw, canonicalSigma_add L hw,
        mul_div_mul_left _ _ (mul_ne_zero (sigmaSign_ne_zero L w) (exp_ne_zero _))])
    ((hF.analyticAt 0).div (Differentiable.analyticAt (by fun_prop) 0) (by simp))
    (by
      filter_upwards [self_mem_nhdsWithin] with z (hz : z ≠ 0)
      rw [canonicalSigma, weierstrassSigma, mul_assoc, ← mul_div_assoc, mul_div_mul_left _ _ hz])
  refine ⟨c, fun z => congrFun (Continuous.ext_on (dense_compl_lattice L) hF.continuous
    (g := fun z => c * canonicalSigma L z)
    (continuous_const.mul (differentiable_canonicalSigma L).continuous) fun z hz => ?_) z⟩
  exact (div_eq_iff (hne z hz)).1 (hc z hz)
end GlobalTheory
