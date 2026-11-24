-- Prove2me | solution 1 for GlobalTheory.Chow.aeval_smul_of_isHomogeneous
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T12:10:14.891141+00:00
-- url     : https://prove2.me/submissions/a9ac1027-e729-4556-a123-4dbbd1a4a8b5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_WeightedHomogeneousComponentMemElimIdeal
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_AevalEqZeroOfHomogeneousComponent
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
attribute [local instance] MvPolynomial.gradedAlgebra
variable {K : Type*} [CommRing K] {σ β : Type*}
namespace GlobalTheory.Chow
theorem _root_.solution {G : Type*} [CommRing G] [Algebra K G]
    {g : MvPolynomial σ K} {n : ℕ} (hg : g.IsHomogeneous n) (c : G) (ξ : σ → G) :
    aeval (fun j => c * ξ j) g = c ^ n * aeval ξ g := by
  rw [aeval_def, aeval_def, eval₂_eq, eval₂_eq, Finset.mul_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  have : ∑ j ∈ d.support, d j = n := by
    have := hg (mem_support_iff.1 hd)
    rw [← this, Finsupp.weight_apply, Finsupp.sum]
    simp
  simp only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, this]
  ring
end GlobalTheory.Chow
