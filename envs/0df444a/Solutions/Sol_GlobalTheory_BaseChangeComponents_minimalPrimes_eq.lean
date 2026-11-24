-- Prove2me | solution 1 for GlobalTheory.BaseChangeComponents.minimalPrimes_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T12:01:26.897548+00:00
-- url     : https://prove2.me/submissions/a797138c-03f7-484c-8549-67afb77ab9ae

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GenericRegularity_IsIntegrallyClosedQuotientOfMemMinimalPrimes
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GenericRegularity_IsNoetherianRingTensor
import Theorems.Thm_GlobalTheory_BaseChangeComponents_incl_injective
import Theorems.Thm_GlobalTheory_BaseChangeComponents_isLocalization_incl

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
open GlobalTheory GlobalTheory.BaseChangeComponents
variable {K Ω : Type} (F : Type) [Field K] [Field F] [Field Ω] [Algebra K F] [Algebra K Ω]
namespace GlobalTheory.BaseChangeComponents
theorem _root_.solution (R : Subalgebra K Ω)
    (hR : ∀ x : Ω, ∃ a ∈ R, ∃ b ∈ R, b ≠ 0 ∧ x * b = a) :
    minimalPrimes (F ⊗[K] R) = Ideal.comap (incl F R) '' minimalPrimes (F ⊗[K] Ω) :=
  by
    letI := (incl F R).toAlgebra
    haveI := isLocalization_incl F R hR
    have h := IsLocalization.minimalPrimes_comap (denoms F R) (F ⊗[K] Ω) (⊥ : Ideal (F ⊗[K] Ω))
    have hb : Ideal.comap (algebraMap (F ⊗[K] R) (F ⊗[K] Ω)) ⊥ = ⊥ := by
      rw [← RingHom.ker_eq_comap_bot]
      exact (RingHom.injective_iff_ker_eq_bot _).1 (incl_injective F R)
    rw [hb] at h
    exact h
end GlobalTheory.BaseChangeComponents
