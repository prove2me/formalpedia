-- Prove2me | solution 1 for GlobalTheory.ReducedAlg.isReduced_field_tensor_domain
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:34:44.097937+00:00
-- url     : https://prove2.me/submissions/2c69d0c2-be6b-4563-b933-00124b0a3d0a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsDomainAndIsIntegrallyClosedAtPrimeOfSmoothOfCo
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_EqZeroOfForallLTensorEqZero
import Theorems.Thm_GlobalTheory_isReduced_of_smooth_of_isIntegrallyClosed


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct
open GlobalTheory GlobalTheory.ReducedAlg
namespace GlobalTheory.ReducedAlg
theorem _root_.solution {k : Type*} [Field k] [PerfectField k] (K A : Type*)
    [Field K] [Algebra k K] [CommRing A] [Algebra k A] [IsDomain A] [Algebra.FiniteType k A] :
    IsReduced (K ⊗[k] A) := by
  classical
  have hfp : Algebra.FinitePresentation k A := Algebra.FinitePresentation.of_finiteType.1 inferInstance
  have hgen : (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum A) ∈ Algebra.smoothLocus k A := by
    show Algebra.FormallySmooth k (Localization.AtPrime (⊥ : Ideal A))
    have hS : (⊥ : Ideal A).primeCompl = nonZeroDivisors A := by
      ext x
      simp [Ideal.primeCompl, mem_nonZeroDivisors_iff_ne_zero]
    have hloc : IsLocalization (nonZeroDivisors A) (Localization.AtPrime (⊥ : Ideal A)) :=
      hS ▸ (inferInstance : IsLocalization (⊥ : Ideal A).primeCompl (Localization.AtPrime (⊥ : Ideal A)))
    have e1 : Algebra.EssFiniteType A (FractionRing A) := .of_isLocalization _ (nonZeroDivisors A)
    have e2 : Algebra.EssFiniteType k (FractionRing A) := .comp k A _
    exact (Algebra.FormallySmooth.iff_of_equiv ((IsLocalization.algEquiv (nonZeroDivisors A)
      (FractionRing A) (Localization.AtPrime (⊥ : Ideal A))).restrictScalars k)).1 inferInstance
  obtain ⟨v, ⟨f, rfl⟩, hv, hsub⟩ := PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open
    hgen Algebra.isOpen_smoothLocus
  have hf0 : f ≠ 0 := by
    have := (PrimeSpectrum.mem_basicOpen f _).1 hv
    simpa using this
  have hsm : Algebra.Smooth k (Localization.Away f) :=
    Algebra.basicOpen_subset_smoothLocus_iff_smooth.1 hsub
  have hred : IsReduced (K ⊗[k] Localization.Away f) :=
    GlobalTheory.isReduced_of_smooth_of_isIntegrallyClosed K _
  have hinj : Function.Injective (algebraMap A (Localization.Away f)) :=
    IsLocalization.injective (Localization.Away f) (powers_le_nonZeroDivisors_of_noZeroDivisors hf0)
  exact isReduced_of_injective
    (Algebra.TensorProduct.map (AlgHom.id k K) (IsScalarTower.toAlgHom k A (Localization.Away f)))
    (Module.Flat.lTensor_preserves_injective_linearMap _ hinj)
end GlobalTheory.ReducedAlg
