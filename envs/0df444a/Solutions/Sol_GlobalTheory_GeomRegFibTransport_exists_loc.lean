-- Prove2me | solution 1 for GlobalTheory.GeomRegFibTransport.exists_loc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T16:18:37.471705+00:00
-- url     : https://prove2.me/submissions/eee0821b-9ea9-4148-b8f9-2dd51523d493

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_FinalTheorems
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_GeomRegFibAdicCompletionOfEssFiniteTypeInt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing TensorProduct
open GlobalTheory GlobalTheory.GeomRegFibTransport
open ReciprocityTheory.AnForm.R.FinalTheorems
namespace GlobalTheory.GeomRegFibTransport
theorem _root_.solution (A : Type) [CommRing A] [IsLocalRing A] [Algebra.EssFiniteType ℤ A] :
    ∃ (A₀ : Type) (_ : CommRing A₀) (_ : Algebra.FiniteType ℤ A₀) (p : Ideal A₀) (_ : p.IsPrime),
      Nonempty (Localization.AtPrime p ≃+* A) := by
  refine ⟨Algebra.EssFiniteType.subalgebra ℤ A, inferInstance, inferInstance,
    (maximalIdeal A).comap (algebraMap (Algebra.EssFiniteType.subalgebra ℤ A) A), inferInstance, ?_⟩
  have hsub : Algebra.EssFiniteType.submonoid ℤ A =
      ((maximalIdeal A).comap (algebraMap (Algebra.EssFiniteType.subalgebra ℤ A) A)).primeCompl := by
    ext x
    simp [Algebra.EssFiniteType.submonoid, Ideal.primeCompl, IsLocalRing.mem_maximalIdeal,
      mem_nonunits_iff, IsUnit.mem_submonoid_iff]
  have hloc := Algebra.EssFiniteType.isLocalization ℤ A
  rw [hsub] at hloc
  haveI : IsLocalization.AtPrime A ((maximalIdeal A).comap (algebraMap (Algebra.EssFiniteType.subalgebra ℤ A) A)) := hloc
  exact ⟨(IsLocalization.algEquiv ((maximalIdeal A).comap (algebraMap (Algebra.EssFiniteType.subalgebra ℤ A) A)).primeCompl
    (Localization.AtPrime _) A).toRingEquiv⟩
end GlobalTheory.GeomRegFibTransport
