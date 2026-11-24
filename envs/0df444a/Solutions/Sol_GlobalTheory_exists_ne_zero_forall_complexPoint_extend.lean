-- Prove2me | solution 1 for GlobalTheory.exists_ne_zero_forall_complexPoint_extend
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:55:38.344885+00:00
-- url     : https://prove2.me/submissions/c67a3724-f137-4cbd-a4e0-32bf19b91660

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_SpecialisationNumberFieldAndCountableValues
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsNeZeroForallComplexPointExtend
import Theorems.Thm_GlobalTheory_exists_basicOpen_subset_of_isConstructible_of_bot_mem
import Theorems.Thm_GlobalTheory_exists_ringHom_extend_of_ker_mem_range_comap

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution :
    ∀ (B A : Type) [CommRing B] [IsDomain B] [IsNoetherianRing B] [CommRing A] [IsDomain A]
    [Algebra B A] [Algebra.FiniteType B A], Function.Injective (algebraMap B A) →
    ∃ q : B, q ≠ 0 ∧ ∀ φ : B →+* ℂ, φ q ≠ 0 → ∃ ψ : A →+* ℂ, ψ.comp (algebraMap B A) = φ := by
  intro B A _ _ _ _ _ _ _ hinj
  have hfp : (algebraMap B A).FinitePresentation :=
    RingHom.finitePresentation_algebraMap.mpr (Algebra.FinitePresentation.of_finiteType.mp ‹_›)

  have hgen : (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum B) ∈
      Set.range (PrimeSpectrum.comap (algebraMap B A)) := by
    refine ⟨⟨⊥, Ideal.isPrime_bot⟩, PrimeSpectrum.ext ?_⟩
    exact Ideal.comap_bot_of_injective _ hinj
  obtain ⟨q, hq, hsub⟩ := exists_basicOpen_subset_of_isConstructible_of_bot_mem
    (PrimeSpectrum.isConstructible_range_comap hfp) hgen
  exact ⟨q, hq, fun φ hφ =>
    exists_ringHom_extend_of_ker_mem_range_comap φ (hsub _ fun hk => hφ (RingHom.mem_ker.mp hk))⟩
end GlobalTheory
