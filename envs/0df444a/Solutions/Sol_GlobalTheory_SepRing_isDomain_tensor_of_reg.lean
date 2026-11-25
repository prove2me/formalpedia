-- Prove2me | solution 1 for GlobalTheory.SepRing.isDomain_tensor_of_reg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T02:46:28.040625+00:00
-- url     : https://prove2.me/submissions/c0e270a6-8e28-4940-b380-6ef20e3928cd

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsRingEquivAdicCompletionLocalizationProd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_IsRegularLocalRingAdicCompletion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_IsNoetherianRingAdicCompletionOfNoetherian
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_MaximalIdealSquares_RingKrullDimQuotientSpanSingletonAddOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IdempotentTensorEqZeroOrOneOfIsPurelyInseparableStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsRegularLocalRingAtPrimeLocalizationTensorStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsCompleteLocalGeomDomain
import Theorems.Thm_GlobalTheory_CompletionFactor_exists_ringEquiv_completion_prod
import Theorems.Thm_GlobalTheory_IsAdicFamily_comp
import Theorems.Thm_GlobalTheory_RegularCompletion_isRegularLocalRing_adicCompletion
import Theorems.Thm_P2M_GlobalTheory_T_idempotent_tensor_eq_zero_or_one_of_isPurelyInseparable__dfb0df3ddba7
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsCub_comm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
open scoped TensorProduct
open GlobalTheory GlobalTheory.SepRing
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 1000000
namespace GlobalTheory.SepRing
theorem _root_.solution (k K S : Type) [Field k] [Field K] [Algebra k K]
    [FiniteDimensional k K] [IsPurelyInseparable k K] [CommRing S] [IsLocalRing S]
    [IsNoetherianRing S] [Algebra k S]
    (hreg : ∀ (𝔫 : Ideal (S ⊗[k] K)) [𝔫.IsPrime], IsRegularLocalRing (Localization.AtPrime 𝔫)) :
    IsDomain (K ⊗[k] AdicCompletion (maximalIdeal S) S) := by
  have hinj : Function.Injective (algebraMap S (S ⊗[k] K)) :=
    Algebra.TensorProduct.includeLeft_injective (R := k) (S := k) (A := S) (B := K)
      (algebraMap k K).injective
  have hker : RingHom.ker (algebraMap S (S ⊗[k] K)) ≤ maximalIdeal S := by
    intro x hx
    rw [RingHom.mem_ker] at hx
    rw [hinj (hx.trans (map_zero _).symm)]
    exact zero_mem _
  obtain ⟨𝔫, h𝔫max, h𝔫⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral (S := S ⊗[k] K)
    (maximalIdeal S) hker
  haveI := h𝔫max.isPrime
  obtain ⟨S', _, e, -⟩ := GlobalTheory.CompletionFactor.exists_ringEquiv_completion_prod S (S ⊗[k] K)
    (Localization.AtPrime 𝔫) 𝔫 h𝔫
  haveI : IsRegularLocalRing (Localization.AtPrime 𝔫) := hreg 𝔫
  haveI : IsRegularLocalRing (AdicCompletion (maximalIdeal (Localization.AtPrime 𝔫))
      (Localization.AtPrime 𝔫)) := GlobalTheory.RegularCompletion.isRegularLocalRing_adicCompletion _
  haveI hdom : IsDomain (AdicCompletion (maximalIdeal (Localization.AtPrime 𝔫))
      (Localization.AtPrime 𝔫)) := ReciprocityTheory.CA.AB.RegA.IsRegularLocalRing.isDomain _
  let f : K ⊗[k] AdicCompletion (maximalIdeal S) S ≃+* _ :=
    (Algebra.TensorProduct.comm k K (AdicCompletion (maximalIdeal S) S)).toRingEquiv.trans
    ((Algebra.TensorProduct.cancelBaseChange k S (AdicCompletion (maximalIdeal S) S)
      (AdicCompletion (maximalIdeal S) S) K).symm.toRingEquiv.trans e)
  have hS' : Subsingleton S' := by
    have hid : IsIdempotentElem (f.symm (0, 1)) := by
      show f.symm (0,1) * f.symm (0,1) = f.symm (0,1)
      rw [← map_mul]; simp
    rcases GlobalTheory.T.idempotent_tensor_eq_zero_or_one_of_isPurelyInseparable' k K (AdicCompletion (maximalIdeal S) S) (f.symm (0, 1)) hid with h | h
    · have h2 := congrArg (fun z => (f z).2) h
      simp at h2
      exact subsingleton_of_zero_eq_one h2.symm
    · have h2 := congrArg (fun z => (f z).1) h
      simp at h2
  exact Function.Injective.isDomain ((RingHom.fst _ _).comp f.toRingHom) (by
    intro x y hxy
    apply f.injective
    exact Prod.ext hxy (Subsingleton.elim _ _))
end GlobalTheory.SepRing
