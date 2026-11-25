-- Prove2me | solution 1 for GlobalTheory.CompletionReduced.isReduced_of_dim_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T15:20:18.233141+00:00
-- url     : https://prove2.me/submissions/cf635422-a3f4-4497-a0dd-be972f08ae6a

import Mathlib
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_SaturatedChains_Integral
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_RingKrullDimLtTopOfEssFiniteTypeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_AssociatedPrimeLocalizationDvrStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsInjectiveAdicCompletionMapOfFiniteStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_FiniteIntegralClosureOfEssFiniteTypeIntDomainStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_IsNoetherianRingAdicCompletionOfNoetherianStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_AdicCompletionQuotientRingEquivStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_IsReducedOfNonZeroDivisorMemJacobsonOfAssociatedStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_AdicCompletionReducedOfJacobson
import Theorems.Thm_GlobalTheory_CompletionReduced_map_le_jacobson_of_comap_isMaximal
import Theorems.Thm_GlobalTheory_CompletionReduced_isReduced_of_normal
import Theorems.Thm_GlobalTheory_T_exists_injective_adicCompletion_map_of_finite
import Theorems.Thm_GlobalTheory_T_finite_integralClosure_of_essFiniteType_int_domain
import Theorems.Thm_ReciprocityTheory_CA_ringKrullDim_eq_of_isIntegral_of_injective


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
open GlobalTheory GlobalTheory.CompletionReduced
namespace GlobalTheory.CompletionReduced
theorem _root_.solution : ∀ (n : ℕ) (D : Type) [CommRing D] [IsDomain D] [Algebra.EssFiniteType ℤ D],
    ringKrullDim D ≤ (n : WithBot ℕ∞) → ∀ (J : Ideal D), J ≤ Ideal.jacobson (⊥ : Ideal D) →
      IsReduced (AdicCompletion J D) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro D _ _ _ hdim J hJ
  haveI : IsNoetherianRing D := Algebra.EssFiniteType.isNoetherianRing ℤ D

  let N := integralClosure D (FractionRing D)
  haveI : Module.Finite D N := GlobalTheory.T.finite_integralClosure_of_essFiniteType_int_domain D
  haveI : IsIntegrallyClosed N := integralClosure.isIntegrallyClosedOfFiniteExtension (FractionRing D)
  have hinj : Function.Injective (algebraMap D N) := by
    intro a b hab
    have := congrArg (fun y : N => (y : FractionRing D)) hab
    exact IsFractionRing.injective D (FractionRing D) this
  have hdimN : ringKrullDim N ≤ (n : WithBot ℕ∞) := by
    rw [ReciprocityTheory.CA.ringKrullDim_eq_of_isIntegral_of_injective hinj]; exact hdim
  haveI : Algebra.EssFiniteType D N := inferInstance
  haveI hessN : @Algebra.EssFiniteType ℤ N _ _ (Ring.toIntAlgebra _) := by
    letI := Ring.toIntAlgebra N
    haveI : IsScalarTower ℤ D N := .of_algebraMap_eq fun z => by simp
    exact Algebra.EssFiniteType.comp ℤ D N
  have hIjac : J.map (algebraMap D N) ≤ Ideal.jacobson (⊥ : Ideal N) :=
    map_le_jacobson_of_comap_isMaximal _
      (fun M hM => Ideal.isMaximal_comap_of_isIntegral_of_isMaximal M) J hJ
  obtain ⟨f, hf⟩ := GlobalTheory.T.exists_injective_adicCompletion_map_of_finite D N hinj J
  haveI := isReduced_of_normal n ih N hdimN _ hIjac
  exact isReduced_of_injective f hf
end GlobalTheory.CompletionReduced
