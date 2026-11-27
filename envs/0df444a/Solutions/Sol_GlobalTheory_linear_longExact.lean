-- Prove2me | solution 1 for GlobalTheory.linear_longExact
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T04:40:09.48681+00:00
-- url     : https://prove2.me/submissions/c60c7a57-e0e7-4c13-809b-b0e54e519634

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_HdimEqZeroOfSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_MapFOneInjectiveOfSectionsSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_SumNegOnePowFinrankEqZero
import Theorems.Thm_P2M_GlobalTheory_cohOn_toH____d75aa9ddc42b
import Theorems.Thm_P2M_GlobalTheory_cohOn_exact__9304e9eeff37
import Theorems.Thm_P2M_GlobalTheory_cohOn_exact__c8d68170d18d
import Theorems.Thm_P2M_GlobalTheory_cohOn_exact__a6c434186df0
import Theorems.Thm_GlobalTheory_cohOn_injective_zero
import Theorems.Thm_P2M_GlobalTheory_cohOn_finite__b94ea04ef99c
import Theorems.Thm_P2M_GlobalTheory_cohOn_finite__b0203fc991a1
import Theorems.Thm_P2M_GlobalTheory_cohOn_finite__ff84c2925af6
import Theorems.Thm_P2M_GlobalTheory_cohOn_finite__zero_149652da37c5
import Theorems.Thm_P2M_GlobalTheory_hdim__le_b9cb39bd95c7
import Theorems.Thm_GlobalTheory_sum_neg_one_pow_hdim_eq_add
import Theorems.Thm_GlobalTheory_SheafLES_injective_zero
import Theorems.Thm_P2M_GlobalTheory_SheafLES_exact__24269ba80ece
import Theorems.Thm_P2M_GlobalTheory_SheafLES_exact__5aa7b67be2da
import Theorems.Thm_P2M_GlobalTheory_SheafLES_exact__a6249fcd4aae


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite Limits Module
universe t v u
noncomputable section
open GlobalTheory
variable {X : Scheme.{u}}
namespace GlobalTheory
theorem _root_.solution {S : ShortComplex X.Modules} (hS : S.ShortExact) :
    (∀ (R : Type v) [CommRing R] [Algebra R Γ(X, ⊤)] (U : X.Opens),
      (∃ d : ∀ n, cohOn S.X₃ U n →ₗ[R] cohOn S.X₁ U (n + 1),
        (∀ n x, cohOn.toH' S.X₁ U (n + 1) (d n x) =
          SheafLES.δ.{u} (shortExact_toAbSheaf hS) n U (cohOn.toH' S.X₃ U n x)) ∧
        Function.Injective (cohOn.map R S.f U 0) ∧ ∀ n,
          Function.Exact (cohOn.map R S.f U n) (cohOn.map R S.g U n) ∧
          Function.Exact (cohOn.map R S.g U n) (d n) ∧
          Function.Exact (d n) (cohOn.map R S.f U (n + 1))) ∧
      (IsNoetherianRing R →
        (Module.Finite R (cohOn S.X₂ U 0) → Module.Finite R (cohOn S.X₁ U 0)) ∧ ∀ n,
        (Module.Finite R (cohOn S.X₁ U n) → Module.Finite R (cohOn S.X₃ U n) →
          Module.Finite R (cohOn S.X₂ U n)) ∧
        (Module.Finite R (cohOn S.X₂ U n) → Module.Finite R (cohOn S.X₁ U (n + 1)) →
          Module.Finite R (cohOn S.X₃ U n)) ∧
        (Module.Finite R (cohOn S.X₃ U n) → Module.Finite R (cohOn S.X₂ U (n + 1)) →
          Module.Finite R (cohOn S.X₁ U (n + 1))))) ∧
    ∀ (k : Type v) [Field k] [Algebra k Γ(X, ⊤)],
      (∀ n, Module.Finite k (coh S.X₁ n) → Module.Finite k (coh S.X₃ n) →
        hdim k S.X₂ n ≤ hdim k S.X₁ n + hdim k S.X₃ n) ∧
      ∀ N, (∀ i < N, Module.Finite k (coh S.X₁ i)) → (∀ i < N, Module.Finite k (coh S.X₃ i)) →
        Subsingleton (coh S.X₁ N) →
        ∑ i ∈ Finset.range N, (-1 : ℤ) ^ i * hdim k S.X₂ i =
          ∑ i ∈ Finset.range N, (-1 : ℤ) ^ i * hdim k S.X₁ i +
            ∑ i ∈ Finset.range N, (-1 : ℤ) ^ i * hdim k S.X₃ i :=
  ⟨fun R _ _ U ↦ ⟨⟨cohOn.δ R hS U, cohOn.toH'_δ R hS U, cohOn.injective_zero R hS U,
      fun n ↦ ⟨cohOn.exact₂ R hS U n, cohOn.exact₃ R hS U n, cohOn.exact₁ R hS U n⟩⟩,
    fun _ ↦ ⟨cohOn.finite₁_zero R hS U, fun n ↦
      ⟨cohOn.finite₂ R hS U n, cohOn.finite₃ R hS U n, cohOn.finite₁ R hS U n⟩⟩⟩,
   fun k _ _ ↦ ⟨hdim₂_le k hS, sum_neg_one_pow_hdim_eq_add k hS⟩⟩
end GlobalTheory
