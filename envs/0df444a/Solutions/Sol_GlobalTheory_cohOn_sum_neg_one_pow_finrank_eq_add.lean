-- Prove2me | solution 1 for GlobalTheory.cohOn.sum_neg_one_pow_finrank_eq_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:31:56.400678+00:00
-- url     : https://prove2.me/submissions/c496a355-7007-48a2-a25f-6b824a097f1b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_HdimEqZeroOfSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_MapFOneInjectiveOfSectionsSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_SumNegOnePowFinrankEqZero
import Theorems.Thm_GlobalTheory_ExactSeq_sum_neg_one_pow_finrank_eq_add
import Theorems.Thm_P2M_GlobalTheory_cohOn_exact__9304e9eeff37
import Theorems.Thm_P2M_GlobalTheory_cohOn_exact__c8d68170d18d
import Theorems.Thm_P2M_GlobalTheory_cohOn_exact__a6c434186df0
import Theorems.Thm_GlobalTheory_cohOn_injective_zero
import Theorems.Thm_P2M_GlobalTheory_cohOn_finite__b94ea04ef99c
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
open GlobalTheory.cohOn
variable (R : Type v) [CommRing R] [Algebra R Γ(X, ⊤)]
  {S : ShortComplex X.Modules} (hS : S.ShortExact)
variable (U : X.Opens) (n : ℕ)
include hS
variable (k : Type v) [Field k] [Algebra k Γ(X, ⊤)]
namespace GlobalTheory.cohOn
theorem _root_.solution (N : ℕ)
    (h₁ : ∀ i < N, Module.Finite k (cohOn S.X₁ U i))
    (h₃ : ∀ i < N, Module.Finite k (cohOn S.X₃ U i)) (hN : Function.Injective (map k S.f U N)) :
    ∑ i ∈ Finset.range N, (-1 : ℤ) ^ i * finrank k (cohOn S.X₂ U i) =
      ∑ i ∈ Finset.range N, (-1 : ℤ) ^ i * finrank k (cohOn S.X₁ U i) +
        ∑ i ∈ Finset.range N, (-1 : ℤ) ^ i * finrank k (cohOn S.X₃ U i) :=
  ExactSeq.sum_neg_one_pow_finrank_eq_add (fun i ↦ map k S.f U i) (fun i ↦ map k S.g U i)
    (fun i ↦ δ k hS U i) N h₁ (fun i hi ↦ finite₂ k hS U i (h₁ i hi) (h₃ i hi)) h₃
    (injective_zero k hS U) (fun i _ ↦ exact₂ k hS U i) (fun i _ ↦ exact₃ k hS U i)
    (fun i _ ↦ exact₁ k hS U i) hN
end GlobalTheory.cohOn
