-- Prove2me | solution 1 for GlobalTheory.cohOn.sum_neg_one_pow_finrank
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T04:37:38.318577+00:00
-- url     : https://prove2.me/submissions/2fadecfd-bf18-48f1-93ca-8a0b556ac234

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_HdimEqZeroOfSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_MapFOneInjectiveOfSectionsSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_SumNegOnePowFinrankEqZero
import Theorems.Thm_P2M_GlobalTheory_ExactSeq_sum_neg_one_pow_finrank__46c8de609247
import Theorems.Thm_P2M_GlobalTheory_cohOn_exact__9304e9eeff37
import Theorems.Thm_P2M_GlobalTheory_cohOn_exact__c8d68170d18d
import Theorems.Thm_P2M_GlobalTheory_cohOn_exact__a6c434186df0
import Theorems.Thm_GlobalTheory_cohOn_injective_zero
import Theorems.Thm_P2M_GlobalTheory_cohOn___map_6ba3242e7e5e
import Theorems.Thm_P2M_GlobalTheory_cohOn_map___8dd9b9fe2c60
import Theorems.Thm_GlobalTheory_SheafLES_injective_zero
import Theorems.Thm_GlobalTheory_SheafLES_map_id
import Theorems.Thm_GlobalTheory_SheafLES_map_zero_hom
import Theorems.Thm_GlobalTheory_SheafLES_res_id
import Theorems.Thm_GlobalTheory_SheafLES_toAbSheaf_map_hom
import Theorems.Thm_GlobalTheory_SheafLES_toAbSheaf_obj_obj
import Theorems.Thm_GlobalTheory_sectionsOn_equivOfSMul_apply
import Theorems.Thm_P2M_GlobalTheory_SheafLES___map_026ec4bafb10
import Theorems.Thm_P2M_GlobalTheory_SheafLES_exact__24269ba80ece
import Theorems.Thm_P2M_GlobalTheory_SheafLES_exact__5aa7b67be2da
import Theorems.Thm_P2M_GlobalTheory_SheafLES_exact__a6249fcd4aae
import Theorems.Thm_P2M_GlobalTheory_SheafLES_map___ee3a67e9aebf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.SheafLES.map_id
attribute [local simp] GlobalTheory.SheafLES.map_zero_hom
attribute [local simp] GlobalTheory.SheafLES.res_id
attribute [local simp] GlobalTheory.SheafLES.toAbSheaf_map_hom
attribute [local simp] GlobalTheory.SheafLES.toAbSheaf_obj_obj
attribute [local simp] GlobalTheory.sectionsOn.equivOfSMul_apply
attribute [local simp] P2M_GlobalTheory_SheafLES___map_026ec4bafb10
attribute [local simp] P2M_GlobalTheory_SheafLES_map___ee3a67e9aebf


attribute [local simp] GlobalTheory.cohOn.δ_map
attribute [local simp] GlobalTheory.cohOn.map_δ

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
theorem _root_.solution (N : ℕ) (h₁ : ∀ i < N, Module.Finite k (cohOn S.X₁ U i))
    (h₂ : ∀ i < N, Module.Finite k (cohOn S.X₂ U i))
    (h₃ : ∀ i < N, Module.Finite k (cohOn S.X₃ U i)) :
    ∑ i ∈ Finset.range N, (-1 : ℤ) ^ i * (finrank k (cohOn S.X₁ U i) -
        finrank k (cohOn S.X₂ U i) + finrank k (cohOn S.X₃ U i)) =
      -(-1) ^ N * finrank k (LinearMap.ker (map k S.f U N)) := by
  rw [ExactSeq.sum_neg_one_pow_finrank₃ (fun i ↦ map k S.f U i) (fun i ↦ map k S.g U i)
    (fun i ↦ δ k hS U i) N h₁ h₂ h₃ (fun i _ ↦ exact₂ k hS U i) (fun i _ ↦ exact₃ k hS U i)
    (fun i _ ↦ exact₁ k hS U i), LinearMap.ker_eq_bot.2 (injective_zero k hS U), finrank_bot]
  simp
end GlobalTheory.cohOn
