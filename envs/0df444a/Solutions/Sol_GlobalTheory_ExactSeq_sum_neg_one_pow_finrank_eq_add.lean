-- Prove2me | solution 1 for GlobalTheory.ExactSeq.sum_neg_one_pow_finrank_eq_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:07:20.834458+00:00
-- url     : https://prove2.me/submissions/9a1878f3-c247-4015-ba63-a235ecf48d26

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_HdimEqZeroOfSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_MapFOneInjectiveOfSectionsSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_SumNegOnePowFinrankEqZero
import Theorems.Thm_P2M_GlobalTheory_ExactSeq_sum_neg_one_pow_finrank__46c8de609247
import Theorems.Thm_GlobalTheory_SheafLES_map_id
import Theorems.Thm_GlobalTheory_SheafLES_map_zero_hom
import Theorems.Thm_GlobalTheory_SheafLES_res_id
import Theorems.Thm_GlobalTheory_SheafLES_toAbSheaf_map_hom
import Theorems.Thm_GlobalTheory_SheafLES_toAbSheaf_obj_obj
import Theorems.Thm_GlobalTheory_sectionsOn_equivOfSMul_apply
import Theorems.Thm_P2M_GlobalTheory_SheafLES___map_026ec4bafb10
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



set_option autoImplicit false
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite Limits Module
universe t v u
noncomputable section
open GlobalTheory
open GlobalTheory.ExactSeq
variable {k : Type*} [DivisionRing k]
variable {A B C : ℕ → Type*} [∀ i, AddCommGroup (A i)] [∀ i, AddCommGroup (B i)]
  [∀ i, AddCommGroup (C i)] [∀ i, Module k (A i)] [∀ i, Module k (B i)] [∀ i, Module k (C i)]
  (f : ∀ i, A i →ₗ[k] B i) (g : ∀ i, B i →ₗ[k] C i) (δ : ∀ i, C i →ₗ[k] A (i + 1))
namespace GlobalTheory.ExactSeq
theorem _root_.solution (N : ℕ) (hA : ∀ i < N, Module.Finite k (A i))
    (hB : ∀ i < N, Module.Finite k (B i)) (hC : ∀ i < N, Module.Finite k (C i))
    (h₀ : Function.Injective (f 0))
    (h₂ : ∀ i < N, Function.Exact (f i) (g i)) (h₃ : ∀ i < N, Function.Exact (g i) (δ i))
    (h₁ : ∀ i < N, Function.Exact (δ i) (f (i + 1))) (hN : Function.Injective (f N)) :
    ∑ i ∈ Finset.range N, (-1 : ℤ) ^ i * finrank k (B i) =
      ∑ i ∈ Finset.range N, (-1 : ℤ) ^ i * finrank k (A i) +
        ∑ i ∈ Finset.range N, (-1 : ℤ) ^ i * finrank k (C i) := by
  have := sum_neg_one_pow_finrank₃ f g δ N hA hB hC h₂ h₃ h₁
  rw [LinearMap.ker_eq_bot.2 h₀, LinearMap.ker_eq_bot.2 hN, finrank_bot, finrank_bot] at this
  simp only [mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib, Nat.cast_zero,
    mul_zero, sub_zero] at this
  linarith
end GlobalTheory.ExactSeq
