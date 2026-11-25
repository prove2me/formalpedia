-- Prove2me | solution 1 for GlobalTheory.HopfQuot.exists_coact_eq_add_of_primitive
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T04:18:11.442463+00:00
-- url     : https://prove2.me/submissions/276c0916-ee05-4149-a1ad-df54e4b7fdd5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RigOfOmegaInjectiveOfEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_FiniteFaithfullyFlatKer
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsCoactionEqAddOfPrimitive
import Theorems.Thm_GlobalTheory_HopfQuot_coact_ev_mulRight_of_primitive
import Theorems.Thm_GlobalTheory_AugCot_baseChangeAug_tmul
import Theorems.Thm_GlobalTheory_AugCot_baseChangeEquiv_tmul_d
import Theorems.Thm_GlobalTheory_AugCot_mvPolynomialBasis_apply
import Theorems.Thm_GlobalTheory_HopfQuot_ev_mem_equalizer
import Theorems.Thm_GlobalTheory_HopfQuot_ev_tmul
import Theorems.Thm_GlobalTheory_HopfQuot_exists_integrals
import Theorems.Thm_GlobalTheory_HopfQuot_finite_faithfullyFlat_ker
import Theorems.Thm_GlobalTheory_IsBicharacter_map
import Theorems.Thm_GlobalTheory_PDivGroup_muLieGen_dlogT
import Theorems.Thm_GlobalTheory_PDivGroup_resOne_succ
import Theorems.Thm_GlobalTheory_PDivGroup_resOne_zero
import Theorems.Thm_GlobalTheory_PDivGroup_rigExtMap_id
import Theorems.Thm_GlobalTheory_PDivGroup_rigExtMap_mk
import Theorems.Thm_GlobalTheory_PDivGroup_rigLevel_mk
import Theorems.Thm_GlobalTheory_PDiv_SemiBialgHom_levelRig_mk
import Theorems.Thm_GlobalTheory_PDiv_digit_zero
import Theorems.Thm_GlobalTheory_PDiv_muChar_muT
import Theorems.Thm_ReciprocityTheory_PGsh_IsPtDer_map_one
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.AugCot.baseChangeAug_tmul
attribute [local simp] GlobalTheory.AugCot.baseChangeEquiv_tmul_d
attribute [local simp] GlobalTheory.AugCot.mvPolynomialBasis_apply
attribute [local simp] GlobalTheory.HopfQuot.ev_tmul
attribute [local simp] GlobalTheory.PDiv.SemiBialgHom.levelRig_mk
attribute [local simp] GlobalTheory.PDiv.digit_zero
attribute [local simp] GlobalTheory.PDiv.muChar_muT
attribute [local simp] GlobalTheory.PDivGroup.muLieGen_dlogT
attribute [local simp] GlobalTheory.PDivGroup.resOne_succ
attribute [local simp] GlobalTheory.PDivGroup.resOne_zero
attribute [local simp] GlobalTheory.PDivGroup.rigExtMap_id
attribute [local simp] GlobalTheory.PDivGroup.rigExtMap_mk
attribute [local simp] GlobalTheory.PDivGroup.rigLevel_mk



set_option autoImplicit false
open TensorProduct Coalgebra Bialgebra CategoryTheory WithConv GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup
open GlobalTheory GlobalTheory.HopfQuot
namespace GlobalTheory.HopfQuot
theorem _root_.solution : ∀ {R Λ B : Type} [CommRing R] [CommRing Λ] [HopfAlgebra R Λ] [Module.Finite R Λ] [Module.Projective R Λ] [CommRing B] [Algebra R B] (ρ : B →ₐ[R] B ⊗[R] Λ), (∀ a, TensorProduct.assoc R B Λ Λ (ρ.toLinearMap.rTensor Λ (ρ a)) = (Coalgebra.comul (R := R) (A := Λ)).lTensor B (ρ a)) → (∀ a, TensorProduct.rid R B ((Coalgebra.counit (R := R) (A := Λ)).lTensor B (ρ a)) = a) → Function.Surjective (Algebra.TensorProduct.productMap (Algebra.TensorProduct.includeLeft : B →ₐ[R] B ⊗[R] Λ) ρ) → ∀ b : Λ, cobOne R Λ b = 0 → ∃ x : B, ρ x = x ⊗ₜ[R] 1 + 1 ⊗ₜ[R] b := by
  intro R Λ B _ _ _ _ _ _ _ ρ hassoc hcounit hsurj b hb0
  have hb : Coalgebra.comul (R := R) b = b ⊗ₜ[R] 1 + 1 ⊗ₜ[R] b := by
    rw [cobOne_apply, sub_sub, sub_eq_zero] at hb0
    exact hb0
  obtain ⟨-, -, hff, -⟩ := finite_faithfullyFlat_ker ρ hassoc hcounit hsurj
  set B₀ := AlgHom.equalizer ρ (Algebra.TensorProduct.includeLeft : B →ₐ[R] B ⊗[R] Λ) with hB₀
  let I : Ideal B₀ :=
    { carrier := {y | ∃ x : B, ρ x = x ⊗ₜ[R] 1 + (y : B) ⊗ₜ[R] b}
      add_mem' := by
        rintro y z ⟨x, hx⟩ ⟨x', hx'⟩
        refine ⟨x + x', ?_⟩
        rw [map_add, hx, hx', Subalgebra.coe_add, add_tmul, add_tmul]
        abel
      zero_mem' := ⟨0, by simp⟩
      smul_mem' := by
        rintro t y ⟨x, hx⟩
        have ht : ρ t = (t : B) ⊗ₜ 1 := t.2
        refine ⟨t * x, ?_⟩
        rw [map_mul, ht, hx]
        simp [mul_add] }
  obtain ⟨n, l, T, hl, hT⟩ := exists_integrals R Λ
  have hmem : ∀ k f, ev B (l k) (ρ f) ∈ I.map (algebraMap B₀ B) := by
    intro k f
    refine Ideal.mem_map_of_mem (algebraMap B₀ B)
      (x := ⟨ev B (l k) (ρ f), ev_mem_equalizer ρ hassoc _ (hl k) f⟩) ?_
    refine ⟨-ev B (l k ∘ₗ LinearMap.mulRight R b) (ρ f), ?_⟩
    rw [map_neg, coact_ev_mulRight_of_primitive ρ hassoc _ (hl k) b hb, neg_tmul]
    abel
  have hall : ∀ k z, ev B (l k) z ∈ I.map (algebraMap B₀ B) := by
    intro k z
    obtain ⟨w, rfl⟩ := hsurj z
    induction w with
    | zero => simp
    | add u v hu hv =>
      rw [map_add, map_add]
      exact add_mem hu hv
    | tmul u v =>
      have : (Algebra.TensorProduct.includeLeft : B →ₐ[R] B ⊗[R] Λ) u * ρ v = u • ρ v := by
        rw [Algebra.smul_def]
        rfl
      rw [Algebra.TensorProduct.productMap_apply_tmul, this, map_smul]
      exact Ideal.mul_mem_left _ _ (hmem k v)
  have h1 : (1 : B) ∈ I.map (algebraMap B₀ B) := by
    have : (1 : B) = ∑ k, ev B (l k) (1 ⊗ₜ T k) := by
      have h := hT 1
      simp only [mul_one, Bialgebra.counit_one] at h
      simp [← Finset.sum_smul, h]
    rw [this]
    exact Ideal.sum_mem _ fun k _ => hall k _
  have h2 : (1 : B₀) ∈ I := by
    rw [← Ideal.comap_map_eq_self_of_faithfullyFlat (B := B) I, Ideal.mem_comap, map_one]
    exact h1
  exact h2
end GlobalTheory.HopfQuot
