-- Prove2me | solution 1 for GlobalTheory.OuterTensor.isIrreducible_outer_tprod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T19:34:00.891506+00:00
-- url     : https://prove2.me/submissions/8f613eb2-cc14-4e08-bd30-7951866232f5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_SpanRangeEqTopOfIsIrreducible
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsIrreducibleOuterTprod
import Theorems.Thm_GlobalTheory_OuterTensor_nontrivial_of_isIrreducible
import Theorems.Thm_GlobalTheory_ClassFin_span_range_eq_top_of_isIrreducible


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
open GlobalTheory GlobalTheory.OuterTensor
namespace GlobalTheory.OuterTensor
theorem _root_.solution :
    ∀ (G H V W : Type) [Group G] [Group H] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ V] [FiniteDimensional ℂ W] (ρ : Representation ℂ G V) (σ : Representation ℂ H W), ρ.IsIrreducible → σ.IsIrreducible → (Representation.tprod (ρ.comp (MonoidHom.fst G H)) (σ.comp (MonoidHom.snd G H)) : Representation ℂ (G × H) (V ⊗[ℂ] W)).IsIrreducible := by
  intro G H V W _ _ _ _ _ _ _ _ ρ σ hρ hσ
  have hV := nontrivial_of_isIrreducible ρ hρ
  have hW := nontrivial_of_isIrreducible σ hσ
  have sρ := GlobalTheory.ClassFin.span_range_eq_top_of_isIrreducible G V ρ hρ
  have sσ := GlobalTheory.ClassFin.span_range_eq_top_of_isIrreducible H W σ hσ
  have hVW : Nontrivial (V ⊗[ℂ] W) := by
    apply Module.nontrivial_of_finrank_pos (R := ℂ)
    rw [Module.finrank_tensorProduct]
    exact Nat.mul_pos Module.finrank_pos Module.finrank_pos
  refine { exists_pair_ne := ⟨⊥, ⊤, fun h => ?_⟩, eq_bot_or_eq_top := fun S => ?_ }
  · exact bot_ne_top (congrArg Subrepresentation.toSubmodule h : (⊥ : Submodule ℂ (V ⊗[ℂ] W)) = ⊤)
  have h1 : ∀ (g : G) (B : W →ₗ[ℂ] W), ∀ x ∈ S.toSubmodule,
      TensorProduct.map (ρ g) B x ∈ S.toSubmodule := by
    intro g B
    have hB : B ∈ Submodule.span ℂ (Set.range σ) := sσ ▸ Submodule.mem_top
    induction hB using Submodule.span_induction with
    | mem B hB =>
      obtain ⟨h, rfl⟩ := hB
      intro x hx
      exact S.apply_mem_toSubmodule (g, h) hx
    | zero => intro x _; simp
    | add B C _ _ hB hC =>
      intro x hx
      rw [TensorProduct.map_add_right, LinearMap.add_apply]
      exact add_mem (hB x hx) (hC x hx)
    | smul c B _ hB =>
      intro x hx
      rw [TensorProduct.map_smul_right, LinearMap.smul_apply]
      exact Submodule.smul_mem _ _ (hB x hx)
  have h2 : ∀ (A : V →ₗ[ℂ] V) (B : W →ₗ[ℂ] W), ∀ x ∈ S.toSubmodule,
      TensorProduct.map A B x ∈ S.toSubmodule := by
    intro A B
    have hA : A ∈ Submodule.span ℂ (Set.range ρ) := sρ ▸ Submodule.mem_top
    induction hA using Submodule.span_induction with
    | mem A hA =>
      obtain ⟨g, rfl⟩ := hA
      exact h1 g B
    | zero => intro x _; simp
    | add A C _ _ hA hC =>
      intro x hx
      rw [TensorProduct.map_add_left, LinearMap.add_apply]
      exact add_mem (hA x hx) (hC x hx)
    | smul c A _ hA =>
      intro x hx
      rw [TensorProduct.map_smul_left, LinearMap.smul_apply]
      exact Submodule.smul_mem _ _ (hA x hx)
  have h3 : ∀ (F : V ⊗[ℂ] W →ₗ[ℂ] V ⊗[ℂ] W), ∀ x ∈ S.toSubmodule, F x ∈ S.toSubmodule := by
    intro F
    obtain ⟨t, rfl⟩ := (homTensorHomEquiv ℂ V W V W).surjective F
    induction t using TensorProduct.induction_on with
    | zero => intro x _; simp
    | tmul A B =>
      intro x hx
      rw [homTensorHomEquiv_apply, TensorProduct.homTensorHomMap_apply]
      exact h2 A B x hx
    | add s t hs ht =>
      intro x hx
      rw [map_add, LinearMap.add_apply]
      exact add_mem (hs x hx) (ht x hx)
  by_cases hS : S.toSubmodule = ⊥
  · exact Or.inl (Subrepresentation.toSubmodule_injective hS)
  · right
    obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hS
    apply Subrepresentation.toSubmodule_injective
    change S.toSubmodule = ⊤
    refine eq_top_iff.2 fun y _ => ?_
    obtain ⟨f, hf⟩ := Module.Projective.exists_dual_eq_one ℂ hx0
    have := h3 (f.smulRight y) x hx
    simpa [hf] using this
end GlobalTheory.OuterTensor
