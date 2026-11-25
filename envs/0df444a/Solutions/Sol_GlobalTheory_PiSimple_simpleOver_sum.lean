-- Prove2me | solution 1 for GlobalTheory.PiSimple.simpleOver_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:02:59.194177+00:00
-- url     : https://prove2.me/submissions/23af6aaa-d0c9-480f-acbe-36debe21a7d8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_SimpleOverStableSubmoduleTensorPureKernelSpanStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_OperatorStablePiTensorPureKernelSpanStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_SimpleOver
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_SimpleOverStableSubmodulePiTensor
import Theorems.Thm_GlobalTheory_PiSimple_simpleOver_of_equiv
import Theorems.Thm_GlobalTheory_T_operatorStable_piTensorPureKernelSpan
import Theorems.Thm_GlobalTheory_T_simpleOverStableSubmodule_tensorPureKernelSpan


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
open GlobalTheory GlobalTheory.PiSimple
open GlobalTheory.TensHead
namespace GlobalTheory.PiSimple
theorem _root_.solution {α β : Type} (hα : PP α) (hβ : PP β) [DecidableEq (α ⊕ β)]
    (N : α ⊕ β → Type) [∀ i, AddCommGroup (N i)] [∀ i, Module ℂ (N i)]
    (Op : ∀ i, Set (Module.End ℂ (N i))) (K : ∀ i, Submodule ℂ (N i))
    (hr : ∀ i, Module.rank ℂ (N i) ≤ Cardinal.aleph0)
    (hrl : Module.rank ℂ (⨂[ℂ] a, N (.inl a)) ≤ Cardinal.aleph0)
    (hs : ∀ i, Stab (Op i) (K i)) (hso : ∀ i, SimpleOver (Op i) (K i)) :
    SimpleOver (piOps Op) (piKer K) := by
  classical
  have hA := hα (fun a => N (.inl a)) (fun a => Op (.inl a)) (fun a => K (.inl a))
    (fun a => hr _) (fun a => hs _) (fun a => hso _)
  have hB := hβ (fun b => N (.inr b)) (fun b => Op (.inr b)) (fun b => K (.inr b))
    (fun b => hr _) (fun b => hs _) (fun b => hso _)
  have hT := GlobalTheory.T.simpleOverStableSubmodule_tensorPureKernelSpan (piOps (fun a => Op (.inl a))) (piOps (fun b => Op (.inr b)))
    (piKer (fun a => K (.inl a))) (piKer (fun b => K (.inr b))) hrl
    (GlobalTheory.T.operatorStable_piTensorPureKernelSpan _ _ (fun a => hs _)) (GlobalTheory.T.operatorStable_piTensorPureKernelSpan _ _ (fun b => hs _)) hA hB
  let e := (PiTensorProduct.tmulEquivDep ℂ N).symm
  refine simpleOver_of_equiv e _ _ _ _ ?_ ?_ hT
  · apply le_antisymm
    · rw [piKer, Submodule.map_span, Submodule.span_le]
      rintro _ ⟨_, ⟨y, ⟨i, hi⟩, rfl⟩, rfl⟩
      refine Submodule.subset_span ⟨PiTensorProduct.tprod ℂ (fun a => y (.inl a)),
        PiTensorProduct.tprod ℂ (fun b => y (.inr b)), ?_, by simp [e]⟩
      cases i with
      | inl a => exact Or.inl (Submodule.subset_span ⟨_, ⟨a, hi⟩, rfl⟩)
      | inr b => exact Or.inr (Submodule.subset_span ⟨_, ⟨b, hi⟩, rfl⟩)
    · set Q := (piKer K).map e.toLinearMap with hQ
      have pure : ∀ (y₁ : ∀ a, N (.inl a)) (y₂ : ∀ b, N (.inr b)),
          ((∃ a, y₁ a ∈ K (.inl a)) ∨ (∃ b, y₂ b ∈ K (.inr b))) →
          PiTensorProduct.tprod ℂ y₁ ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ y₂ ∈ Q := by
        intro y₁ y₂ h
        refine ⟨PiTensorProduct.tprod ℂ (fun i => Sum.rec y₁ y₂ i),
          Submodule.subset_span ⟨_, ?_, rfl⟩, by simp [e]⟩
        rcases h with ⟨a, ha⟩ | ⟨b, hb⟩
        · exact ⟨.inl a, ha⟩
        · exact ⟨.inr b, hb⟩
      have left : ∀ (y₁ : ∀ a, N (.inl a)), (∃ a, y₁ a ∈ K (.inl a)) →
          ∀ z, PiTensorProduct.tprod ℂ y₁ ⊗ₜ[ℂ] z ∈ Q := by
        intro y₁ h z
        have : (⊤ : Submodule ℂ (⨂[ℂ] b, N (.inr b))) ≤
            Q.comap (TensorProduct.mk ℂ _ _ (PiTensorProduct.tprod ℂ y₁)) := by
          rw [← PiTensorProduct.span_tprod_eq_top, Submodule.span_le]
          rintro _ ⟨y₂, rfl⟩
          exact pure y₁ y₂ (Or.inl h)
        exact this Submodule.mem_top
      have right : ∀ (y₂ : ∀ b, N (.inr b)), (∃ b, y₂ b ∈ K (.inr b)) →
          ∀ x, x ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ y₂ ∈ Q := by
        intro y₂ h x
        have : (⊤ : Submodule ℂ (⨂[ℂ] a, N (.inl a))) ≤
            Q.comap ((TensorProduct.mk ℂ _ _).flip (PiTensorProduct.tprod ℂ y₂)) := by
          rw [← PiTensorProduct.span_tprod_eq_top, Submodule.span_le]
          rintro _ ⟨y₁, rfl⟩
          exact pure y₁ y₂ (Or.inr h)
        exact this Submodule.mem_top
      rw [tensKer, Submodule.span_le]
      rintro _ ⟨x, z, hxz, rfl⟩
      rcases hxz with hx | hz
      · have : piKer (fun a => K (.inl a)) ≤ Q.comap ((TensorProduct.mk ℂ _ _).flip z) := by
          rw [piKer, Submodule.span_le]
          rintro _ ⟨y₁, h, rfl⟩
          exact left y₁ h z
        exact this hx
      · have : piKer (fun b => K (.inr b)) ≤ Q.comap (TensorProduct.mk ℂ _ _ x) := by
          rw [piKer, Submodule.span_le]
          rintro _ ⟨y₂, h, rfl⟩
          exact right y₂ h x
        exact this hz
  · rintro _ (⟨_, ⟨a, g, hg, rfl⟩, rfl⟩ | ⟨_, ⟨b, g, hg, rfl⟩, rfl⟩)
    · refine ⟨piOp (Sum.inl a) g, ⟨_, g, hg, rfl⟩, fun x => ?_⟩
      have H : (TensorProduct.map (piOp a g) LinearMap.id) ∘ₗ e.toLinearMap =
          e.toLinearMap ∘ₗ piOp (Sum.inl a) g := by
        apply PiTensorProduct.ext
        apply MultilinearMap.ext
        intro y
        simp only [e, piOp, LinearMap.compMultilinearMap_apply, LinearMap.comp_apply,
          LinearEquiv.coe_coe, PiTensorProduct.map_tprod, PiTensorProduct.tmulEquivDep_symm_apply,
          TensorProduct.map_tmul, LinearMap.id_apply]
        congr 2
        · funext a'
          by_cases h : a' = a
          · subst h; simp
          · rw [Function.update_of_ne h, Function.update_of_ne (fun h' => h (Sum.inl_injective h'))]
        · funext b'
          rw [Function.update_of_ne (Sum.inr_ne_inl)]
          rfl
      exact LinearMap.congr_fun H x
    · refine ⟨piOp (Sum.inr b) g, ⟨_, g, hg, rfl⟩, fun x => ?_⟩
      have H : (TensorProduct.map LinearMap.id (piOp b g)) ∘ₗ e.toLinearMap =
          e.toLinearMap ∘ₗ piOp (Sum.inr b) g := by
        apply PiTensorProduct.ext
        apply MultilinearMap.ext
        intro y
        simp only [e, piOp, LinearMap.compMultilinearMap_apply, LinearMap.comp_apply,
          LinearEquiv.coe_coe, PiTensorProduct.map_tprod, PiTensorProduct.tmulEquivDep_symm_apply,
          TensorProduct.map_tmul, LinearMap.id_apply]
        congr 2
        · funext a'
          rw [Function.update_of_ne (Sum.inl_ne_inr)]
          rfl
        · funext b'
          by_cases h : b' = b
          · subst h; simp
          · rw [Function.update_of_ne h, Function.update_of_ne (fun h' => h (Sum.inr_injective h'))]
      exact LinearMap.congr_fun H x
end GlobalTheory.PiSimple
