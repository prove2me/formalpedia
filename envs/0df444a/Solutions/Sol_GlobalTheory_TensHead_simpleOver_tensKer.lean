-- Prove2me | solution 1 for GlobalTheory.TensHead.simpleOver_tensKer
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:51:34.50624+00:00
-- url     : https://prove2.me/submissions/29bd346c-b5e4-4973-b543-56ace5fc93b0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_SimpleTensorProductOperatorStableCountableStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_SimpleOver
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_SimpleOverStableSubmoduleTensorPureKernelSpan
import Theorems.Thm_GlobalTheory_TensHead_quot_simple
import Theorems.Thm_GlobalTheory_TensHead_ker_map_mkQ_le
import Theorems.Thm_GlobalTheory_T_simple_tensor_product_operatorStable_countable


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
open GlobalTheory GlobalTheory.TensHead
namespace GlobalTheory.TensHead
theorem _root_.solution : ∀ {V₀ V₁ : Type} [AddCommGroup V₀] [Module ℂ V₀] [AddCommGroup V₁] [Module ℂ V₁]
    (A : Set (Module.End ℂ V₀)) (B : Set (Module.End ℂ V₁)) (K₀ : Submodule ℂ V₀) (K₁ : Submodule ℂ V₁),
    Module.rank ℂ V₀ ≤ Cardinal.aleph0 → GlobalTheory.TensHead.Stab A K₀ → GlobalTheory.TensHead.Stab B K₁ →
    GlobalTheory.TensHead.SimpleOver A K₀ → GlobalTheory.TensHead.SimpleOver B K₁ →
    GlobalTheory.TensHead.SimpleOver (GlobalTheory.TensHead.tensOps A B) (GlobalTheory.TensHead.tensKer K₀ K₁) := by
  intro V₀ V₁ _ _ _ _ A B K₀ K₁ hr hA hB hsA hsB N hN hKN
  set φ := TensorProduct.map K₀.mkQ K₁.mkQ with hφ
  have hker : LinearMap.ker φ ≤ N := (ker_map_mkQ_le K₀ K₁).trans hKN
  have hstU : Stab (tensOps (quotOps A K₀) (quotOps B K₁)) (N.map φ) := by
    rintro f hf _ ⟨x, hx, rfl⟩
    rcases hf with ⟨f', ⟨g, hg, hfg⟩, rfl⟩ | ⟨f', ⟨g, hg, hfg⟩, rfl⟩
    · have hc : TensorProduct.map f' LinearMap.id ∘ₗ φ = φ ∘ₗ TensorProduct.map g LinearMap.id := by
        rw [hφ, ← TensorProduct.map_comp, ← TensorProduct.map_comp, hfg]; rfl
      refine ⟨TensorProduct.map g LinearMap.id x, hN _ (Or.inl ⟨g, hg, rfl⟩) x hx, ?_⟩
      exact (LinearMap.congr_fun hc x).symm
    · have hc : TensorProduct.map LinearMap.id f' ∘ₗ φ = φ ∘ₗ TensorProduct.map LinearMap.id g := by
        rw [hφ, ← TensorProduct.map_comp, ← TensorProduct.map_comp, hfg]; rfl
      refine ⟨TensorProduct.map LinearMap.id g x, hN _ (Or.inr ⟨g, hg, rfl⟩) x hx, ?_⟩
      exact (LinearMap.congr_fun hc x).symm
  rcases GlobalTheory.T.simple_tensor_product_operatorStable_countable (quotOps A K₀) (quotOps B K₁) ((rank_quotient_le K₀).trans hr)
    (quot_simple A K₀ hA hsA) (quot_simple B K₁ hB hsB) _ hstU with h | h
  · left
    refine le_antisymm ?_ hKN
    intro x hx
    apply ker_map_mkQ_le K₀ K₁
    rw [LinearMap.mem_ker, ← Submodule.mem_bot ℂ, ← h]
    exact Submodule.mem_map_of_mem hx
  · right
    rw [eq_top_iff]
    intro x _
    have : φ x ∈ N.map φ := h ▸ Submodule.mem_top
    obtain ⟨y, hy, hxy⟩ := this
    have : x - y ∈ LinearMap.ker φ := by simp [hxy]
    simpa using add_mem (hker this) hy
end GlobalTheory.TensHead
