-- Prove2me | solution 1 for GlobalTheory.TensHead.simple_tensor
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:38:57.260659+00:00
-- url     : https://prove2.me/submissions/c39b8a85-ff21-453a-922a-f7008a602135

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_SimpleOver
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DixmierSchurOfRankLeAleph0
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_SimpleTensorProductOperatorStableCountable
import Theorems.Thm_GlobalTheory_TensHead_exists_adjoin_agree

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
theorem _root_.solution :
    ∀ {S₀ S₁ : Type} [AddCommGroup S₀] [Module ℂ S₀] [AddCommGroup S₁] [Module ℂ S₁]
    (A : Set (Module.End ℂ S₀)) (B : Set (Module.End ℂ S₁)),
    Module.rank ℂ S₀ ≤ Cardinal.aleph0 →
    (∀ U : Submodule ℂ S₀, GlobalTheory.TensHead.Stab A U → U = ⊥ ∨ U = ⊤) →
    (∀ U : Submodule ℂ S₁, GlobalTheory.TensHead.Stab B U → U = ⊥ ∨ U = ⊤) →
    ∀ U : Submodule ℂ (S₀ ⊗[ℂ] S₁), GlobalTheory.TensHead.Stab (GlobalTheory.TensHead.tensOps A B) U →
      U = ⊥ ∨ U = ⊤ := by
  classical
  intro S₀ S₁ _ _ _ _ A B hrank hA hB U hU
  rcases eq_or_ne U ⊥ with h0 | h0
  · exact Or.inl h0
  right
  obtain ⟨t, htU, ht0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h0
  have hadj : ∀ r ∈ Algebra.adjoin ℂ A, ∀ z ∈ U, TensorProduct.map r LinearMap.id z ∈ U := by
    intro r hr
    induction hr using Algebra.adjoin_induction with
    | mem g hg => exact hU _ (Or.inl ⟨g, hg, rfl⟩)
    | algebraMap c =>
      intro z hz
      rw [Algebra.algebraMap_eq_smul_one, TensorProduct.map_smul_left, LinearMap.smul_apply,
        Module.End.one_eq_id, TensorProduct.map_id]
      exact U.smul_mem c hz
    | add f g _ _ hf hg =>
      intro z hz
      rw [TensorProduct.map_add_left]
      exact U.add_mem (hf z hz) (hg z hz)
    | mul f g _ _ hf hg =>
      intro z hz
      have : TensorProduct.map (f * g) (LinearMap.id : S₁ →ₗ[ℂ] S₁) =
          (TensorProduct.map f LinearMap.id) ∘ₗ (TensorProduct.map g LinearMap.id) := by
        rw [← TensorProduct.map_comp]; rfl
      rw [this]
      exact hf _ (hg z hz)
  let b := Module.Basis.ofVectorSpace ℂ S₀
  set c := TensorProduct.equivFinsuppOfBasisLeft b t with hc
  have ht : t = c.sum fun i n => b i ⊗ₜ[ℂ] n := by
    rw [hc, ← TensorProduct.equivFinsuppOfBasisLeft_symm_apply, LinearEquiv.symm_apply_apply]
  have hc0 : c ≠ 0 := by
    intro h
    apply ht0
    rw [ht, h, Finsupp.sum_zero_index]
  obtain ⟨i, hi⟩ := Finsupp.support_nonempty_iff.2 hc0
  have hbi : b i ≠ 0 := b.ne_zero i
  haveI : Nontrivial S₀ := ⟨⟨b i, 0, hbi⟩⟩
  obtain ⟨r, hr, hrp⟩ := exists_adjoin_agree A hrank hA ((b.coord i).smulRight (b i))
    (c.support.image b)
  have h1 : b i ⊗ₜ[ℂ] c i ∈ U := by
    have h2 := hadj r hr t htU
    have h3 : TensorProduct.map r LinearMap.id t = b i ⊗ₜ[ℂ] c i := by
      conv_lhs => rw [ht]
      rw [Finsupp.sum, map_sum, Finset.sum_eq_single i]
      · rw [TensorProduct.map_tmul, ← hrp _ (Finset.mem_image_of_mem b hi)]
        simp
      · intro j hj hji
        rw [TensorProduct.map_tmul, ← hrp _ (Finset.mem_image_of_mem b hj)]
        simp [Finsupp.single_apply, hji]
      · intro h; exact absurd hi h
    rwa [h3] at h2
  have h4 : U.comap (TensorProduct.mk ℂ S₀ S₁ (b i)) = ⊤ := by
    refine (hB _ ?_).resolve_left ?_
    · intro g hg y hy
      exact hU _ (Or.inr ⟨g, hg, rfl⟩) _ hy
    · intro h
      have : c i ∈ U.comap (TensorProduct.mk ℂ S₀ S₁ (b i)) := h1
      rw [h, Submodule.mem_bot] at this
      exact Finsupp.mem_support_iff.1 hi this
  have h5 : ∀ y, U.comap ((TensorProduct.mk ℂ S₀ S₁).flip y) = ⊤ := by
    intro y
    refine (hA _ ?_).resolve_left ?_
    · intro g hg x hx
      exact hU _ (Or.inl ⟨g, hg, rfl⟩) _ hx
    · intro h
      have h6 : y ∈ U.comap (TensorProduct.mk ℂ S₀ S₁ (b i)) := by rw [h4]; trivial
      have : b i ∈ U.comap ((TensorProduct.mk ℂ S₀ S₁).flip y) := h6
      rw [h, Submodule.mem_bot] at this
      exact hbi this
  rw [eq_top_iff]
  rintro z -
  induction z using TensorProduct.induction_on with
  | zero => exact U.zero_mem
  | tmul x y =>
    have : x ∈ U.comap ((TensorProduct.mk ℂ S₀ S₁).flip y) := by rw [h5]; trivial
    exact this
  | add x y hx hy => exact U.add_mem hx hy
end GlobalTheory.TensHead
