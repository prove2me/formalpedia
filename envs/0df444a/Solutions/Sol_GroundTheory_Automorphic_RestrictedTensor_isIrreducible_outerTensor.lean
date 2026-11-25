-- Prove2me | solution 1 for GroundTheory.Automorphic.RestrictedTensor.isIrreducible_outerTensor
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:08:45.562225+00:00
-- url     : https://prove2.me/submissions/03c329f6-ec09-4bae-b431-4c0893d82c36

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_GenWindow
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_OuterTensor
import Theorems.Thm_GroundTheory_Automorphic_RestrictedTensor_nontrivial_of_irreducible
import Theorems.Thm_GroundTheory_Automorphic_RestrictedTensor_outerTensor_tmul
import Theorems.Thm_GroundTheory_Automorphic_RestrictedTensor_exists_asAlgebraHom_eq
import Theorems.Thm_GroundTheory_Automorphic_RestrictedTensor_mem_span_mOrbit


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.RestrictedTensor
open Module Set TensorProduct
open scoped TensorProduct
variable {M₁ M₂ : Type*} [Monoid M₁] [Monoid M₂] {V₁ V₂ : Type*} [AddCommGroup V₁] [Module ℂ V₁]
  [AddCommGroup V₂] [Module ℂ V₂]
namespace GroundTheory.Automorphic.RestrictedTensor
theorem _root_.solution {ρ₁ : Representation ℂ M₁ V₁} {ρ₂ : Representation ℂ M₂ V₂}
    (hirr₁ : ρ₁.IsIrreducible) (hirr₂ : ρ₂.IsIrreducible)
    (hschur : ∀ T : End ℂ V₂, (∀ m, T * ρ₂ m = ρ₂ m * T) → ∃ c : ℂ, T = c • 1) :
    (outerTensor ρ₁ ρ₂).IsIrreducible := by
  classical
  haveI := hirr₁
  haveI := hirr₂
  set ρ := outerTensor ρ₁ ρ₂
  have hnt₁ := nontrivial_of_irreducible hirr₁
  have hnt₂ := nontrivial_of_irreducible hirr₂
  let b := Basis.ofVectorSpace ℂ V₂
  set F := TensorProduct.equivFinsuppOfBasisRight (M := V₁) b

  have key : ∀ Y : Subrepresentation ρ, Y ≠ ⊥ → ∀ a b', a ⊗ₜ[ℂ] b' ∈ Y.toSubmodule := by
    intro Y hY
    have hY' : Y.toSubmodule ≠ ⊥ := fun h => hY (Subrepresentation.toSubmodule_injective h)
    obtain ⟨y, hy, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hY'
    have hfy : F y ≠ 0 := fun h => hy0 (F.injective (h.trans (map_zero F).symm))
    obtain ⟨j₀, hj₀⟩ := Finsupp.ne_iff.1 hfy
    simp only [Finsupp.coe_zero, Pi.zero_apply] at hj₀

    let A : End ℂ V₂ := b.constr ℂ fun j => if j = j₀ then b j₀ else 0
    obtain ⟨r, hr⟩ := exists_asAlgebraHom_eq hirr₂ hschur A ((F y).support.image b)
    have hstab : ∀ r' : MonoidAlgebra ℂ M₂, ∀ z ∈ Y.toSubmodule,
        TensorProduct.map LinearMap.id (ρ₂.asAlgebraHom r') z ∈ Y.toSubmodule := by
      intro r' z hz
      induction r' using MonoidAlgebra.induction_on with
      | of m =>
        have := Y.apply_mem_toSubmodule (1, m) hz
        rw [MonoidAlgebra.of_apply, Representation.asAlgebraHom_single_one]
        have h1 : ρ (1, m) = TensorProduct.map LinearMap.id (ρ₂ m) := by
          show TensorProduct.map (ρ₁ 1) (ρ₂ m) = _
          rw [map_one]
          rfl
        rw [← h1]
        exact this
      | add f g hf hg =>
        rw [map_add, TensorProduct.map_add_right, LinearMap.add_apply]
        exact Y.toSubmodule.add_mem hf hg
      | smul c f hf =>
        rw [map_smul, TensorProduct.map_smul_right, LinearMap.smul_apply]
        exact Y.toSubmodule.smul_mem c hf
    have hy' : y = (F y).sum fun j a => a ⊗ₜ[ℂ] b j := by
      conv_lhs => rw [← F.symm_apply_apply y]
      exact TensorProduct.equivFinsuppOfBasisRight_symm_apply b (F y)
    have hpure : F y j₀ ⊗ₜ[ℂ] b j₀ ∈ Y.toSubmodule := by
      have := hstab r y hy
      rw [hy', map_finsuppSum] at this
      convert this using 1
      rw [Finsupp.sum, Finset.sum_eq_single j₀]
      · rw [TensorProduct.map_tmul, LinearMap.id_apply, hr _ (Finset.mem_image_of_mem _
          (Finsupp.mem_support_iff.2 hj₀))]
        simp [A]
      · intro j hj hjj
        rw [TensorProduct.map_tmul, LinearMap.id_apply, hr _ (Finset.mem_image_of_mem _ hj)]
        simp [A, hjj]
      · intro h
        exact absurd (Finsupp.mem_support_iff.2 hj₀) h

    intro a b'
    have h1 : ∀ a' ∈ Submodule.span ℂ (range fun m => ρ₁ m (F y j₀)),
        a' ⊗ₜ[ℂ] b j₀ ∈ Y.toSubmodule := by
      intro a' ha'
      induction ha' using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨m, rfl⟩ := hx
        have := Y.apply_mem_toSubmodule (m, 1) hpure
        simpa [ρ, outerTensor_tmul] using this
      | zero => simp
      | add x z _ _ hx hz => rw [TensorProduct.add_tmul]; exact Y.toSubmodule.add_mem hx hz
      | smul c x _ hx => rw [← TensorProduct.smul_tmul']; exact Y.toSubmodule.smul_mem c hx
    have ha := h1 a (mem_span_mOrbit (ρ := ρ₁) hj₀ a)
    have h2 : ∀ b'' ∈ Submodule.span ℂ (range fun m => ρ₂ m (b j₀)),
        a ⊗ₜ[ℂ] b'' ∈ Y.toSubmodule := by
      intro b'' hb''
      induction hb'' using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨m, rfl⟩ := hx
        have := Y.apply_mem_toSubmodule (1, m) ha
        simpa [ρ, outerTensor_tmul] using this
      | zero => simp
      | add x z _ _ hx hz => rw [TensorProduct.tmul_add]; exact Y.toSubmodule.add_mem hx hz
      | smul c x _ hx => rw [TensorProduct.tmul_smul]; exact Y.toSubmodule.smul_mem c hx
    exact h2 b' (mem_span_mOrbit (ρ := ρ₂) (b.ne_zero j₀) b')
  have hbt : (⊥ : Subrepresentation ρ) ≠ ⊤ := by
    intro h
    obtain ⟨a, ha⟩ := exists_ne (0 : V₁)
    obtain ⟨v₂, hv₂⟩ := exists_ne (0 : V₂)
    obtain ⟨j, hj⟩ : ∃ j, b.repr v₂ j ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact hv₂ (b.repr.injective (Finsupp.ext fun j => by simp [hcon j]))
    have : a ⊗ₜ[ℂ] v₂ ∈ (⊥ : Subrepresentation ρ).toSubmodule := by rw [h]; trivial
    have h0 : a ⊗ₜ[ℂ] v₂ = 0 := this
    have := congrArg (fun z => F z j) h0
    simp only [F, TensorProduct.equivFinsuppOfBasisRight_apply_tmul_apply, map_zero,
      Finsupp.coe_zero, Pi.zero_apply] at this
    exact (smul_ne_zero hj ha) this
  refine { exists_pair_ne := ⟨⊥, ⊤, hbt⟩, eq_bot_or_eq_top := fun Y => ?_ }
  by_cases hY : Y = ⊥
  · exact Or.inl hY
  right
  apply Subrepresentation.toSubmodule_injective
  refine eq_top_iff.2 fun z _ => ?_
  have := TensorProduct.span_tmul_eq_top ℂ V₁ V₂
  have hz : z ∈ Submodule.span ℂ {t | ∃ a b', a ⊗ₜ[ℂ] b' = t} := by rw [this]; trivial
  refine Submodule.span_le.2 ?_ hz
  rintro _ ⟨a, b', rfl⟩
  exact key Y hY a b'
end GroundTheory.Automorphic.RestrictedTensor
