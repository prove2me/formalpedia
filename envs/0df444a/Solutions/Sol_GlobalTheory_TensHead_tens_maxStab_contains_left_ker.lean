-- Prove2me | solution 1 for GlobalTheory.TensHead.tens_maxStab_contains_left_ker
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:05:11.283627+00:00
-- url     : https://prove2.me/submissions/76464f87-c3ad-4584-8d9b-1058fb8b5457

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_LeKerOfLocalFiniteLengthToSimpleStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_SimpleOver
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_TensorMaximalStableContainsLeftKernel
import Theorems.Thm_GlobalTheory_T_le_ker_of_local_finite_length_to_simple
import Theorems.Thm_GlobalTheory_TensHead_MinStab_map


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
theorem _root_.solution : ∀ {M₀ V : Type} [AddCommGroup M₀] [Module ℂ M₀] [AddCommGroup V] [Module ℂ V]
    (Op₀ : Set (Module.End ℂ M₀)) (B : Set (Module.End ℂ V)) (Rel₀ K₀ : Submodule ℂ M₀),
    (∃ L : ℕ, ∀ (m : ℕ) (N : Fin m → Submodule ℂ M₀), StrictMono N →
        (∀ j, Rel₀ ≤ N j ∧ ∀ g ∈ Op₀, ∀ x ∈ N j, g x ∈ N j) → m ≤ L) →
    (∀ N : Submodule ℂ M₀, Rel₀ ≤ N → GlobalTheory.TensHead.Stab Op₀ N → N ≠ ⊤ → N ≤ K₀) →
    K₀ ≠ ⊤ → GlobalTheory.TensHead.Stab Op₀ K₀ →
    ∀ N' : Submodule ℂ (M₀ ⊗[ℂ] V),
      (∀ x ∈ Rel₀, ∀ y, x ⊗ₜ[ℂ] y ∈ N') → GlobalTheory.TensHead.Stab (GlobalTheory.TensHead.tensOps Op₀ B) N' →
      (∀ U, GlobalTheory.TensHead.Stab (GlobalTheory.TensHead.tensOps Op₀ B) U → N' ≤ U → U = N' ∨ U = ⊤) →
      ∀ x ∈ K₀, ∀ y, x ⊗ₜ[ℂ] y ∈ N' := by
  classical
  intro M₀ V _ _ _ _ Op₀ B Rel₀ K₀ hlen hmax hK hKs N' hrel hN'st hN'max x hx y

  let act : Module.End ℂ M₀ → Module.End ℂ ((M₀ ⊗[ℂ] V) ⧸ N') := fun g =>
    if hs : N' ≤ N'.comap (TensorProduct.map g LinearMap.id) then
      N'.mapQ N' (TensorProduct.map g LinearMap.id) hs else 0
  let bAct : Module.End ℂ V → Module.End ℂ ((M₀ ⊗[ℂ] V) ⧸ N') := fun h =>
    if hs : N' ≤ N'.comap (TensorProduct.map LinearMap.id h) then
      N'.mapQ N' (TensorProduct.map LinearMap.id h) hs else 0
  have hsg : ∀ g ∈ Op₀, N' ≤ N'.comap (TensorProduct.map g LinearMap.id) := by
    intro g hg z hz
    exact hN'st _ (Or.inl ⟨g, hg, rfl⟩) z hz
  have hsh : ∀ h ∈ B, N' ≤ N'.comap (TensorProduct.map LinearMap.id h) := by
    intro h hh z hz
    exact hN'st _ (Or.inr ⟨h, hh, rfl⟩) z hz
  have hactg : ∀ g ∈ Op₀, ∀ z, act g (N'.mkQ z) = N'.mkQ (TensorProduct.map g LinearMap.id z) := by
    intro g hg z
    simp only [act, dif_pos (hsg g hg), Submodule.mapQ_apply, Submodule.mkQ_apply]
  have hbacth : ∀ h ∈ B, ∀ z, bAct h (N'.mkQ z) = N'.mkQ (TensorProduct.map LinearMap.id h z) := by
    intro h hh z
    simp only [bAct, dif_pos (hsh h hh), Submodule.mapQ_apply, Submodule.mkQ_apply]
  let φ : M₀ →ₗ[ℂ] (M₀ ⊗[ℂ] V) ⧸ N' := N'.mkQ ∘ₗ (TensorProduct.mk ℂ M₀ V).flip y
  have hφ : ∀ x, φ x = N'.mkQ (x ⊗ₜ[ℂ] y) := fun x => rfl
  have key := GlobalTheory.T.le_ker_of_local_finite_length_to_simple Op₀ Rel₀ K₀ φ act (bAct '' B) hlen hmax hK hKs
    (by
      intro z hz
      rw [LinearMap.mem_ker, hφ, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      exact hrel z hz y)
    (by
      intro g hg
      ext z
      simp only [LinearMap.comp_apply, hφ, hactg g hg, TensorProduct.map_tmul, LinearMap.id_apply])
    (by
      rintro g hg b ⟨h, hh, rfl⟩
      apply Submodule.linearMap_qext
      apply TensorProduct.ext'
      intro u v
      simp only [LinearMap.comp_apply, Module.End.mul_apply, hactg g hg, hbacth h hh,
        TensorProduct.map_tmul, LinearMap.id_apply])
    (by
      intro U hU
      have hP : Stab (tensOps Op₀ B) (U.comap N'.mkQ) := by
        rintro f (⟨g, hg, rfl⟩ | ⟨h, hh, rfl⟩) z hz
        · rw [Submodule.mem_comap] at hz ⊢
          rw [← hactg g hg]
          exact hU _ (Or.inl ⟨g, hg, rfl⟩) _ hz
        · rw [Submodule.mem_comap] at hz ⊢
          rw [← hbacth h hh]
          exact hU _ (Or.inr ⟨h, hh, rfl⟩) _ hz
      have hle : N' ≤ U.comap N'.mkQ := by
        intro z hz
        rw [Submodule.mem_comap, Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero N').2 hz]
        exact U.zero_mem
      have hsurj : Function.Surjective N'.mkQ := Submodule.mkQ_surjective N'
      rcases hN'max _ hP hle with h1 | h1
      · left
        rw [← Submodule.map_comap_eq_of_surjective hsurj U, h1, Submodule.mkQ_map_self]
      · right
        rw [← Submodule.map_comap_eq_of_surjective hsurj U, h1, Submodule.map_top,
          LinearMap.range_eq_top.2 hsurj])
  have := key hx
  rw [LinearMap.mem_ker, hφ, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at this
  exact this
end GlobalTheory.TensHead
