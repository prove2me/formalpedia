-- Prove2me | solution 1 for GlobalTheory.lift_square_presentation_of_flat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:36:07.109035+00:00
-- url     : https://prove2.me/submissions/eb6016e4-18f3-4f85-9ad1-d823c0abe274

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_KerInfMapLeMapMulKerOfFlatTargetStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LeSupKerMulOfLeSupMaximalMulSectionStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LiftSquarePresentationOfFlat
import Theorems.Thm_GlobalTheory_T_ker_inf_map_le_map_mul_ker_of_flat_target
import Theorems.Thm_GlobalTheory_T_le_sup_ker_mul_of_le_sup_maximal_mul_section


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution : ∀ (O B A k H σ : Type) [CommRing O] [IsLocalRing O] [CommRing B] [CommRing A] [Algebra O B] [Algebra O A] [Algebra B A] [IsScalarTower O B A] [Module.Flat B A] [Field k] [CommRing H] [Algebra k H] [Fintype σ] (ε : A →ₐ[O] O) (π : O →+* k) (ρ : A →+* H) (εH : H →ₐ[k] k) (x : σ → A), Function.Surjective π → RingHom.ker π = IsLocalRing.maximalIdeal O → (∀ c : O, ρ (algebraMap O A c) = algebraMap k H (π c)) → (∀ a, εH (ρ a) = π (ε a)) → RingHom.ker ρ = (RingHom.ker (π.comp ((ε : A →+* O).comp (algebraMap B A)))).map (algebraMap B A) → Function.Surjective (MvPolynomial.aeval x : MvPolynomial σ B →ₐ[B] A) → (RingHom.ker (MvPolynomial.aeval x : MvPolynomial σ B →ₐ[B] A)).FG → ∀ g : σ → MvPolynomial σ k, (∀ i, MvPolynomial.aeval (fun j => ρ (x j)) (g i) = 0) → RingHom.ker (MvPolynomial.aeval (fun j => ρ (x j)) : MvPolynomial σ k →ₐ[k] H) ≤ Ideal.span (Set.range g) ⊔ RingHom.ker (εH.comp (MvPolynomial.aeval (fun j => ρ (x j)) : MvPolynomial σ k →ₐ[k] H)) * RingHom.ker (MvPolynomial.aeval (fun j => ρ (x j)) : MvPolynomial σ k →ₐ[k] H) → ∃ f : σ → MvPolynomial σ B, (∀ i, MvPolynomial.aeval x (f i) = 0) ∧ RingHom.ker (MvPolynomial.aeval x : MvPolynomial σ B →ₐ[B] A) ≤ Ideal.span (Set.range f) ⊔ (RingHom.ker ε).comap (MvPolynomial.aeval x : MvPolynomial σ B →ₐ[B] A) * RingHom.ker (MvPolynomial.aeval x : MvPolynomial σ B →ₐ[B] A) := by
  intro O B A k H σ _ _ _ _ _ _ _ _ _ _ _ _ _ ε π ρ εH x hπ hker hρO hε hρ hx hfg g hg hJ
  classical
  set τ : B →+* k := π.comp ((ε : A →+* O).comp (algebraMap B A)) with hτ
  have hτb : ∀ b, τ b = π (ε (algebraMap B A b)) := fun b => rfl
  have hτO : ∀ c, τ (algebraMap O B c) = π c := by
    intro c
    rw [hτb, ← IsScalarTower.algebraMap_apply, AlgHom.commutes]
    rfl
  have hτs : Function.Surjective τ := by
    intro y
    obtain ⟨c, rfl⟩ := hπ y
    exact ⟨_, hτO c⟩
  have hρB : ∀ b, ρ (algebraMap B A b) = algebraMap k H (τ b) := by
    intro b
    have h1 : b - algebraMap O B (ε (algebraMap B A b)) ∈ RingHom.ker τ := by
      rw [RingHom.mem_ker, map_sub, hτO, hτb, sub_self]
    have h2 : algebraMap B A (b - algebraMap O B (ε (algebraMap B A b))) ∈ RingHom.ker ρ := by
      rw [hρ]
      exact Ideal.mem_map_of_mem _ h1
    rw [RingHom.mem_ker, map_sub, map_sub, ← IsScalarTower.algebraMap_apply, hρO,
      sub_eq_zero] at h2
    rw [h2, hτb]
  set Ψ : MvPolynomial σ B →ₐ[B] A := MvPolynomial.aeval x with hΨ
  set Φ : MvPolynomial σ k →ₐ[k] H := MvPolynomial.aeval (fun j => ρ (x j)) with hΦ
  set T : MvPolynomial σ B →+* MvPolynomial σ k := MvPolynomial.map τ with hT
  have hcomm : ∀ F, ρ (Ψ F) = Φ (T F) := by
    intro F
    induction F using MvPolynomial.induction_on with
    | C a => simp [hΨ, hΦ, hT, hρB]
    | add p q hp hq => simp only [map_add, hp, hq]
    | mul_X p i hp =>
      simp only [map_mul, hp]
      simp [hΨ, hΦ, hT]
  have hTs : Function.Surjective T := MvPolynomial.map_surjective τ hτs
  have hTk : RingHom.ker T = (RingHom.ker τ).map (algebraMap B (MvPolynomial σ B)) :=
    MvPolynomial.ker_map τ
  have hlift : ∀ G, Φ G = 0 → ∃ F, Ψ F = 0 ∧ T F = G := by
    intro G hG
    obtain ⟨F0, rfl⟩ := hTs G
    have h1 : Ψ F0 ∈ ((RingHom.ker τ).map (algebraMap B (MvPolynomial σ B))).map
        (Ψ : MvPolynomial σ B →+* A) := by
      rw [Ideal.map_map, AlgHom.comp_algebraMap, ← hρ, RingHom.mem_ker, hcomm, hG]
    rw [Ideal.mem_map_iff_of_surjective (Ψ : MvPolynomial σ B →+* A) hx] at h1
    obtain ⟨F1, hF1, hF⟩ := h1
    rw [← hTk, RingHom.mem_ker] at hF1
    refine ⟨F0 - F1, ?_, ?_⟩
    · rw [map_sub, sub_eq_zero]
      exact hF.symm
    · rw [map_sub, hF1, sub_zero]
  choose f hf hfT using fun i => hlift (g i) (hg i)
  refine ⟨f, hf, ?_⟩
  let η : MvPolynomial σ B →ₐ[O] O := ε.comp (Ψ.restrictScalars O)
  have hη : ∀ F, η F = ε (Ψ F) := fun F => rfl
  have hn : ∀ F, F ∈ (IsLocalRing.maximalIdeal O).comap η ↔ εH (Φ (T F)) = 0 := by
    intro F
    rw [Ideal.mem_comap, ← hker, RingHom.mem_ker, ← hcomm, hε, hη]
  have key : RingHom.ker Ψ ≤ Ideal.span (Set.range f) ⊔
      (IsLocalRing.maximalIdeal O).comap η * RingHom.ker Ψ := by
    have hle : Ideal.span (Set.range g) ⊔ RingHom.ker (εH.comp Φ) * RingHom.ker Φ ≤
        (Ideal.span (Set.range f) ⊔
          (IsLocalRing.maximalIdeal O).comap η * RingHom.ker Ψ).map T := by
      rw [Ideal.map_sup, Ideal.map_mul]
      refine sup_le_sup ?_ (Ideal.mul_mono ?_ ?_)
      · rw [Ideal.span_le]
        rintro _ ⟨i, rfl⟩
        rw [← hfT i]
        exact Ideal.mem_map_of_mem _ (Ideal.subset_span ⟨i, rfl⟩)
      · intro G hG
        obtain ⟨F, rfl⟩ := hTs G
        exact Ideal.mem_map_of_mem _ ((hn F).2 hG)
      · intro G hG
        obtain ⟨F, hF, rfl⟩ := hlift G hG
        exact Ideal.mem_map_of_mem _ hF
    have hS : Ideal.span (Set.range f) ⊔
        (IsLocalRing.maximalIdeal O).comap η * RingHom.ker Ψ ≤ RingHom.ker Ψ := by
      refine sup_le ?_ Ideal.mul_le_right
      rw [Ideal.span_le]
      rintro _ ⟨i, rfl⟩
      exact hf i
    have hp : (RingHom.ker τ).map (algebraMap B (MvPolynomial σ B)) ≤
        (IsLocalRing.maximalIdeal O).comap η := by
      rw [← hTk]
      intro F hF
      rw [hn, (RingHom.mem_ker).1 hF, map_zero, map_zero]
    intro F hF
    have h1 : T F ∈ RingHom.ker Φ := by
      rw [RingHom.mem_ker, ← hcomm, (RingHom.mem_ker).1 hF, map_zero]
    obtain ⟨F1, hF1, hF'⟩ := (Ideal.mem_map_iff_of_surjective T hTs).1 (hle (hJ h1))
    have h2 : F - F1 ∈ RingHom.ker Ψ ⊓
        (RingHom.ker τ).map (algebraMap B (MvPolynomial σ B)) := by
      refine ⟨sub_mem hF (hS hF1), ?_⟩
      rw [← hTk]
      show T (F - F1) = 0
      rw [map_sub, hF', sub_self]
    have h3 := Ideal.mul_mono_left hp
      (GlobalTheory.T.ker_inf_map_le_map_mul_ker_of_flat_target B (MvPolynomial σ B) A Ψ hx (RingHom.ker τ) h2)
    have h4 : F = F1 + (F - F1) := by ring
    rw [h4]
    exact add_mem hF1 (Ideal.mem_sup_right h3)
  exact GlobalTheory.T.le_sup_ker_mul_of_le_sup_maximal_mul_section O (MvPolynomial σ B) η _ _ hfg key
end GlobalTheory
