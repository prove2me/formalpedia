-- Prove2me | solution 1 for GlobalTheory.TraceIso.nonempty_linear_equiv_of_charpoly_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T21:58:09.940057+00:00
-- url     : https://prove2.me/submissions/e80644b6-fb30-4dcd-81ab-c547eaeee20b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NonemptyLinearEquivOfCharpolyEq
import Theorems.Thm_GlobalTheory_TraceIso_tr_congr
import Theorems.Thm_GlobalTheory_TraceIso_tr_prod
import Theorems.Thm_GlobalTheory_TraceIso_finiteDimensional_sub
import Theorems.Thm_GlobalTheory_TraceIso_finrank_eq_zero_of_hom
import Theorems.Thm_GlobalTheory_TraceIso_split_of_hom

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.TraceIso
open Module
variable {k A : Type} [Field k] [Ring A] [Algebra k A]
namespace GlobalTheory.TraceIso
theorem _root_.solution [CharZero k] (n : ℕ) : ∀ (V W : Type) [AddCommGroup V] [Module k V] [Module A V]
    [IsScalarTower k A V] [AddCommGroup W] [Module k W] [Module A W] [IsScalarTower k A W]
    [FiniteDimensional k V] [FiniteDimensional k W] [IsSemisimpleModule A V] [IsSemisimpleModule A W],
    finrank k V + finrank k W ≤ n → (∀ a : A, tr k V a = tr k W a) → Nonempty (V ≃ₗ[A] W) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  have step : ∀ (V W : Type) [AddCommGroup V] [Module k V] [Module A V]
      [IsScalarTower k A V] [AddCommGroup W] [Module k W] [Module A W] [IsScalarTower k A W]
      [FiniteDimensional k V] [FiniteDimensional k W] [IsSemisimpleModule A V] [IsSemisimpleModule A W],
      finrank k V + finrank k W ≤ n → (∀ a : A, tr k V a = tr k W a) → ∀ f : V →ₗ[A] W, f ≠ 0 →
      Nonempty (V ≃ₗ[A] W) := by
    intro V W _ _ _ _ _ _ _ _ _ _ _ _ hn h f hf
    obtain ⟨P, Q, S, ⟨e₁⟩, ⟨e₂⟩, hP, hQ⟩ := split_of_hom (k := k) f hf
    haveI := finiteDimensional_sub (k := k) P
    haveI := finiteDimensional_sub (k := k) Q
    haveI := finiteDimensional_sub (k := k) S
    obtain ⟨e⟩ := ih (finrank k P + finrank k Q) (by omega) P Q le_rfl fun a => by
      have := h a
      rw [tr_congr e₁, tr_congr e₂, tr_prod, tr_prod] at this
      exact add_right_cancel this
    exact ⟨e₁.trans ((e.prodCongr (LinearEquiv.refl A _)).trans e₂.symm)⟩
  intro V W _ _ _ _ _ _ _ _ _ _ _ _ hn h
  by_cases h₁ : ∀ f : V →ₗ[A] W, f = 0
  · by_cases h₂ : ∀ f : W →ₗ[A] V, f = 0
    · haveI : Subsingleton V := Module.finrank_zero_iff.1 (finrank_eq_zero_of_hom h h₁ h₂)
      haveI : Subsingleton W :=
        Module.finrank_zero_iff.1 (finrank_eq_zero_of_hom (fun a => (h a).symm) h₂ h₁)
      exact ⟨LinearEquiv.ofSubsingleton V W⟩
    · push_neg at h₂
      obtain ⟨f, hf⟩ := h₂
      obtain ⟨e⟩ := step W V (by omega) (fun a => (h a).symm) f hf
      exact ⟨e.symm⟩
  · push_neg at h₁
    obtain ⟨f, hf⟩ := h₁
    exact step V W hn h f hf
end GlobalTheory.TraceIso
