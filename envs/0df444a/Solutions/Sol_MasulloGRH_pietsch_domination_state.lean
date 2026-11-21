-- Prove2me | solution 1 for MasulloGRH.pietsch_domination_state
-- status  : ACCEPTED   (prove)
-- author  : @Ismael Correa
-- created : 2026-11-20T23:47:19.346151+00:00
-- url     : https://prove2.me/submissions/af7308cf-7102-426b-b76b-4c61620fd826

import Mathlib
import Theorems.Thm_MasulloGRH_exists_state_nonpos_on_cone
import Theorems.Thm_MasulloGRH_exists_cone_of_finite_sums_inf_le

set_option autoImplicit false

open MasulloGRH

universe u

theorem solution (E : Type u)
    [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    (p q : Seminorm ℂ E)
    (hAS : ∀ (n : ℕ) (x : Fin n → E) (c : ℝ),
      (∀ f : StrongDual ℂ E, (∀ y, ‖f y‖ ≤ q y) → ∑ i, ‖f (x i)‖ ≤ c) →
      ∑ i, p (x i) ≤ c) :
    ∃ Λ : (StrongDual ℂ E → ℝ) → ℝ,
      (∀ φ ψ : StrongDual ℂ E → ℝ,
        (∃ M : ℝ, ∀ f : StrongDual ℂ E, (∀ y, ‖f y‖ ≤ q y) → |φ f| ≤ M) →
        (∃ M : ℝ, ∀ f : StrongDual ℂ E, (∀ y, ‖f y‖ ≤ q y) → |ψ f| ≤ M) →
        Λ (φ + ψ) = Λ φ + Λ ψ) ∧
      (∀ (r : ℝ) (φ : StrongDual ℂ E → ℝ),
        (∃ M : ℝ, ∀ f : StrongDual ℂ E, (∀ y, ‖f y‖ ≤ q y) → |φ f| ≤ M) →
        Λ (r • φ) = r * Λ φ) ∧
      (∀ φ ψ : StrongDual ℂ E → ℝ,
        (∃ M : ℝ, ∀ f : StrongDual ℂ E, (∀ y, ‖f y‖ ≤ q y) → |φ f| ≤ M) →
        (∃ M : ℝ, ∀ f : StrongDual ℂ E, (∀ y, ‖f y‖ ≤ q y) → |ψ f| ≤ M) →
        (∀ f : StrongDual ℂ E, (∀ y, ‖f y‖ ≤ q y) → φ f ≤ ψ f) → Λ φ ≤ Λ ψ) ∧
      Λ (fun _ => 1) = 1 ∧
      ∀ x : E, p x ≤ Λ (fun f => ‖f x‖) := by
  set S : Set (StrongDual ℂ E) := {f | ∀ y, ‖f y‖ ≤ q y} with hSdef
  let u : E → StrongDual ℂ E → ℝ := fun x f => p x - ‖f x‖
  have hu : ∀ x, ∃ M : ℝ, ∀ t ∈ S, |u x t| ≤ M := by
    intro x
    refine ⟨p x + q x, fun t ht => ?_⟩
    have h1 : ‖t x‖ ≤ q x := ht x
    have h2 : 0 ≤ ‖t x‖ := norm_nonneg _
    have h3 : 0 ≤ p x := apply_nonneg p x
    rw [abs_le]; constructor <;> simp only [u] <;> linarith
  have hsum : ∀ (n : ℕ) (i : Fin n → E) (ε : ℝ), 0 < ε → ∃ t ∈ S, ∑ j, u (i j) t ≤ ε := by
    intro n i ε hε
    by_contra hcon
    push_neg at hcon
    have key := hAS n i (∑ j, p (i j) - ε) (fun f hf => by
      have := hcon f hf
      simp only [u, Finset.sum_sub_distrib] at this
      linarith)
    linarith
  obtain ⟨K, huK, hadd, hsmul, hbdd, hinf⟩ :=
    exists_cone_of_finite_sums_inf_le (StrongDual ℂ E) E S u hu hsum
  have hS : S.Nonempty := ⟨0, fun y => by simp⟩
  obtain ⟨Λ, h1, h2, h3, h4, h5⟩ := exists_state_nonpos_on_cone _ S hS K hadd hsmul hbdd hinf
  refine ⟨Λ, h1, h2, h3, h4, fun x => ?_⟩
  have hb1 : ∃ M : ℝ, ∀ t ∈ S, |(fun _ : StrongDual ℂ E => (1 : ℝ)) t| ≤ M :=
    ⟨1, fun t _ => by simp⟩
  have hbx : ∃ M : ℝ, ∀ t ∈ S, |(fun f : StrongDual ℂ E => ‖f x‖) t| ≤ M :=
    ⟨q x, fun t ht => by simpa [abs_of_nonneg (norm_nonneg _)] using ht x⟩
  have hdecomp : u x = (p x) • (fun _ : StrongDual ℂ E => (1 : ℝ)) +
      (-1 : ℝ) • (fun f : StrongDual ℂ E => ‖f x‖) := by
    funext f; simp [u, sub_eq_add_neg]
  have hsm1 : ∃ M : ℝ, ∀ t ∈ S, |((p x) • (fun _ : StrongDual ℂ E => (1 : ℝ))) t| ≤ M :=
    ⟨|p x|, fun t _ => by simp⟩
  have hsm2 : ∃ M : ℝ, ∀ t ∈ S, |((-1 : ℝ) • (fun f : StrongDual ℂ E => ‖f x‖)) t| ≤ M := by
    obtain ⟨M, hM⟩ := hbx
    exact ⟨M, fun t ht => by simpa using hM t ht⟩
  have hval : Λ (u x) = p x - Λ (fun f => ‖f x‖) := by
    rw [hdecomp, h1 _ _ hsm1 hsm2, h2 _ _ hb1, h2 _ _ hbx, h4]
    ring
  have := h5 (u x) (huK x)
  linarith
