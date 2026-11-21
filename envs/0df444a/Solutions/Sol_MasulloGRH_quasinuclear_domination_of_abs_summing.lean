-- Prove2me | solution 1 for MasulloGRH.quasinuclear_domination_of_abs_summing
-- status  : ACCEPTED   (prove)
-- author  : @Ismael Correa
-- created : 2026-11-20T23:23:25.932063+00:00
-- url     : https://prove2.me/submissions/052c12e8-0029-4bac-bfeb-1f8f549373d2

import Theorems.Thm_MasulloGRH_pietsch_hilbertian_two_summing
import Theorems.Thm_MasulloGRH_quasinuclear_of_hilbertian_two_summing_chain

set_option autoImplicit false

open MasulloGRH

universe u

theorem solution (E : Type u)
    [AddCommGroup E] [Module ℂ E] [TopologicalSpace E] (hE : IsHLCS E)
    (hAS : ∀ p : Seminorm ℂ E, Continuous p → ∃ q : Seminorm ℂ E, Continuous q ∧
      ∀ (n : ℕ) (x : Fin n → E) (c : ℝ),
        (∀ f : StrongDual ℂ E, (∀ y, ‖f y‖ ≤ q y) → ∑ i, ‖f (x i)‖ ≤ c) →
        ∑ i, p (x i) ≤ c) :
    ∀ p : Seminorm ℂ E, Continuous p →
      ∃ (q : Seminorm ℂ E) (f : ℕ → StrongDual ℂ E) (c : ℕ → ℝ),
        Continuous q ∧ (∀ n, 0 ≤ c n) ∧ Summable c ∧ (∀ n x, ‖f n x‖ ≤ q x) ∧
        ∀ x, p x ≤ ∑' n, c n * ‖f n x‖ := by
  intro p hp
  obtain ⟨q₁, hq₁, hAS₁⟩ := hAS p hp
  obtain ⟨k₁, hk₁, hpk₁, hk₁q₁, hpar₁, hs₁⟩ :=
    pietsch_hilbertian_two_summing E hE p q₁ hp hq₁ hAS₁
  obtain ⟨q₂, hq₂, hAS₂⟩ := hAS q₁ hq₁
  obtain ⟨k₂, hk₂, hq₁k₂, hk₂q₂, hpar₂, hs₂⟩ :=
    pietsch_hilbertian_two_summing E hE q₁ q₂ hq₁ hq₂ hAS₂
  obtain ⟨q₃, hq₃, hAS₃⟩ := hAS q₂ hq₂
  obtain ⟨k₃, hk₃, hq₂k₃, hk₃q₃, hpar₃, hs₃⟩ :=
    pietsch_hilbertian_two_summing E hE q₂ q₃ hq₂ hq₃ hAS₃
  have h₁₂ : ∀ (n : ℕ) (x : Fin n → E) (c : ℝ),
      (∀ f : StrongDual ℂ E, (∀ y, ‖f y‖ ≤ k₂ y) → ∑ i, ‖f (x i)‖ ^ 2 ≤ c) →
      ∑ i, k₁ (x i) ^ 2 ≤ c := by
    intro n x c hc
    exact hs₁ n x c (fun f hf => hc f (fun y => (hf y).trans (hq₁k₂ y)))
  have h₂₃ : ∀ (n : ℕ) (x : Fin n → E) (c : ℝ),
      (∀ f : StrongDual ℂ E, (∀ y, ‖f y‖ ≤ k₃ y) → ∑ i, ‖f (x i)‖ ^ 2 ≤ c) →
      ∑ i, k₂ (x i) ^ 2 ≤ c := by
    intro n x c hc
    exact hs₂ n x c (fun f hf => hc f (fun y => (hf y).trans (hq₂k₃ y)))
  obtain ⟨f, c, hc0, hcs, hf, hdom⟩ :=
    quasinuclear_of_hilbertian_two_summing_chain E hE k₁ k₂ k₃ hk₃ hpar₁ hpar₂ hpar₃ h₁₂ h₂₃
  exact ⟨k₃, f, c, hk₃, hc0, hcs, hf, fun x => (hpk₁ x).trans (hdom x)⟩

