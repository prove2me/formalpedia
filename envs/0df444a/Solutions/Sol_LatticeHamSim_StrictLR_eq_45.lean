-- Prove2me | solution 1 for LatticeHamSim.StrictLR.eq_45
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T12:12:37.365642+00:00
-- url     : https://prove2.me/submissions/de07f458-677d-4f95-8619-33a43ef51841

import Mathlib
import Definitions.Def_LatticeHamSim_StrictLR_Setting
open scoped Matrix.Norms.L2Operator

set_option autoImplicit false
open LatticeHamSim.StrictLR

theorem solution {Λ : Type*} [Fintype Λ] [DecidableEq Λ] [MetricSpace Λ] {q : ℕ}
    (h : Finset Λ → Matrix (Λ → Fin q) (Λ → Fin q) ℂ)
    (hloc : ∀ X : Finset Λ, 1 < Metric.diam (X : Set Λ) → h X = 0)
    (ζ₀ : ℝ) (hζ₀ : ∀ x : Λ, ∑ Q ∈ Finset.univ.filter (fun Q => x ∈ Q), (Q.card : ℝ) * ‖h Q‖ ≤ ζ₀)
    (P S : Finset Λ) :
    ∑ Q ∈ Finset.univ.filter (fun Q => LatticeHamSim.CommLR.meets P Q ∧ LatticeHamSim.CommLR.meets Q S), ‖h Q‖ ≤
      ζ₀ * ∑ p ∈ P, (if Metric.infDist p (S : Set Λ) ≤ 1 then (1 : ℝ) else 0) := by
  have hw0 : ∀ Q : Finset Λ, 0 ≤ ‖h Q‖ := fun Q => norm_nonneg _
  have step1 : ∑ Q ∈ Finset.univ.filter (fun Q => LatticeHamSim.CommLR.meets P Q ∧ LatticeHamSim.CommLR.meets Q S), ‖h Q‖ ≤
      ∑ Q ∈ Finset.univ.filter (fun Q => LatticeHamSim.CommLR.meets P Q ∧ LatticeHamSim.CommLR.meets Q S),
        ∑ p ∈ P, (if Metric.infDist p (S : Set Λ) ≤ 1 then (if p ∈ Q then ‖h Q‖ else 0) else 0) := by
    apply Finset.sum_le_sum
    intro Q hQ
    rw [Finset.mem_filter] at hQ
    have h1 : (P ∩ Q).Nonempty := hQ.2.1
    have h2 : (Q ∩ S).Nonempty := hQ.2.2
    obtain ⟨p, hp⟩ := h1
    obtain ⟨s, hs⟩ := h2
    have hnn : ∀ p' ∈ P, 0 ≤ (if Metric.infDist p' (S : Set Λ) ≤ 1 then (if p' ∈ Q then ‖h Q‖ else 0) else 0) := by
      intro p' _
      split_ifs <;> simp [hw0 Q]
    by_cases hz : h Q = 0
    · calc ‖h Q‖ = 0 := by rw [hz, norm_zero]
        _ ≤ _ := Finset.sum_nonneg hnn
    · have hdiam : Metric.diam (Q : Set Λ) ≤ 1 := by
        by_contra hc
        exact hz (hloc Q (not_le.mp hc))
      have hpP := (Finset.mem_inter.mp hp).1
      have hpQ := (Finset.mem_inter.mp hp).2
      have hsQ := (Finset.mem_inter.mp hs).1
      have hsS := (Finset.mem_inter.mp hs).2
      have hdist : dist p s ≤ 1 :=
        (Metric.dist_le_diam_of_mem (Q.finite_toSet.isBounded) hpQ hsQ).trans hdiam
      have hinf : Metric.infDist p (S : Set Λ) ≤ 1 :=
        (Metric.infDist_le_dist_of_mem hsS).trans hdist
      have := Finset.single_le_sum (f := fun p' => (if Metric.infDist p' (S : Set Λ) ≤ 1 then (if p' ∈ Q then ‖h Q‖ else 0) else 0)) hnn hpP
      simpa [hinf, hpQ] using this
  refine step1.trans ?_
  rw [Finset.sum_comm, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro p _
  by_cases hp : Metric.infDist p (S : Set Λ) ≤ 1
  · simp only [hp, if_true, mul_one]
    calc ∑ Q ∈ Finset.univ.filter (fun Q => LatticeHamSim.CommLR.meets P Q ∧ LatticeHamSim.CommLR.meets Q S),
          (if p ∈ Q then ‖h Q‖ else 0)
        = ∑ Q ∈ (Finset.univ.filter (fun Q => LatticeHamSim.CommLR.meets P Q ∧ LatticeHamSim.CommLR.meets Q S)).filter (fun Q => p ∈ Q), ‖h Q‖ := by
          exact (Finset.sum_filter _ _).symm
      _ ≤ ∑ Q ∈ Finset.univ.filter (fun Q => p ∈ Q), ‖h Q‖ := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro Q hQ
            rw [Finset.mem_filter] at hQ ⊢
            exact ⟨Finset.mem_univ _, hQ.2⟩
          · intro Q _ _; exact hw0 Q
      _ ≤ ∑ Q ∈ Finset.univ.filter (fun Q => p ∈ Q), (Q.card : ℝ) * ‖h Q‖ := by
          apply Finset.sum_le_sum
          intro Q hQ
          have hpQ : p ∈ Q := (Finset.mem_filter.mp hQ).2
          have : (1 : ℝ) ≤ Q.card := by exact_mod_cast Finset.card_pos.mpr ⟨p, hpQ⟩
          nlinarith [hw0 Q]
      _ ≤ ζ₀ := hζ₀ p
  · simp [hp]
