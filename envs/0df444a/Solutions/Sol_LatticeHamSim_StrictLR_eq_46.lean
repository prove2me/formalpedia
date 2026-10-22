-- Prove2me | solution 1 for LatticeHamSim.StrictLR.eq_46
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T12:21:44.190292+00:00
-- url     : https://prove2.me/submissions/121cdd46-43b5-4503-9440-1350a7036472

import Mathlib
import Definitions.Def_LatticeHamSim_StrictLR_Setting
open scoped Matrix.Norms.L2Operator

set_option autoImplicit false
open LatticeHamSim.StrictLR

theorem solution {Λ : Type*} [Fintype Λ] [DecidableEq Λ] [MetricSpace Λ] {q : ℕ}
    (h : Finset Λ → Matrix (Λ → Fin q) (Λ → Fin q) ℂ)
    (hloc : ∀ X : Finset Λ, 1 < Metric.diam (X : Set Λ) → h X = 0)
    (ζ₀ : ℝ) (hζ₀ : ∀ x : Λ, ∑ Q ∈ Finset.univ.filter (fun Q => x ∈ Q), (Q.card : ℝ) * ‖h Q‖ ≤ ζ₀)
    (P S : Finset Λ) (d : ℝ) :
    ∑ Q ∈ Finset.univ.filter (fun Q => LatticeHamSim.CommLR.meets P Q),
        (Q.card : ℝ) * ‖h Q‖ * (if LatticeHamSim.CommLR.setDist Q S ≤ d then 1 else 0) ≤
      ζ₀ * ∑ p ∈ P, (if Metric.infDist p (S : Set Λ) ≤ d + 1 then (1 : ℝ) else 0) := by
  have hw0 : ∀ Q : Finset Λ, 0 ≤ ‖h Q‖ := fun Q => norm_nonneg _
  have step1 : ∑ Q ∈ Finset.univ.filter (fun Q => LatticeHamSim.CommLR.meets P Q),
        (Q.card : ℝ) * ‖h Q‖ * (if LatticeHamSim.CommLR.setDist Q S ≤ d then 1 else 0) ≤
      ∑ Q ∈ Finset.univ.filter (fun Q => LatticeHamSim.CommLR.meets P Q),
        ∑ p ∈ P, (if Metric.infDist p (S : Set Λ) ≤ d + 1 then
          (if p ∈ Q then (Q.card : ℝ) * ‖h Q‖ else 0) else 0) := by
    apply Finset.sum_le_sum
    intro Q hQ
    rw [Finset.mem_filter] at hQ
    have h1 : (P ∩ Q).Nonempty := hQ.2
    obtain ⟨p, hp⟩ := h1
    have hnn : ∀ p' ∈ P, 0 ≤ (if Metric.infDist p' (S : Set Λ) ≤ d + 1 then
          (if p' ∈ Q then (Q.card : ℝ) * ‖h Q‖ else 0) else 0) := by
      intro p' _
      split_ifs <;> first | exact le_rfl | exact mul_nonneg (Nat.cast_nonneg _) (hw0 Q)
    by_cases hd : LatticeHamSim.CommLR.setDist Q S ≤ d
    · rw [if_pos hd, mul_one]
      by_cases hz : h Q = 0
      · calc (Q.card : ℝ) * ‖h Q‖ = 0 := by rw [hz, norm_zero, mul_zero]
          _ ≤ _ := Finset.sum_nonneg hnn
      · have hdiam : Metric.diam (Q : Set Λ) ≤ 1 := by
          by_contra hc
          exact hz (hloc Q (not_le.mp hc))
        have hpP := (Finset.mem_inter.mp hp).1
        have hpQ := (Finset.mem_inter.mp hp).2
        have hinf : Metric.infDist p (S : Set Λ) ≤ d + 1 := by
          unfold LatticeHamSim.CommLR.setDist at hd
          by_cases hne : (Q ×ˢ S).Nonempty
          · rw [dif_pos hne] at hd
            obtain ⟨⟨q, s⟩, hqs, hqseq⟩ := Finset.exists_mem_eq_inf' hne (fun p => dist p.1 p.2)
            rw [hqseq] at hd
            have hq := (Finset.mem_product.mp hqs).1
            have hs := (Finset.mem_product.mp hqs).2
            have h2 : dist p q ≤ 1 :=
              (Metric.dist_le_diam_of_mem (Q.finite_toSet.isBounded) hpQ hq).trans hdiam
            have h3 : dist p s ≤ dist p q + dist q s := dist_triangle _ _ _
            have h4 : Metric.infDist p (S : Set Λ) ≤ dist p s := Metric.infDist_le_dist_of_mem hs
            simp only at hd
            linarith
          · rw [dif_neg hne] at hd
            have hSe : (S : Set Λ) = ∅ := by
              by_contra hS
              apply hne
              obtain ⟨s, hs⟩ := Set.nonempty_iff_ne_empty.mpr hS
              exact ⟨(p, s), Finset.mem_product.mpr ⟨hpQ, hs⟩⟩
            rw [hSe, Metric.infDist_empty]
            linarith
        have := Finset.single_le_sum (f := fun p' => (if Metric.infDist p' (S : Set Λ) ≤ d + 1 then
          (if p' ∈ Q then (Q.card : ℝ) * ‖h Q‖ else 0) else 0)) hnn hpP
        simpa [hinf, hpQ] using this
    · rw [if_neg hd, mul_zero]
      exact Finset.sum_nonneg hnn
  refine step1.trans ?_
  rw [Finset.sum_comm, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro p _
  by_cases hp : Metric.infDist p (S : Set Λ) ≤ d + 1
  · simp only [hp, if_true, mul_one]
    calc ∑ Q ∈ Finset.univ.filter (fun Q => LatticeHamSim.CommLR.meets P Q),
          (if p ∈ Q then (Q.card : ℝ) * ‖h Q‖ else 0)
        = ∑ Q ∈ (Finset.univ.filter (fun Q => LatticeHamSim.CommLR.meets P Q)).filter (fun Q => p ∈ Q),
            (Q.card : ℝ) * ‖h Q‖ := by
          exact (Finset.sum_filter _ _).symm
      _ ≤ ∑ Q ∈ Finset.univ.filter (fun Q => p ∈ Q), (Q.card : ℝ) * ‖h Q‖ := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro Q hQ
            rw [Finset.mem_filter] at hQ ⊢
            exact ⟨Finset.mem_univ _, hQ.2⟩
          · intro Q _ _; exact mul_nonneg (Nat.cast_nonneg _) (hw0 Q)
      _ ≤ ζ₀ := hζ₀ p
  · simp [hp]
