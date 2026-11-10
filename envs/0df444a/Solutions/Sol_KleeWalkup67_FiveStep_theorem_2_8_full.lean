-- Prove2me | solution 1 for KleeWalkup67.FiveStep.theorem_2_8_full
-- status  : ACCEPTED   (disprove)
-- author  : @kmehltretter82
-- created : 2026-11-09T11:38:21.473177+00:00
-- url     : https://prove2.me/submissions/577a77eb-3631-41cf-af6d-2f2d1745cf6a

import Definitions.Def_KleeWalkup67_Support_Classes

open scoped RealInnerProductSpace
open KleeWalkup67.FiveStep

private lemma inner_fin1 (u v : EuclideanSpace ℝ (Fin 1)) : ⟪u, v⟫ = u 0 * v 0 := by
  simp [PiLp.inner_apply, mul_comm]

private lemma no_strict_between (α β u t v : ℝ) (hut : u ≤ t) (htv : t ≤ v)
    (hu : α * u ≤ β) (hv : α * v ≤ β) (ht : β < α * t) : False := by
  rcases le_total 0 α with hα | hα <;> nlinarith

theorem solution : ¬ ((∀ d n : ℕ, 1 ≤ d → d < n →
      ∃ (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ),
        Support.IsClass a b ∧ IsSimple a b ∧ Bornology.IsBounded (Hirsch.Hpoly a b) ∧
        ∃ x ∈ Set.extremePoints ℝ (Hirsch.Hpoly a b),
        ∃ y ∈ Set.extremePoints ℝ (Hirsch.Hpoly a b),
          (2 * d ≤ n → Disjoint (TightSet a b x) (TightSet a b y)) ∧
          ∃ L : ℕ, Hirsch.Reach (Hirsch.Hpoly a b) L x y ∧
            (∀ k < L, ¬ Hirsch.Reach (Hirsch.Hpoly a b) k x y) ∧
            (∀ (c : Fin n → EuclideanSpace ℝ (Fin d)) (e : Fin n → ℝ),
              Support.IsClass c e → Bornology.IsBounded (Hirsch.Hpoly c e) →
              Hirsch.DiamLE (Hirsch.Hpoly c e) L)) ∧
    (∀ d n : ℕ, 2 ≤ d → d < n →
      ∃ (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ),
        Support.IsClass a b ∧ IsSimple a b ∧
        ∃ x ∈ Set.extremePoints ℝ (Hirsch.Hpoly a b),
        ∃ y ∈ Set.extremePoints ℝ (Hirsch.Hpoly a b),
          Support.IncidentUnboundedEdge a b x ∧ Support.IncidentUnboundedEdge a b y ∧
          (2 * d ≤ n → Disjoint (TightSet a b x) (TightSet a b y)) ∧
          ∃ L : ℕ, Hirsch.Reach (Hirsch.Hpoly a b) L x y ∧
            (∀ k < L, ¬ Hirsch.Reach (Hirsch.Hpoly a b) k x y) ∧
            (∀ (c : Fin n → EuclideanSpace ℝ (Fin d)) (e : Fin n → ℝ),
              Support.IsClass c e → Hirsch.DiamLE (Hirsch.Hpoly c e) L))) := by
  intro h
  rcases h.1 1 3 (by decide) (by decide) with ⟨a, b, ⟨_, _, ⟨_, hirr⟩, _⟩, _⟩
  rcases hirr 0 with ⟨x0, hx0_le, hx0_gt⟩
  rcases hirr 1 with ⟨x1, hx1_le, hx1_gt⟩
  rcases hirr 2 with ⟨x2, hx2_le, hx2_gt⟩
  have h10 := hx0_le 1 (by decide)
  have h20 := hx0_le 2 (by decide)
  have h01 := hx1_le 0 (by decide)
  have h21 := hx1_le 2 (by decide)
  have h02 := hx2_le 0 (by decide)
  have h12 := hx2_le 1 (by decide)
  simp only [inner_fin1] at hx0_gt hx1_gt hx2_gt h10 h20 h01 h21 h02 h12
  rcases le_total (x0 0) (x1 0) with h_01 | h_10 <;>
    rcases le_total (x1 0) (x2 0) with h_12 | h_21
  · exact no_strict_between (a 1 0) (b 1) (x0 0) (x1 0) (x2 0) h_01 h_12 h10 h12 hx1_gt
  · rcases le_total (x0 0) (x2 0) with h_02 | h_20
    · exact no_strict_between (a 2 0) (b 2) (x0 0) (x2 0) (x1 0) h_02 h_21 h20 h21 hx2_gt
    · exact no_strict_between (a 0 0) (b 0) (x2 0) (x0 0) (x1 0) h_20 h_01 h02 h01 hx0_gt
  · rcases le_total (x0 0) (x2 0) with h_02 | h_20
    · exact no_strict_between (a 0 0) (b 0) (x1 0) (x0 0) (x2 0) h_10 h_02 h01 h02 hx0_gt
    · exact no_strict_between (a 2 0) (b 2) (x1 0) (x2 0) (x0 0) h_12 h_20 h21 h20 hx2_gt
  · exact no_strict_between (a 1 0) (b 1) (x2 0) (x1 0) (x0 0) h_21 h_10 h12 h10 hx1_gt
