-- Prove2me | solution 1 for ModernConvex.SLemma.projective_image_path_connected
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T14:48:19.181175+00:00
-- url     : https://prove2.me/submissions/ecbac261-fab5-4878-94b7-b6fd35d7e407

import Mathlib
import Definitions.Def_ModernConvex_SLemma_ProjectiveSpace
open ModernConvex.SLemma

theorem solution {n : ℕ}
    (Y : Set (Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1))
    (hY : ∀ x ∈ Y, ∀ x' ∈ Y, ∃ y ∈ Y, (JoinedIn Y x y ∨ JoinedIn Y x (-y)) ∧
      (JoinedIn Y x' y ∨ JoinedIn Y x' (-y))) :
    (∀ p ∈ canonicalProjection n '' Y, ∀ q ∈ canonicalProjection n '' Y,
        JoinedIn (canonicalProjection n '' Y) p q) ∧
      IsPreconnected (canonicalProjection n '' Y) := by

  have hc : Continuous (canonicalProjection n) := continuous_quotient_mk'
  have hneg : ∀ y, canonicalProjection n (-y) = canonicalProjection n y := by
    intro y; exact Quotient.sound (Or.inr rfl)
  have hJ : ∀ x y, (JoinedIn Y x y ∨ JoinedIn Y x (-y)) →
      JoinedIn (canonicalProjection n '' Y) (canonicalProjection n x) (canonicalProjection n y) := by
    intro x y h
    rcases h with h | h
    · exact h.map hc
    · have := h.map hc; rwa [hneg] at this
  have hpath : ∀ p ∈ canonicalProjection n '' Y, ∀ q ∈ canonicalProjection n '' Y,
      JoinedIn (canonicalProjection n '' Y) p q := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨x', hx', rfl⟩
    obtain ⟨y, _, h1, h2⟩ := hY x hx x' hx'
    exact (hJ x y h1).trans (hJ x' y h2).symm
  refine ⟨hpath, ?_⟩
  rcases (canonicalProjection n '' Y).eq_empty_or_nonempty with h | ⟨p, hp⟩
  · rw [h]; exact isPreconnected_empty
  · exact (isPathConnected_iff.2 ⟨⟨p, hp⟩, hpath⟩).isConnected.isPreconnected
