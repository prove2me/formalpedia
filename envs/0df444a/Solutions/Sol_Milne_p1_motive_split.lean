-- Prove2me | solution 1 for Milne.p1_motive_split
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T23:13:42.923254+00:00
-- url     : https://prove2.me/submissions/15783c02-330a-4bcd-84b2-b5b2458b3312

import Mathlib
import Definitions.Def_Milne_world
import Definitions.Def_Milne_motives
import Definitions.Def_Milne_zeta
universe u v

open Milne

theorem solution (W : CorrWorld.{u, v}) :
    ∃ i₀ : Hom W (H0 W) (P1M W),
      ∃ i₂ : Hom W (L1 W) (P1M W),
        ∃ p₀ : Hom W (P1M W) (H0 W),
          ∃ p₂ : Hom W (P1M W) (L1 W),
            homComp W i₀ p₀ = idM W (H0 W)
              ∧ homComp W i₂ p₂ = idM W (L1 W)
              ∧ homComp W i₂ p₀ = homZero W (L1 W) (H0 W)
              ∧ homComp W i₀ p₂ = homZero W (H0 W) (L1 W)
              ∧ homAdd W (homComp W p₀ i₀) (homComp W p₂ i₂) = idM W (P1M W)
    ∧ ∀ φ : Hom W (P1M W) (P1M W),
        ∃ a b : ℚ, φ.val = W.add (W.smul a W.e0) (W.smul b W.e2) := by
  refine ⟨⟨W.e0, (by show W.cc (W.cc W.e0 W.e0) (W.delta W.P1) = W.e0; rw [W.e0_idem, W.cc_id_right]), W.e0_deg⟩,
    ⟨W.e2, (by show W.cc (W.cc W.e2 W.e2) (W.delta W.P1) = W.e2; rw [W.e2_idem, W.cc_id_right]), W.e2_deg⟩,
    ⟨W.e0, (by show W.cc (W.cc (W.delta W.P1) W.e0) W.e0 = W.e0; rw [W.cc_id_left, W.e0_idem]), W.e0_deg⟩,
    ⟨W.e2, (by show W.cc (W.cc (W.delta W.P1) W.e2) W.e2 = W.e2; rw [W.cc_id_left, W.e2_idem]), W.e2_deg⟩,
    Subtype.ext W.e0_idem, Subtype.ext W.e2_idem, Subtype.ext W.e2_e0_zero,
    Subtype.ext W.e0_e2_zero, ?_, ?_⟩
  · apply Subtype.ext
    show W.add (W.cc W.e0 W.e0) (W.cc W.e2 W.e2) = W.delta W.P1
    rw [W.e0_idem, W.e2_idem, W.p1_diag]
  · intro φ
    exact W.endP1_span φ.val φ.property.2 φ.property.1
