-- Prove2me | solution 1 for GordanGenProof.fm_vec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:52:39.9738+00:00
-- url     : https://prove2.me/submissions/219c8cdf-7584-46cc-bd47-cdcfaa2d8d1a

import Mathlib
import Definitions.Def_Formalism_UnipotentAdelicQuotients_GordanCones
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GordanIntegerMultiple_ExistsIntMultiple
import Theorems.Thm_GordanGenProof_fm_scalar
import Theorems.Thm_GordanGenProof_fm_dot

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open GordanGenProof
open Finset
namespace GordanGenProof
theorem _root_.solution {n : ℕ} (P : Finset ((Fin n → ℚ) × ℚ)) (x : Fin n → ℚ) :
    (∃ t : ℚ, ∀ p ∈ P, 0 ≤ p.1 ⬝ᵥ x + p.2 * t) ↔ x ∈ hcone (fmSet P) id := by
  refine (fm_scalar P (fun p => p.1 ⬝ᵥ x) (fun p => p.2)).trans ?_
  constructor
  · rintro ⟨h0, h1⟩
    show ∀ a ∈ fmSet P, 0 ≤ id a ⬝ᵥ x
    intro a ha
    rcases Finset.mem_union.1 ha with ha | ha
    · obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 ha
      rw [Finset.mem_filter] at hp
      exact h0 p hp.1 hp.2
    · obtain ⟨⟨p, q⟩, hpq, rfl⟩ := Finset.mem_image.1 ha
      simp only [Finset.mem_product, Finset.mem_filter] at hpq
      show 0 ≤ (p.2 • q.1 - q.2 • p.1) ⬝ᵥ x
      rw [fm_dot]
      exact h1 p hpq.1.1 q hpq.2.1 hpq.1.2 hpq.2.2
  · intro h
    have h' : ∀ a ∈ fmSet P, 0 ≤ a ⬝ᵥ x := h
    refine ⟨fun p hp hz => h' p.1 (Finset.mem_union_left _
      (Finset.mem_image_of_mem _ (Finset.mem_filter.2 ⟨hp, hz⟩))), fun p hp q hq hcp hcq => ?_⟩
    have h2 := h' (p.2 • q.1 - q.2 • p.1) (Finset.mem_union_right _ (Finset.mem_image.2
      ⟨(p, q), Finset.mem_product.2 ⟨Finset.mem_filter.2 ⟨hp, hcp⟩, Finset.mem_filter.2 ⟨hq, hcq⟩⟩, rfl⟩))
    rw [fm_dot] at h2
    exact h2
end GordanGenProof
