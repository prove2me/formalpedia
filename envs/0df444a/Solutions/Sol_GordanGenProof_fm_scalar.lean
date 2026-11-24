-- Prove2me | solution 1 for GordanGenProof.fm_scalar
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:45:29.586643+00:00
-- url     : https://prove2.me/submissions/6559785b-d8e5-46c5-a7a0-514aa299a10b

import Mathlib
import Definitions.Def_Formalism_UnipotentAdelicQuotients_GordanCones
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GordanIntegerMultiple_ExistsIntMultiple

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
theorem _root_.solution {κ : Type*} (P : Finset κ) (u c : κ → ℚ) :
    (∃ t : ℚ, ∀ p ∈ P, 0 ≤ u p + c p * t) ↔
      (∀ p ∈ P, c p = 0 → 0 ≤ u p) ∧
      (∀ p ∈ P, ∀ q ∈ P, 0 < c p → c q < 0 → 0 ≤ c p * u q - c q * u p) := by
  classical
  constructor
  · rintro ⟨t, ht⟩
    refine ⟨fun p hp hc => by simpa [hc] using ht p hp, fun p hp q hq hcp hcq => ?_⟩
    have h1 := ht p hp
    have h2 := ht q hq
    nlinarith [mul_nonneg (neg_nonneg.2 hcq.le) h1, mul_nonneg hcp.le h2]
  · rintro ⟨h0, h1⟩
    obtain ⟨b, eb⟩ : ∃ b : κ → ℚ, ∀ p, c p ≠ 0 → c p * b p = -u p :=
      ⟨fun p => -u p * (c p)⁻¹, fun p hp => by
        show c p * (-u p * (c p)⁻¹) = -u p
        rw [mul_left_comm, mul_inv_cancel₀ hp, mul_one]⟩
    have key : ∀ p ∈ P, ∀ q ∈ P, 0 < c p → c q < 0 → b p ≤ b q := by
      intro p hp q hq hcp hcq
      by_contra hlt
      push_neg at hlt
      have e1 : c p * b p * c q = -u p * c q := by rw [eb p hcp.ne']
      have e2 : c q * b q * c p = -u q * c p := by rw [eb q hcq.ne]
      have hm := mul_pos (mul_pos hcp (neg_pos.2 hcq)) (sub_pos.2 hlt)
      have h3 := h1 p hp q hq hcp hcq
      nlinarith
    have good : ∀ t : ℚ, (∀ p ∈ P, 0 < c p → b p ≤ t) → (∀ q ∈ P, c q < 0 → t ≤ b q) →
        ∀ p ∈ P, 0 ≤ u p + c p * t := by
      intro t hlo hhi p hp
      rcases lt_trichotomy (c p) 0 with hn | hz | hpos
      · have h4 := mul_le_mul_of_nonpos_left (hhi p hp hn) hn.le
        rw [eb p hn.ne] at h4
        linarith
      · rw [hz, zero_mul, add_zero]
        exact h0 p hp hz
      · have h4 := mul_le_mul_of_nonneg_left (hlo p hp hpos) hpos.le
        rw [eb p hpos.ne'] at h4
        linarith
    by_cases hL : ∃ p ∈ P, 0 < c p
    · obtain ⟨p0, hp0, hcp0, hmax⟩ : ∃ p0 ∈ P, 0 < c p0 ∧ ∀ p ∈ P, 0 < c p → b p ≤ b p0 := by
        obtain ⟨p, hp, hc⟩ := hL
        have hne : (P.filter (fun p => 0 < c p)).Nonempty := ⟨p, Finset.mem_filter.2 ⟨hp, hc⟩⟩
        obtain ⟨p0, hp0, hm⟩ := Finset.exists_max_image _ b hne
        rw [Finset.mem_filter] at hp0
        exact ⟨p0, hp0.1, hp0.2, fun p hp hc => hm p (Finset.mem_filter.2 ⟨hp, hc⟩)⟩
      exact ⟨b p0, good _ hmax (fun q hq hcq => key p0 hp0 q hq hcp0 hcq)⟩
    · push_neg at hL
      by_cases hU : ∃ q ∈ P, c q < 0
      · obtain ⟨q0, hq0, hcq0, hmin⟩ : ∃ q0 ∈ P, c q0 < 0 ∧ ∀ q ∈ P, c q < 0 → b q0 ≤ b q := by
          obtain ⟨q, hq, hc⟩ := hU
          have hne : (P.filter (fun q => c q < 0)).Nonempty := ⟨q, Finset.mem_filter.2 ⟨hq, hc⟩⟩
          obtain ⟨q0, hq0, hm⟩ := Finset.exists_min_image _ b hne
          rw [Finset.mem_filter] at hq0
          exact ⟨q0, hq0.1, hq0.2, fun q hq hc => hm q (Finset.mem_filter.2 ⟨hq, hc⟩)⟩
        exact ⟨b q0, good _ (fun p hp hcp => absurd hcp (not_lt.2 (hL p hp))) hmin⟩
      · push_neg at hU
        exact ⟨0, good 0 (fun p hp hcp => absurd hcp (not_lt.2 (hL p hp)))
          (fun q hq hcq => absurd hcq (not_lt.2 (hU q hq)))⟩
end GordanGenProof
