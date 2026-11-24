-- Prove2me | solution 1 for GlobalTheory.reducedArtinian_involution_split
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:37:44.811629+00:00
-- url     : https://prove2.me/submissions/8c983cd9-db05-40b5-99b4-242de8c8059d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ReducedArtinianInvolutionIdempotentSplit
import Theorems.Thm_GlobalTheory_reducedArtinian_exists_idem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Polynomial
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution :
    ∀ (R : Type) [CommRing R] [IsReduced R] [IsArtinianRing R] (σ : R →+* R), (∀ x, σ (σ x) = x) →
      ∃ e f : R, IsIdempotentElem e ∧ IsIdempotentElem f ∧ e * σ e = 0 ∧ e + σ e + f = 1 ∧
        ∀ w, w * σ w = 0 → w * f = 0 := by
  intro R _ _ _ σ hσ
  let S : Set (Ideal R) := {I | ∃ e : R, e * e = e ∧ e * σ e = 0 ∧ I = Ideal.span {1 - e - σ e}}
  have hS : S.Nonempty := ⟨_, 0, by simp, by simp, rfl⟩
  obtain ⟨I, ⟨e, he, heσ, rfl⟩, hmin⟩ := WellFounded.has_min wellFounded_lt S hS
  have hσe : σ e * σ e = σ e := by rw [← map_mul, he]
  set f := 1 - e - σ e with hfdef
  have hf : f * f = f := by linear_combination he + hσe + 2 * heσ
  have hσf : σ f = f := by simp only [hfdef, map_sub, map_one, hσ]; ring
  have hef : e * f = 0 := by linear_combination -he - heσ
  have hσef : σ e * f = 0 := by linear_combination -hσe - heσ
  refine ⟨e, f, he, hf, heσ, by ring, ?_⟩
  intro w hw
  by_contra hwf
  set w' := w * f with hw'def
  have hw'σ : w' * σ w' = 0 := by
    rw [hw'def, map_mul, hσf]; linear_combination (f * f) * hw
  obtain ⟨ε, a, hε, hεa, hw'ε⟩ := reducedArtinian_exists_idem w'
  have hεne : ε ≠ 0 := by
    intro h0; rw [h0, mul_zero] at hw'ε; exact hwf hw'ε.symm
  have hεσ : ε * σ ε = 0 := by
    rw [hεa, map_mul]; linear_combination (a * σ a) * hw'σ
  have hw'f : w' * f = w' := by rw [hw'def, mul_assoc, hf]
  have hεf : ε * f = ε := by rw [hεa]; linear_combination a * hw'f
  have hσεf : σ ε * f = σ ε := by
    have := congrArg σ hεf; rw [map_mul, hσf] at this; exact this
  have hσε : σ ε * σ ε = σ ε := by rw [← map_mul, hε]
  have heε : e * ε = 0 := by linear_combination (-e) * hεf + ε * hef
  have heσε : e * σ ε = 0 := by linear_combination (-e) * hσεf + σ ε * hef
  have hσeε : σ e * ε = 0 := by linear_combination (-σ e) * hεf + ε * hσef
  have hmem : Ideal.span {1 - (e + ε) - σ (e + ε)} ∈ S :=
    ⟨e + ε, by linear_combination he + hε + 2 * heε,
      by rw [map_add]; linear_combination heσ + heσε + hσeε + hεσ, rfl⟩
  apply hmin _ hmem
  have hff : f * (1 - (e + ε) - σ (e + ε)) = 1 - (e + ε) - σ (e + ε) := by
    rw [map_add]; linear_combination hf - hεf - hσεf
  refine lt_of_le_of_ne ?_ ?_
  · rw [Ideal.span_singleton_le_span_singleton]
    exact ⟨_, hff.symm⟩
  · intro hEq
    have : f ∈ Ideal.span {1 - (e + ε) - σ (e + ε)} := by
      rw [hEq]; exact Ideal.mem_span_singleton_self f
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp this
    apply hεne
    have hεg : ε * (1 - (e + ε) - σ (e + ε)) = 0 := by
      rw [map_add]; linear_combination -heε - hσeε - hε - hεσ
    linear_combination -hεf - ε * hc + c * hεg
end GlobalTheory
