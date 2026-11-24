-- Prove2me | solution 1 for GlobalTheory.GaussUnits.sum_ideal_of_exists
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T16:33:00.820576+00:00
-- url     : https://prove2.me/submissions/ff6acbfe-e842-49bd-b08d-029d5dc7957b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_GaussUnitsNormSq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ComplexConjugate Finset
open GlobalTheory
open GlobalTheory.GaussUnits
variable {R : Type} [CommRing R] [Fintype R]
namespace GlobalTheory.GaussUnits
theorem _root_.solution (I : Ideal R) [DecidablePred (· ∈ I)] (ψ : AddChar R ℂ)
    (hψ : ∀ d : R, (∀ x, ψ (d * x) = 1) → d = 0) (b : R) (hb : ∃ x ∈ I, b * x ≠ 0) :
    ∑ x, (if x ∈ I then ψ (b * x) else 0) = 0 := by
  obtain ⟨x₀, hx₀I, hx₀⟩ := hb
  have hne : ¬ ∀ r, ψ (b * x₀ * r) = 1 := fun h => hx₀ (hψ _ h)
  push_neg at hne
  obtain ⟨r, hr⟩ := hne
  have hyI : x₀ * r ∈ I := I.mul_mem_right r hx₀I
  have hby : ψ (b * (x₀ * r)) ≠ 1 := by rwa [← mul_assoc]
  have hshift := Fintype.sum_equiv (Equiv.addRight (x₀ * r))
    (fun x => if x + x₀ * r ∈ I then ψ (b * (x + x₀ * r)) else 0)
    (fun x => if x ∈ I then ψ (b * x) else 0) (fun _ => rfl)
  have hS : ∑ x, (if x ∈ I then ψ (b * x) else 0)
      = ψ (b * (x₀ * r)) * ∑ x, (if x ∈ I then ψ (b * x) else 0) := by
    conv_lhs => rw [← hshift]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    by_cases hx : x ∈ I
    · have h' : x + x₀ * r ∈ I := I.add_mem hx hyI
      rw [if_pos h', if_pos hx, mul_add, AddChar.map_add_eq_mul, mul_comm]
    · have h' : x + x₀ * r ∉ I := fun h => hx (by simpa using I.sub_mem h hyI)
      rw [if_neg h', if_neg hx, mul_zero]
  have h1 : (1 - ψ (b * (x₀ * r))) * ∑ x, (if x ∈ I then ψ (b * x) else 0) = 0 := by
    rw [sub_mul, one_mul, ← hS, sub_self]
  rcases mul_eq_zero.mp h1 with h | h
  · exact absurd (sub_eq_zero.mp h).symm hby
  · exact h
end GlobalTheory.GaussUnits
