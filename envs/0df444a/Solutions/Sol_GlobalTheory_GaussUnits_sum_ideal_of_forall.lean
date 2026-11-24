-- Prove2me | solution 1 for GlobalTheory.GaussUnits.sum_ideal_of_forall
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T16:33:01.890079+00:00
-- url     : https://prove2.me/submissions/afd20e2e-77cc-421e-9f62-a5df024dc56b

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
theorem _root_.solution (I : Ideal R) [DecidablePred (· ∈ I)] (ψ : AddChar R ℂ) (b : R)
    (hb : ∀ x ∈ I, b * x = 0) :
    ∑ x, (if x ∈ I then ψ (b * x) else 0) = ((univ.filter (· ∈ I)).card : ℂ) := by
  rw [← Finset.sum_filter, Finset.card_eq_sum_ones, Nat.cast_sum]
  refine Finset.sum_congr rfl (fun x hx => ?_)
  rw [Finset.mem_filter] at hx
  rw [hb x hx.2, AddChar.map_zero_eq_one, Nat.cast_one]
end GlobalTheory.GaussUnits
