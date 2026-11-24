-- Prove2me | solution 1 for GlobalTheory.DworkGhost.coeff_spec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T14:25:08.908068+00:00
-- url     : https://prove2.me/submissions/b2763b25-8fc3-4fad-a36f-deca55f666d7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsWittVectorGhostEqFrobeniusIterate

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped NNReal
open Finset
open GlobalTheory GlobalTheory.DworkGhost
namespace GlobalTheory.DworkGhost
theorem _root_.solution {A : Type} [CommRing A] (l : ℕ) (φ : A →+* A) (a : A) (n : ℕ)
    (h : (l : A) ^ n ∣ φ^[n] a - ∑ i ∈ range n, (l : A) ^ i * coeff l φ a i ^ l ^ (n - i)) :
    φ^[n] a = ∑ i ∈ range (n + 1), (l : A) ^ i * coeff l φ a i ^ l ^ (n - i) := by
  have h' : (l : A) ^ n ∣ φ^[n] a - ∑ i : Fin n, (l : A) ^ (i : ℕ) * coeff l φ a i ^ l ^ (n - i) := by
    rwa [Fin.sum_univ_eq_sum_range (fun i => (l : A) ^ i * coeff l φ a i ^ l ^ (n - i)) n]
  have e : coeff l φ a n = h'.choose := by
    rw [coeff, dif_pos h']
  have hc := h'.choose_spec
  rw [← e, Fin.sum_univ_eq_sum_range (fun i => (l : A) ^ i * coeff l φ a i ^ l ^ (n - i)) n] at hc
  rw [sum_range_succ, Nat.sub_self, pow_zero, pow_one, ← hc]
  ring
end GlobalTheory.DworkGhost
