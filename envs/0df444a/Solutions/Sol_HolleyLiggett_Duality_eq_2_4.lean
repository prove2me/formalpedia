-- Prove2me | solution 1 for HolleyLiggett.Duality.eq_2_4
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T13:14:27.749821+00:00
-- url     : https://prove2.me/submissions/a5ce8678-1066-4207-b719-4b3418684b4e

import Mathlib
import Definitions.Def_HolleyLiggett_Duality_Setting
set_option autoImplicit false
open HolleyLiggett.Duality
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

open Classical in
theorem solution {I : Type*} [Countable I] [DecidableEq I] (N : I → ℕ → Finset I)
    (hN0 : ∀ i, N i 0 = ∅) (f : I → PMF ℕ)
    (η : Config I) (F : Finset I) :
    dualProb N f 1 F η =
      ∑' k : (↥F → ℕ),
        (if ∀ i : ↥F, Disjoint (N i (k i) : Set I) (occupied η) then ∏ i : ↥F, f i (k i) else 0) := by
  have h1 : ∀ B, bpiProb N f 1 F B = bpiStep N f F B := by
    intro B
    simp only [bpiProb]
    rw [tsum_eq_single F]
    · simp
    · intro G hG
      simp [Ne.symm hG]
  unfold dualProb
  simp_rw [h1, bpiStep]
  simp_rw [← ENNReal.tsum_mul_right]
  rw [ENNReal.tsum_comm]
  refine tsum_congr fun k => ?_
  rw [tsum_eq_single (Finset.univ.biUnion (fun i : ↥F => N i (k i)))]
  · simp only [if_true]
    by_cases hd : ∀ i : ↥F, Disjoint (N i (k i) : Set I) (occupied η)
    · have : Disjoint ((Finset.univ.biUnion (fun i : ↥F => N i (k i)) : Finset I) : Set I) (occupied η) := by
        rw [Finset.coe_biUnion]
        simp only [Finset.coe_univ, Set.mem_univ, Set.iUnion_true]
        exact Set.disjoint_iUnion_left.mpr hd
      simp [hd, this]
    · have : ¬ Disjoint ((Finset.univ.biUnion (fun i : ↥F => N i (k i)) : Finset I) : Set I) (occupied η) := by
        intro h
        apply hd
        intro i
        refine Set.disjoint_of_subset_left ?_ h
        intro x hx
        simp only [Finset.coe_biUnion, Finset.coe_univ, Set.mem_univ, Set.iUnion_true, Set.mem_iUnion]
        exact ⟨i, hx⟩
      simp [hd, this]
  · intro B hB
    rw [if_neg (Ne.symm hB), zero_mul]
