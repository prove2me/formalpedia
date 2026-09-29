-- Prove2me | solution 1 for MonotonicSolutions.CoreRules.core_youngV
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-28T20:57:50.630733+00:00
-- url     : https://prove2.me/submissions/ce8df9f7-adbe-4e85-8cee-978486fe385a

import Mathlib
import Definitions.Def_Supermodularity_Cooperative_Core
import Definitions.Def_MonotonicSolutions_CoreRules_Game
import Definitions.Def_MonotonicSolutions_CoreRules_YoungGames

open MonotonicSolutions.CoreRules Supermodularity.Cooperative

/-- The value of the game on a coalition, as a natural number: `12` on the grand coalition,
otherwise the largest listed value among the coalitions `S_k ⊆ S`. -/
def vNat (S : Finset (Fin 5)) : ℕ :=
  if S = Finset.univ then 12 else (Finset.univ.filter (fun k => youngCoalition k ⊆ S)).sup ![3, 3, 9, 9, 12]

lemma game_eq (S : Finset (Fin 5)) : youngV.1 S = (vNat S : ℝ) := by
  show youngMaxFun ![3, 3, 9, 9, 12] 12 S = _
  unfold youngMaxFun vNat
  split_ifs <;> simp

lemma vec_cast : (![3, 0, 0, 6, 3] : Fin 5 → ℝ) = fun i => (((![3, 0, 0, 6, 3] : Fin 5 → ℕ) i : ℕ) : ℝ) := by
  funext i; fin_cases i <;> simp

/-- Acceptability of the candidate vector: a finite check over all 32 coalitions. -/
lemma acc_nat : ∀ S : Finset (Fin 5), vNat S ≤ ∑ i ∈ S, (![3, 0, 0, 6, 3] : Fin 5 → ℕ) i := by
  unfold vNat
  decide +kernel

lemma acc (S : Finset (Fin 5)) : youngV.1 S ≤ ∑ i ∈ S, (![3, 0, 0, 6, 3] : Fin 5 → ℝ) i := by
  rw [game_eq, vec_cast, ← Nat.cast_sum]
  exact_mod_cast acc_nat S

theorem solution :
    Supermodularity.Cooperative.Core Finset.univ youngV.1 = {![3, 0, 0, 6, 3]} := by
  ext y
  simp only [Core, Set.mem_ofPred_eq, Set.mem_singleton_iff]
  constructor
  · rintro ⟨hsum, hacc⟩
    have e : ∀ S : Finset (Fin 5), (vNat S : ℝ) ≤ ∑ i ∈ S, y i := fun S => by
      rw [← game_eq]; exact hacc S (Finset.subset_univ S)
    have c1 := e {2, 4}
    have c2 := e {0, 1, 2}
    have c3 := e {0, 2, 3}
    have c4 := e {1, 3, 4}
    have c5 := e {0, 1, 3, 4}
    have s0 := e {0}
    have s1 := e {1}
    have s2 := e {2}
    have s3 := e {3}
    have s4 := e {4}
    rw [game_eq] at hsum
    rw [show vNat {2, 4} = 3 by unfold vNat; decide +kernel] at c1
    rw [show vNat {0, 1, 2} = 3 by unfold vNat; decide +kernel] at c2
    rw [show vNat {0, 2, 3} = 9 by unfold vNat; decide +kernel] at c3
    rw [show vNat {1, 3, 4} = 9 by unfold vNat; decide +kernel] at c4
    rw [show vNat {0, 1, 3, 4} = 12 by unfold vNat; decide +kernel] at c5
    rw [show vNat {0} = 0 by unfold vNat; decide +kernel] at s0
    rw [show vNat {1} = 0 by unfold vNat; decide +kernel] at s1
    rw [show vNat {2} = 0 by unfold vNat; decide +kernel] at s2
    rw [show vNat {3} = 0 by unfold vNat; decide +kernel] at s3
    rw [show vNat {4} = 0 by unfold vNat; decide +kernel] at s4
    rw [show vNat Finset.univ = 12 by unfold vNat; decide +kernel] at hsum
    simp (config := { decide := true }) [Finset.sum_insert, Finset.sum_singleton, Fin.sum_univ_five]
      at c1 c2 c3 c4 c5 s0 s1 s2 s3 s4 hsum
    funext i
    fin_cases i <;> simp <;> linarith
  · rintro rfl
    refine ⟨?_, fun S _ => acc S⟩
    rw [game_eq, show vNat Finset.univ = 12 by unfold vNat; decide +kernel]
    simp [Fin.sum_univ_five]
    norm_num
