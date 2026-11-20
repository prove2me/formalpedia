-- Prove2me | solution 1 for MatchIndiff.PublicSM.lemma_D_17
-- status  : ACCEPTED   (disprove)
-- author  : @ethanlee515
-- created : 2026-11-20T02:03:41.393538+00:00
-- url     : https://prove2.me/submissions/64991a22-68b3-4ed5-866c-5ad07b3e9659

import Definitions.Def_MatchIndiff_PublicSM_Model
import Definitions.Def_MatchIndiff_PublicSM_Tape

-- Joint discovery of the empty-market counterexample: Yu-Fang Chen (Academia
-- Sinica); Kai-Min Chung (Academia Sinica); Shih-Han Hung (National Taiwan
-- University); and Yi Lee (University of Maryland).

set_option autoImplicit false

open MatchIndiff.PublicSM

theorem solution :
  ¬ (∀ {n m : ℕ} (Q : Fin m → Fin n → ℕ) (P : Fin n → Fin m → ℕ)
    (_hQ : ∀ h, IsRow (Q h)) (_hP : ∀ i, IsRow (P i)) (proc : Procedure n m),
    (∀ board : List Bool, (∀ d, tapeCheck Q proc d (P d) board = true) →
      maskE Q (board.take (pubPairs Q).length) = trueE Q P ∧
        ∃ ans, replay (proc (trueE Q P)) [] (board.drop (pubPairs Q).length) = some ans ∧
          IsTrueRun proc (trueE Q P) P ans) ∧
    (∀ ans : List Ans, IsTrueRun proc (trueE Q P) P ans →
      ans.length ≤ (Finset.univ.filter (fun x : Fin n × Fin m => trueE Q P x.1 x.2 = true)).card →
      ∃ board : List Bool, (∀ d, tapeCheck Q proc d (P d) board = true) ∧
        board.length ≤ mQ Q + 2 * (Finset.univ.filter
          (fun x : Fin n × Fin m => trueE Q P x.1 x.2 = true)).card)) := by
  intro claim
  let Q : Fin 0 → Fin 0 → ℕ := fun _ _ => 0
  let P : Fin 0 → Fin 0 → ℕ := fun _ _ => 0
  let stop : Procedure 0 0 := fun _ _ => none
  have validQ : ∀ h, IsRow (Q h) := fun h => Fin.elim0 h
  have validP : ∀ d, IsRow (P d) := fun d => Fin.elim0 d
  have accept : ∀ d, tapeCheck Q stop d (P d) [true] = true :=
    fun d => Fin.elim0 d
  obtain ⟨ans, replayed, _⟩ := ((claim Q P validQ validP stop).1 [true] accept).2
  have rejected : replay (stop (trueE Q P)) []
      ([true].drop (pubPairs Q).length) = none := by
    simp [stop, pubPairs, replay]
  have impossible : (none : Option (List Ans)) = some ans :=
    rejected.symm.trans replayed
  cases impossible
