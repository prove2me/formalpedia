-- Prove2me | solution 1 for HHRControl.PV.claim_4_30
-- status  : ACCEPTED   (disprove)
-- author  : @mrfancypants
-- created : 2026-10-26T23:39:27.421671+00:00
-- url     : https://prove2.me/submissions/f0b00bc9-bbb6-475c-b1cd-b5d5e153b5a7

import Mathlib
import Definitions.Def_CookPvsNP_defs
import Definitions.Def_ProjSchedTW_Complexity_Encoding
import Definitions.Def_HHRControl_PV_Elections
import Definitions.Def_HHRControl_PV_Languages
import Definitions.Def_HHRControl_PV_Construction428

open HHRControl.PV CookPvsNP Finset

namespace D430

/-- Build a permutation of `Fin m` from a function and its inverse. -/
def mkPerm {m : ℕ} (f g : Fin m → Fin m) (h1 : ∀ x, g (f x) = x) (h2 : ∀ x, f (g x) = x) :
    Ranking m := ⟨f, g, h1, h2⟩

-- candidates: b0..b4 = 0..4, c = 5, w = 6.  `f` gives the position of each candidate.
-- cw voter: c > w > b0 > b1 > b2 > b3 > b4
def rcw : Ranking 7 := mkPerm ![2,3,4,5,6,0,1] ![5,6,0,1,2,3,4] (by decide) (by decide)
-- wc voter: w > c > b0 > ...
def rwc : Ranking 7 := mkPerm ![2,3,4,5,6,1,0] ![6,5,0,1,2,3,4] (by decide) (by decide)
-- elem 0: b0 > w > b1 > b2 > b3 > b4 > c
def re0 : Ranking 7 := mkPerm ![0,2,3,4,5,6,1] ![0,6,1,2,3,4,5] (by decide) (by decide)
-- elem 1: b1 > w > b0 > b2 > b3 > b4 > c
def re1 : Ranking 7 := mkPerm ![2,0,3,4,5,6,1] ![1,6,0,2,3,4,5] (by decide) (by decide)
-- elem 2: b2 > w > b0 > b1 > b3 > b4 > c
def re2 : Ranking 7 := mkPerm ![2,3,0,4,5,6,1] ![2,6,0,1,3,4,5] (by decide) (by decide)
-- elem 3: b3 > w > b0 > b1 > b2 > b4 > c
def re3 : Ranking 7 := mkPerm ![2,3,4,0,5,6,1] ![3,6,0,1,2,4,5] (by decide) (by decide)
-- elem 4: b4 > w > b0 > b1 > b2 > b3 > c
def re4 : Ranking 7 := mkPerm ![2,3,4,5,0,6,1] ![4,6,0,1,2,3,5] (by decide) (by decide)

def Pce : Fin 19 → Ranking 7 :=
  ![rcw, rcw, rcw, rcw, rwc, rwc, rwc, rwc, rwc,
    re0, re0, re1, re1, re2, re2, re3, re3, re4, re4]

def τce : Fin 19 → VoterType 5 0 :=
  ![.cw, .cw, .cw, .cw, .wc, .wc, .wc, .wc, .wc,
    .elem 0, .elem 0, .elem 1, .elem 1, .elem 2, .elem 2, .elem 3, .elem 3, .elem 4, .elem 4]

def Sce : Fin 0 → Finset (Fin 5) := Fin.elim0

theorem hcons : IsConstruction428 5 0 5 Sce Pce := by
  refine ⟨by norm_num, by norm_num, τce, ?_, ?_, ?_, ?_, ?_⟩
  · decide
  · decide
  · intro i; exact i.elim0
  · decide
  · intro v
    fin_cases v <;> exact ⟨by decide, by decide⟩

theorem hwin : plurality.winners 7 19 Pce (insert (candC 5) {candB 0}) Finset.univ ≠ {candC 5} := by
  decide

end D430

set_option linter.unusedVariables false in
open D430 in
theorem solution : ¬ (∀ (m n k : ℕ) (S : Fin n → Finset (Fin m)) {N : ℕ} (P : Fin N → Ranking (m + 2))
    (hP : IsConstruction428 m n k S P) (D : Finset (Fin (m + 2)))
    (hD : D ⊆ Finset.univ.image candB ∪ {candW m})
    (hc : plurality.winners (m + 2) N P (insert (candC m) D) Finset.univ ≠ {candC m}),
    ∃ B' : Finset (Fin m), D = B'.image candB ∪ {candW m} ∧
      plurality.winners (m + 2) N P (B'.image candB ∪ {candC m, candW m}) Finset.univ =
        {candW m} ∧
      B'.card ≤ k ∧ IsHittingSet S B') := by
  intro h
  obtain ⟨B', hB', -⟩ := h 5 0 5 Sce Pce hcons {candB 0} (by decide) hwin
  have : candW 5 ∈ ({candB 0} : Finset (Fin 7)) := by rw [hB']; simp
  exact absurd this (by decide)
