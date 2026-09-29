-- Prove2me | solution 1 for MagicSquares.magic_three_normal_classify
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-09-17T07:14:08.829347+00:00
-- url     : https://prove2.me/submissions/9c158b95-9c87-4846-9329-8a7933344587

import Mathlib
import Definitions.Def_MagicSquares
import Definitions.Def_MagicSquaresParam3

set_option autoImplicit false
set_option maxHeartbeats 0

open MagicSquares

namespace MagicSquares

/-- `IsNormal` spread out over the two index variables separately, so that
`simp` can unfold the (finite) quantifiers. -/
private lemma isNormal_iff (M : Square 3 ℕ) :
    IsNormal M ↔
      (∀ i : Fin 3, ∀ j : Fin 3, 1 ≤ M i j ∧ M i j ≤ 9) ∧
        (∀ i i' : Fin 3, ∀ j j' : Fin 3, M i j = M i' j' → i = i' ∧ j = j') := by
  constructor
  · intro hN
    constructor
    · intro i j
      have h := hN.1 (i, j)
      norm_num at h ⊢
      exact h
    · intro i i' j j' hij
      have hp : (i, j) = (i', j') := hN.2 hij
      exact ⟨congrArg Prod.fst hp, congrArg Prod.snd hp⟩
  · intro h
    constructor
    · intro p
      have hb := h.1 p.1 p.2
      norm_num at hb ⊢
      exact hb
    · intro p q hpq
      have hh := h.2 p.1 q.1 p.2 q.2 hpq
      exact Prod.ext hh.1 hh.2

/-- A normal square of order three has all entries in `[1, 9]`. -/
private lemma normal_bounds {M : Square 3 ℕ} (hN : IsNormal M) (i j : Fin 3) :
    1 ≤ M i j ∧ M i j ≤ 9 :=
  (isNormal_iff M).mp hN |>.1 i j

/-- Both parameters of a normal `mkMagic3 5 a c` lie in `[1, 9]`. -/
private lemma normal_params_bounds {a c : ℕ} (hN : IsNormal (mkMagic3 5 a c)) :
    1 ≤ a ∧ a ≤ 9 ∧ 1 ≤ c ∧ c ≤ 9 := by
  have h00 := normal_bounds hN 0 0
  have h02 := normal_bounds hN 0 2
  simp [mkMagic3] at h00 h02
  omega

/-- The eight parameter pairs of the Lo Shu orbit. -/
private def loShuParams (a c : ℕ) : Prop :=
  (a = 2 ∧ c = 4) ∨ (a = 2 ∧ c = 6) ∨ (a = 4 ∧ c = 2) ∨ (a = 4 ∧ c = 8) ∨
    (a = 6 ∧ c = 2) ∨ (a = 6 ∧ c = 8) ∨ (a = 8 ∧ c = 4) ∨ (a = 8 ∧ c = 6)

/-- Classification: within the range forced by normality, `mkMagic3 5 a c` is
normal exactly for the eight Lo Shu parameters. -/
private lemma normal_iff_loShu (a c : ℕ) (ha1 : 1 ≤ a) (ha9 : a ≤ 9)
    (hc1 : 1 ≤ c) (hc9 : c ≤ 9) :
    IsNormal (mkMagic3 5 a c) ↔ loShuParams a c := by
  interval_cases a <;> interval_cases c <;>
    rw [isNormal_iff] <;>
    simp [mkMagic3, loShuParams, Fin.forall_fin_succ] <;> norm_num

end MagicSquares

open MagicSquares

/-- Classification: for an admissible pair, `mkMagic3 5 a c` is normal exactly
for the eight Lo Shu parameters. -/
theorem solution (a c : ℕ) (_hac : (a, c) ∈ paramSet 5) :
    IsNormal (mkMagic3 5 a c) ↔
      (a = 2 ∧ c = 4) ∨ (a = 2 ∧ c = 6) ∨ (a = 4 ∧ c = 2) ∨ (a = 4 ∧ c = 8) ∨
        (a = 6 ∧ c = 2) ∨ (a = 6 ∧ c = 8) ∨ (a = 8 ∧ c = 4) ∨ (a = 8 ∧ c = 6) := by
  constructor
  · intro hN
    have hb := normal_params_bounds hN
    exact (normal_iff_loShu a c hb.1 hb.2.1 hb.2.2.1 hb.2.2.2).mp hN
  · intro h
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      exact (normal_iff_loShu _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num)).mpr
        (by simp [loShuParams])
