-- Prove2me | solution 1 for GridHam.mem_primeShapes_of
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T22:31:40.430806+00:00
-- url     : https://prove2.me/submissions/e22ccca2-22a0-4d02-bdcd-62818ce36ff1

module
public import Definitions.Def_GridHam_Arith
public import Definitions.Def_GridHam_PrimeTable
public import Definitions.Def_GridHam_Reduction

set_option autoImplicit true
@[expose] public section
public section
open GridHam
namespace GridHam
theorem _root_.solution (w h : ℕ) (hw : 1 ≤ w) (hh : 1 ≤ h) (hp : ¬ NotPrime w h) :
    (w, h) ∈ primeShapes := by
  unfold NotPrime at hp
  have hp' : (w ≤ 3 ∧ h ≤ 3) ∨ (w = 4 ∧ h = 4) ∨ (w = 4 ∧ h = 5) ∨ (w = 5 ∧ h = 4) := by
    by_contra hn
    exact hp hn
  rcases hp' with ⟨hw3, hh3⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rcases (by omega : w = 1 ∨ w = 2 ∨ w = 3) with rfl | rfl | rfl <;>
      rcases (by omega : h = 1 ∨ h = 2 ∨ h = 3) with rfl | rfl | rfl <;> decide
  · decide
  · decide
  · decide
end GridHam
