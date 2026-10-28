-- Prove2me | solution 1 for MarkovMixing.innerPi_self_eq_sum_sq
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-27T01:08:26.757009+00:00
-- url     : https://prove2.me/submissions/7cc658b4-7734-4577-b746-f60fa2e91425

import Mathlib
import Definitions.Def_mm_spectral
import Theorems.Thm_MarkovMixing_eigenbasis_expand

-- carved verbatim out of submission b36a2a77-0ed1-410e-b982-dafb4dc643a6, lines 617-633

section
open scoped BigOperators
open scoped Matrix
open MarkovMixing
set_option maxHeartbeats 1000000
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {P : Matrix V V ℝ} {π : V → ℝ} {n : ℕ} {lam : Fin n → ℝ} {ff : Fin n → V → ℝ}

theorem solution (hpos : ∀ x, 0 < π x)
    (hcomp : ∀ x y : V, ∑ j, ff j x * ff j y = (if x = y then 1 else 0) / π y)
    (g : V → ℝ) : innerPi π g g = ∑ j, (innerPi π g (ff j)) ^ 2 := by
  have e1 : ∀ x : V, g x * g x * π x
      = ∑ j, innerPi π g (ff j) * (g x * ff j x * π x) := by
    intro x
    have : ∀ j, innerPi π g (ff j) * (g x * ff j x * π x)
        = (innerPi π g (ff j) * ff j x) * (g x * π x) := fun j => by ring
    rw [Finset.sum_congr rfl (fun j _ => this j), ← Finset.sum_mul, MarkovMixing.eigenbasis_expand hpos hcomp g x]
    ring
  show ∑ x : V, g x * g x * π x = _
  rw [Finset.sum_congr rfl (fun x _ => e1 x), Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← Finset.mul_sum]
  show innerPi π g (ff j) * innerPi π g (ff j) = _
  ring

end
