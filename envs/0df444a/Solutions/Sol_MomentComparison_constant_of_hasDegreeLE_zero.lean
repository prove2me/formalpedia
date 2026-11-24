-- Prove2me | solution 1 for MomentComparison.constant_of_hasDegreeLE_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T11:22:09.191798+00:00
-- url     : https://prove2.me/submissions/2a19c1ac-0636-443c-9ad5-01b71395e6c2

module
public import Definitions.Def_MomentComparison_Basic
public import Mathlib.Data.Finset.SymmDiff
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Tactic.Ring
public import Definitions.Def_MomentComparison_Basic
import all Definitions.Def_MomentComparison_Basic
public import Definitions.Def_MomentComparison_Walsh
public import Theorems.Thm_MomentComparison_walsh_empty
public import Theorems.Thm_MomentComparison_cubeSign_mul_self
public import Theorems.Thm_MomentComparison_cubeAverage_const
public import Theorems.Thm_MomentComparison_walshExpansion
attribute [local simp] MomentComparison.walsh_empty
attribute [local simp] MomentComparison.cubeSign_mul_self
attribute [local simp] MomentComparison.cubeAverage_const

set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators symmDiff
open MomentComparison
open Finset
namespace MomentComparison
theorem _root_.solution {n : ℕ} {f : Cube n → ℝ}
    (h : HasDegreeLE f 0) : ∃ c, ∀ x, f x = c := by
  refine ⟨cubeAverage f, fun x => ?_⟩
  rw [← walshExpansion f x]
  have hz : ∀ s : Finset (Fin n), s ≠ ∅ →
      (cubeAverage fun y => f y * walsh s y) * walsh s x = 0 := by
    intro s hs
    have he := h s (card_pos.mpr (nonempty_iff_ne_empty.mpr hs))
    change cubeAverage (fun y => f y * walsh s y) = 0 at he
    simp [he]
  rw [sum_eq_single ∅ (fun s _ hs => hz s hs) (by simp)]
  simp [walsh_empty]
end MomentComparison
