-- Prove2me | solution 1 for GlobalTheory.RootEx.Model.simpleSum_row_col
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T18:08:07.846391+00:00
-- url     : https://prove2.me/submissions/42150322-520f-41b4-af4a-4bcc9dc9ed5a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSumRowCol

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix
open scoped NNReal ENNReal
noncomputable section
open GlobalTheory GlobalTheory.RootEx GlobalTheory.RootEx.Model
open GlobalTheory.SplitWeil GlobalTheory.RootEx
variable {k : Type*} [Field k] {n : Type*} [Fintype n] [DecidableEq n] {c : ℕ}
namespace GlobalTheory.RootEx.Model
theorem _root_.solution (l : Fin c) (hl : l.val + 1 < c) (u β : n → k) :
    simpleSum (rowE c (l.val + 1) u * colE c (l.val + 1 + 1) β * (rowE c (l.val + 1) u)⁻¹) = u ⬝ᵥ β := by
  have hv : ∀ i j : Fin c, (rowE c (l.val + 1) u * colE c (l.val + 1 + 1) β * (rowE c (l.val + 1) u)⁻¹).val
      (Sum.inr i) (Sum.inr j) = (if i = l ∧ j.val = l.val + 1 then u ⬝ᵥ β else 0) + (1 : Matrix _ _ k) i j := by
    intro i j
    show ((fromBlocks 1 0 _ 1 * fromBlocks 1 _ 0 1 * fromBlocks 1 0 _ 1 : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k)) _ _ = _
    simp only [fromBlocks_multiply, fromBlocks_apply₂₂]
    by_cases hi : i = l <;> by_cases hj : j.val = l.val + 1 <;>
      simp [Matrix.mul_apply, Matrix.one_apply, dotProduct, hi, hj, Fin.val_inj]
  simp only [simpleSum, hv]
  rw [Finset.sum_eq_single l, Finset.sum_eq_single ⟨l.val + 1, hl⟩]
  · simp [Matrix.one_apply, Fin.ext_iff]
  · intro j _ hj
    rw [if_neg]; intro h; exact hj (Fin.ext h)
  · simp
  · intro i _ hi
    refine Finset.sum_eq_zero fun j _ => ?_
    split_ifs with h1 h2
    · exact absurd h2.1 hi
    · have : i ≠ j := by rintro rfl; omega
      simp [this]
    · rfl
  · simp
end GlobalTheory.RootEx.Model
