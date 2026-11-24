-- Prove2me | solution 1 for GlobalTheory.PartRed.LowLaw.simpleSum_elem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:04:52.570748+00:00
-- url     : https://prove2.me/submissions/1c36e840-8a1b-4570-ad98-ea13bd7c5dc0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ChLApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_SchwartzBruhatCompAffineMatrixStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_IntegralCoordinateShearHaarLocalFieldStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_PartialReductionLowerEntryMultiplicationLaw
import Theorems.Thm_GlobalTheory_PartRed_LowLaw_embA_elem_val

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData
noncomputable section
open GlobalTheory GlobalTheory.PartRed GlobalTheory.PartRed.LowLaw
variable {k : Type} [Field k] {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ}
namespace GlobalTheory.PartRed.LowLaw
theorem _root_.solution (r l : Fin c) (h : r ≠ l) (a : k) :
    simpleSum (embA n (elem r l h a)) = if l.val = r.val + 1 then a else 0 := by
  rw [simpleSum, embA_elem_val]
  have key : ∀ i j : Fin c, (if j.val = i.val + 1 then
      (fromBlocks 1 0 0 (transvection r l a) : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) (Sum.inr i) (Sum.inr j) else 0) =
      if j = l then (if i = r then (if l.val = r.val + 1 then a else 0) else 0) else 0 := by
    intro i j
    simp only [fromBlocks_apply₂₂, transvection, Matrix.add_apply, single_apply]
    by_cases hij : j.val = i.val + 1
    · have hne : i ≠ j := fun h => by rw [h] at hij; omega
      rw [if_pos hij, one_apply_ne hne, zero_add]
      by_cases hi : i = r
      · subst hi
        by_cases hj : j = l
        · subst hj; simp [hij]
        · simp [hj, Ne.symm hj]
      · simp [hi, Ne.symm hi]
    · rw [if_neg hij]
      by_cases hi : i = r
      · subst hi
        by_cases hj : j = l
        · subst hj; simp [hij]
        · simp [hj]
      · simp [hi]
  simp only [key]
  simp
end GlobalTheory.PartRed.LowLaw
