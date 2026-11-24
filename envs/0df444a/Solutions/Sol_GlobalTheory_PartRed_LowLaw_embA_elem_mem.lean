-- Prove2me | solution 1 for GlobalTheory.PartRed.LowLaw.embA_elem_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:16:09.785036+00:00
-- url     : https://prove2.me/submissions/2d74a27f-a90b-4ca1-82c0-3e0fa4148f5e

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
theorem _root_.solution (r l : Fin c) (h : r ≠ l) (hrl : r.val < l.val) (a : k) (p : ℕ) :
    embA n (elem r l h a) ∈ N k n c p := by
  apply Subgroup.subset_closure
  show InN p _
  intro r' s hrs
  rw [embA_elem_val]
  rcases r' with r' | r' <;> rcases s with s | s
  · simp [one_apply]
  · simp [one_apply]
  · simp [one_apply]
  · simp only [lev, Sum.elim_inr] at hrs
    simp only [fromBlocks_apply₂₂, transvection, Matrix.add_apply, single_apply, one_apply, Sum.inr.injEq]
    have : ¬ (r = r' ∧ l = s) := by
      rintro ⟨rfl, rfl⟩
      omega
    rw [if_neg this, add_zero]
end GlobalTheory.PartRed.LowLaw
