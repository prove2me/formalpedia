-- Prove2me | solution 1 for GlobalTheory.PartRed.UpperLaw.elem_mem_N
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:06:08.518105+00:00
-- url     : https://prove2.me/submissions/6b2565b1-e5e3-4b9c-aef0-4bd18c67008b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ChLApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_SchwartzBruhatCompAffineMatrixStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_IntegralCoordinateShearHaarLocalFieldStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_PartialReductionUpperFreeEntryTranslationLaw
import Theorems.Thm_GlobalTheory_PartRed_UpperLaw_embA_elem_apply

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
open GlobalTheory GlobalTheory.PartRed GlobalTheory.PartRed.UpperLaw
open GlobalTheory.PartRed
variable {k : Type} [Field k] {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ}
namespace GlobalTheory.PartRed.UpperLaw
theorem _root_.solution (ρ : ℕ) (l m : Fin c) (h : l ≠ m) (hlm : l.val < m.val) (hm : m.val ≤ ρ) (a : k) :
    embA n (elem l m h a) ∈ N k n c (ρ + 1) := by
  apply Subgroup.subset_closure
  intro r s hrs
  rw [embA_elem_apply, if_neg, add_zero]
  rintro ⟨rfl, rfl⟩
  simp only [lev, Sum.elim_inr] at hrs
  omega
end GlobalTheory.PartRed.UpperLaw
