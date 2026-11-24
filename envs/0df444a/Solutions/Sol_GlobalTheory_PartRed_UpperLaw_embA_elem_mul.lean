-- Prove2me | solution 1 for GlobalTheory.PartRed.UpperLaw.embA_elem_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:06:09.395807+00:00
-- url     : https://prove2.me/submissions/2ecccac7-9b99-47e4-845e-476c111cd37b

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
theorem _root_.solution {Q : Type} (l m : Fin c) (h : l ≠ m) (a : k) (t : Matrix (n ⊕ Fin c) Q k) (r : n ⊕ Fin c) (q : Q) :
    ((embA n (elem l m h a)).val * t) r q = t r q + if r = Sum.inr l then a * t (Sum.inr m) q else 0 := by
  simp only [Matrix.mul_apply, embA_elem_apply, add_mul, Finset.sum_add_distrib]
  congr 1
  · simp [Matrix.one_apply]
  · by_cases hr : r = Sum.inr l
    · simp [hr]
    · simp [hr]
end GlobalTheory.PartRed.UpperLaw
