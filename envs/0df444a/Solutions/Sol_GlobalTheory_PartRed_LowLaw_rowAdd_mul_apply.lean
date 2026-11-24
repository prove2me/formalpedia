-- Prove2me | solution 1 for GlobalTheory.PartRed.LowLaw.rowAdd_mul_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:55:18.619603+00:00
-- url     : https://prove2.me/submissions/8bea7bcb-c018-4a1f-9f22-e676078919fe

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ChLApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_SchwartzBruhatCompAffineMatrixStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_IntegralCoordinateShearHaarLocalFieldStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_PartialReductionLowerEntryMultiplicationLaw

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
omit [Fintype n'] [DecidableEq n']
namespace GlobalTheory.PartRed.LowLaw
theorem _root_.solution (r l : Fin c) (a : k) (t : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k)
    (p : n ⊕ Fin c) (q : n' ⊕ Fin (c + 1)) :
    ((fromBlocks 1 0 0 (transvection r l a) : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) * t) p q =
      t p q + if p = Sum.inr r then a * t (Sum.inr l) q else 0 := by
  rw [mul_apply]
  rcases p with p | p
  · simp [Fintype.sum_sum_type, one_apply]
  · simp [Fintype.sum_sum_type, transvection, add_mul, Finset.sum_add_distrib, one_apply, single_apply,
      ite_and, eq_comm]
end GlobalTheory.PartRed.LowLaw
