-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLog.ReconstructionProgram.reconstructionBudget_le
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T03:46:22.793675+00:00
-- url     : https://prove2.me/submissions/e185b6ca-dc9e-46c7-b6e2-403723fd43bc

import Mathlib
import Definitions.Def_OAIQ081S042

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_ReconstructionProgramCost
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Polynomial bounds for the actual outer tape operations. Arithmetic is
accounted for by its proved per-node primitive runtime K. -/
namespace SubexponentialSAT.SqrtLog.ReconstructionProgram

open SubexponentialSAT SubexpCRTOuterProgram

theorem controllerBudget_mono {W J Q K W' J' Q' K' : ℕ}
    (hW : W ≤ W') (hJ : J ≤ J') (hQ : Q ≤ Q') (hK : K ≤ K') :
    controllerBudget W J Q K ≤ controllerBudget W' J' Q' K' := by
  unfold controllerBudget initializationBudget SubexpFactorCountSetup.countBudget
    transportCost cleanupBudget
  gcongr

theorem controllerBudget_le (W J Q K S : ℕ)
    (hW : W ≤ S) (hJ : J ≤ S) (hQ : Q ≤ S) :
    controllerBudget W J Q K ≤ S * K + 300 * (S + 1)^3 := by
  calc
    _ ≤ controllerBudget S S S K := controllerBudget_mono hW hJ hQ le_rfl
    _ ≤ _ := by
      unfold controllerBudget initializationBudget SubexpFactorCountSetup.countBudget
        transportCost cleanupBudget
      ring_nf
      omega

end SubexponentialSAT.SqrtLog.ReconstructionProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_ReconstructionProgramBounds
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Polynomial majorants for the physical middle and outer traversal. The
native service costs can be substituted directly in these inequalities. -/
namespace SubexponentialSAT.SqrtLog.ReconstructionProgram

open SubexponentialSAT SubexpCRTOuterProgram

theorem middleBudget_mono {Q J W Km Ka Kl Q' J' W' Km' Ka' Kl' : ℕ}
    (hQ : Q ≤ Q') (hJ : J ≤ J') (hW : W ≤ W')
    (hm : Km ≤ Km') (ha : Ka ≤ Ka') (hl : Kl ≤ Kl') :
    Middle.budget Q J W Km Ka Kl ≤ Middle.budget Q' J' W' Km' Ka' Kl' := by
  unfold Middle.budget CofactorOuter.budget Cofactor.includeBudget Local.budget
    Horner.budget HornerProgram.budget
  gcongr

theorem middleBudget_le (Q J W Km Ka Kl S : ℕ)
    (hQ : Q ≤ S) (hJ : J ≤ S) (hW : W ≤ S)
    (hm : Km ≤ S) (ha : Ka ≤ S) (hl : Kl ≤ S) :
    Middle.budget Q J W Km Ka Kl ≤ 2000 * (S + 1)^3 := by
  calc
    _ ≤ Middle.budget S S S S S S := middleBudget_mono hQ hJ hW hm ha hl
    _ ≤ _ := by
      unfold Middle.budget CofactorOuter.budget Cofactor.includeBudget Local.budget
        Horner.budget HornerProgram.budget
      ring_nf
      omega

theorem reconstructionBudget_le_oai (Q J W Km Ka Kl S : ℕ)
    (hQ : Q ≤ S) (hJ : J ≤ S) (hW : W ≤ S)
    (hm : Km ≤ S) (ha : Ka ≤ S) (hl : Kl ≤ S) :
    controllerBudget W J Q (Middle.budget Q J W Km Ka Kl) + 1 ≤
      2300 * (S + 1)^4 + 1 := by
  have hmid := middleBudget_le Q J W Km Ka Kl S hQ hJ hW hm ha hl
  have houter := controllerBudget_le W J Q (Middle.budget Q J W Km Ka Kl) S hW hJ hQ
  have hmult := Nat.mul_le_mul_left S hmid
  nlinarith

end SubexponentialSAT.SqrtLog.ReconstructionProgram

end OAI.Algorithms
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLog.ReconstructionProgram.reconstructionBudget_le_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLog.ReconstructionProgram.reconstructionBudget_le_oai
