-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram.nativeRowsBudget_le_polynomial
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T08:49:17.39993+00:00
-- url     : https://prove2.me/submissions/f4a232a3-5361-4177-9a8b-64c6e6cd8173

import Mathlib
import Definitions.Def_OAIQ081S168

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutSourcePlanLookup
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Full pair-plan lookup at the source-row ABI. All query construction, record
comparison, index increments and cleanup are native paid instructions. -/
namespace SubexponentialSAT.SqrtLog.LayoutSourcePlanLookup
open SubexponentialSAT BitProgram StructuredCalls

/-- Coarse quadratic bound in the actual serialized input and unary query. -/
theorem pairBudget_polynomial (v n f : ℕ) (ps : List (ℕ × ℕ)) :
    pairBudget v n f ps ≤
      1000*((LayoutOwnerFiberProgram.stream ps).length+v+n+f+1)^2 := by
  unfold pairBudget
  nlinarith [sq_nonneg ((LayoutOwnerFiberProgram.stream ps).length : ℤ),
    sq_nonneg ((v+n+f : ℕ) : ℤ)]

end SubexponentialSAT.SqrtLog.LayoutSourcePlanLookup

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutSourceRowsProgramCostBase
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram
open SubexponentialSAT

theorem uniformRowBudget_le_polynomial (N : ℕ) (ps : List (ℕ × ℕ))
    (I K L D d B a b S : ℕ)
    (hN : N ≤ S) (hps : ps.length ≤ S) (hs : (LayoutOwnerFiberProgram.stream ps).length ≤ S)
    (hI : I ≤ S) (ha : a ≤ S) (hb : b ≤ S) :
    uniformRowBudget N ps I K L D d B a b ≤ rowBudgetPolynomial K L D d B S := by
  dsimp only [uniformRowBudget,rowBudgetPolynomial]
  have hT : 2+ps.length*(L+2) ≤ 2+S*(L+2) := by gcongr
  have howner : 1000*((LayoutOwnerFiberProgram.stream ps).length+N+1)^2 ≤
      1000*(2*S+1)^2 := by gcongr ; omega
  have hscan : ps.length*(K+5*I+3*L+15) ≤ S*(K+5*S+3*L+15) := by gcongr
  have hexec : 300000*(2+ps.length*(L+2)+1)*(D+1)^3*(d+1)^3*(B+1)^2 ≤
      300000*(2+S*(L+2)+1)*(D+1)^3*(d+1)^3*(B+1)^2 := by gcongr
  omega

end SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutSourceRowsProgramNativeCost
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A state-independent polynomial allowance for the complete source phase. -/
namespace SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram
open SubexponentialSAT LayoutProgram
open SubexponentialSAT.SubexpLiftRing
attribute [local simp] Fin.coe_ofNat_eq_mod

theorem nativeRowsBudget_le_polynomial_oai {r Q d : ℕ} (p : SourceBank.Parameters r Q d)
    (s : Store) (v N f S : ℕ) (ps : List (ℕ × ℕ))
    (hv : v ≤ S) (hN : N ≤ S) (hf : f ≤ S) (hps : ps.length ≤ S)
    (hs : (LayoutOwnerFiberProgram.stream ps).length ≤ S)
    (h21 : (s 21).length ≤ S) (h26 : (s 26).length ≤ S) :
    nativeRowsBudget p s v N f S ps ≤ nativeRowsPolynomial p S := by
  have hlookup : LayoutSourcePlanLookup.pairBudget v N f ps ≤ 1000*(4*S+1)^2 :=
    (LayoutSourcePlanLookup.pairBudget_polynomial v N f ps).trans (by gcongr ; omega)
  have hidx : ps.idxOf (v,N+f) ≤ S := by
    simpa only [List.idxOf, beq_eq_decide] using
      (List.idxOf_le_length (a := (v,N+f)) (l := ps)).trans hps
  have hrow := uniformRowBudget_le_polynomial N ps (ps.length-1)
    (stagedSourceBudget p S) (Subexp.UniversalRowSourceBound.sourceLengthBound S)
    (p.R+1) d (baseWidth 3 p.t)
    ((preparedSourceStore s (p.R+1) (d*baseWidth 3 p.t) ps v N f) 21).length
    ((preparedSourceStore s (p.R+1) (d*baseWidth 3 p.t) ps v N f) 26).length S
    hN hps hs (by omega)
    (by simpa [preparedSourceStore,initializeFinish] using h21)
    (by simpa [preparedSourceStore,initializeFinish] using h26)
  dsimp only [nativeRowsBudget,nativeRowsPolynomial]
  gcongr

end SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram

end OAI.Algorithms
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram.nativeRowsBudget_le_polynomial_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram.nativeRowsBudget_le_polynomial_oai
