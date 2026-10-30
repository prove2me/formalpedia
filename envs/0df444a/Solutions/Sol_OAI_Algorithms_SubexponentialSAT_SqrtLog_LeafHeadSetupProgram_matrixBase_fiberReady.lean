-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.matrixBase_fiberReady
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T05:53:27.102466+00:00
-- url     : https://prove2.me/submissions/7b9f3d7a-627c-42a6-8ea5-6c83ac8380e0

import Mathlib
import Definitions.Def_OAIQ081S122
import Definitions.Def_OAIQ081S125

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafHeadSetupProgramEntryReady
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The paid sparse matrix cache satisfies the actual fiber wrapper's empty
scratch-bank precondition; no unframed ambient storage is passed to it. -/
noncomputable section
namespace SubexponentialSAT.SqrtLog.LeafHeadSetupProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

theorem matrixBase_empty (a : Data) (k : Fin 288)
    (hlo : 25 ≤ k.val) (hrange : k.val < 225 ∨ 236 < k.val) : matrixBase a k=[] := by
  have hn (v : Fin 288) (hv : v.val < 25 ∨ 225 ≤ v.val ∧ v.val ≤ 236) : k≠v := by
    intro he
    subst k
    omega
  simp [matrixBase,hn 0 (by decide),hn 17 (by decide),hn 18 (by decide),hn 23 (by decide),
    hn 225 (by decide),hn 226 (by decide),hn 227 (by decide),hn 228 (by decide),
    hn 229 (by decide),hn 230 (by decide),hn 231 (by decide),hn 232 (by decide),
    hn 233 (by decide),hn 234 (by decide),hn 235 (by decide),hn 236 (by decide)]

theorem matrixBase_entry_low (a : Data) (i : Fin 256) (hi : i.val < 200) :
    matrixBase a (LayoutMatrixProgram.bankPort i)=[] := by
  apply matrixBase_empty
  · simp [LayoutMatrixProgram.bankPort]
  · left
    simp only [LayoutMatrixProgram.bankPort]
    omega

theorem matrixBase_entry_high (a : Data) (i : Fin 256) (hi : 212 ≤ i.val) :
    matrixBase a (LayoutMatrixProgram.bankPort i)=[] := by
  apply matrixBase_empty
  · simp [LayoutMatrixProgram.bankPort]
  · right
    simp only [LayoutMatrixProgram.bankPort]
    omega

theorem matrixBase_fiberReady_oai (a : Data) (regs : Fin 16 → Bool) (row col : List Bool) :
    LayoutFiberSumProgram.Ready (LayoutMatrixProgram.entryState (matrixBase a) regs row col [] []) := by
  constructor
  · intro i hi
    have h252 : i≠252 := by
      intro h
      have he : i.val=(252:ℕ) := congrArg Fin.val h
      omega
    have h253 : i≠253 := by
      intro h
      have he : i.val=(253:ℕ) := congrArg Fin.val h
      omega
    have h254 : i≠254 := by
      intro h
      have he : i.val=(254:ℕ) := congrArg Fin.val h
      omega
    have h255 : i≠255 := by
      intro h
      have he : i.val=(255:ℕ) := congrArg Fin.val h
      omega
    simpa [LayoutMatrixProgram.entryState,h252,h253,h254,h255] using matrixBase_entry_low a i hi
  · intro i hlo hhi
    have h252 : i≠252 := by
      intro h
      have he : i.val=(252:ℕ) := congrArg Fin.val h
      omega
    have h253 : i≠253 := by
      intro h
      have he : i.val=(253:ℕ) := congrArg Fin.val h
      omega
    have h254 : i≠254 := by
      intro h
      have he : i.val=(254:ℕ) := congrArg Fin.val h
      omega
    have h255 : i≠255 := by
      intro h
      have he : i.val=(255:ℕ) := congrArg Fin.val h
      omega
    simpa [LayoutMatrixProgram.entryState,h252,h253,h254,h255] using matrixBase_entry_high a i hlo

end SubexponentialSAT.SqrtLog.LeafHeadSetupProgram

end
end OAI.Algorithms
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.matrixBase_fiberReady_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.matrixBase_fiberReady_oai
