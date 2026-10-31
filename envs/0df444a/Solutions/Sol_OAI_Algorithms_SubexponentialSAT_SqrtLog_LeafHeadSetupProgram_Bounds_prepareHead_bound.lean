-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.Bounds.prepareHead_bound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T07:11:55.767866+00:00
-- url     : https://prove2.me/submissions/3997731c-b1d8-4327-ad43-45daed88992c

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S132
import Definitions.Def_OAIQ081S144
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_LeafHeadSetupProgram_stageCost_linear

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HeadIdentifierProgramRun
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.HeadIdentifierProgram
open SubexponentialSAT BitProgram StructuredCalls SubexpScanPrimitives

theorem budget_polynomial (n W L z : ℕ) :
    budget n W L z ≤ 300*(n+W+L+z+1)^3 := by
  let s := n+W+L+z+1
  have hn : n ≤ s := by dsimp [s]; omega
  have hW : W ≤ s := by dsimp [s]; omega
  have hL : L ≤ s := by dsimp [s]; omega
  have hz : z ≤ s := by dsimp [s]; omega
  have hs : 1 ≤ s := by dsimp [s]; omega
  have hs2 : s ≤ s^2 := by nlinarith
  have hs23 : s^2 ≤ s^3 := Nat.pow_le_pow_right hs (by decide)
  have hv : visitBound n W L z ≤ 200*s^2 := by
    calc
      _ ≤ s*(14*s+17)+15*s+22+22*s+9*s+10*s+2*s+43 := by
        unfold visitBound lookupCost
        gcongr
      _ ≤ 200*s^2 := by nlinarith
  have hm : n*(visitBound n W L z+2) ≤ 202*s^3 := by
    calc
      _ ≤ s*(200*s^2+2) := Nat.mul_le_mul hn (by omega)
      _ ≤ 202*s^3 := by nlinarith
  unfold budget
  change n*(visitBound n W L z+2)+7*n+26 ≤ 300*s^3
  nlinarith

end SubexponentialSAT.SqrtLog.HeadIdentifierProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HeadScatterProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Runtime scatter of head bits into the original ambient coordinate order.
Coordinate identifiers are framed unary words; array replacement is a genuine
runtime scan. No coordinate permutation is compiled into the instruction table. -/
namespace SubexponentialSAT.SqrtLog.HeadScatterProgram

open SubexponentialSAT BitProgram StructuredCalls Subexp.MatrixProgramSupport

theorem write_length (mask : List Bool) (j : ℕ) (bit : Bool) (hj : j < mask.length) :
    (write mask j bit).length = mask.length := by
  simp [write, List.length_take, List.length_drop, Nat.min_eq_left hj.le]
  omega

end SubexponentialSAT.SqrtLog.HeadScatterProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HeadScatterProgramScan
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.HeadScatterProgram
open SubexponentialSAT BitProgram StructuredCalls

theorem scatter_length (js : List ℕ) (bits mask : List Bool)
    (hb : ∀ j ∈ js, j < mask.length) :
    (scatter js bits mask).length = mask.length := by
  induction js generalizing bits mask with
  | nil => rfl
  | cons j js ih =>
      cases bits with
      | nil => rfl
      | cons b bits =>
          have hj := hb j (by simp)
          have hw := write_length mask j b hj
          have ht : ∀ k ∈ js, k < (write mask j b).length := by
            intro k hk; rw [hw]; exact hb k (by simp [hk])
          exact (ih bits _ ht).trans hw

end SubexponentialSAT.SqrtLog.HeadScatterProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HeadScatterProgramSemantics
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.HeadScatterProgram

theorem mask_length (n : ℕ) (js : List ℕ) (bits : List Bool)
    (hb : ∀ j ∈ js, j < n) : (mask n js bits).length = n := by
  simpa [mask] using scatter_length js bits (List.replicate n false) (by simpa using hb)

end SubexponentialSAT.SqrtLog.HeadScatterProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HeadScatterProgramRun
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.HeadScatterProgram
open SubexponentialSAT BitProgram StructuredCalls

theorem indices_length_bound (n : ℕ) (js : List ℕ) (hb : ∀ j ∈ js,j < n) :
    (indices js).length ≤ js.length*(2*n+2)+1 := by
  induction js with
  | nil => simp [indices,ProgramEncoding.encodeRecords,Encoding.encodeList]
  | cons j js ih =>
      have hj := hb j (by simp)
      have ht := ih (by intro k hk; exact hb k (by simp [hk]))
      simp only [indices,List.map_cons,ProgramEncoding.encodeRecords,Encoding.encodeList,
        List.length_cons,List.length_append,Encoding.length_frame, id_eq, unary,List.length_replicate]
      change 2*j+1+(indices js).length+1 ≤ (js.length+1)*(2*n+2)+1
      nlinarith

end SubexponentialSAT.SqrtLog.HeadScatterProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HeadIdentifierProgramSemantics
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.HeadIdentifierProgram
open SubexponentialSAT BitProgram StructuredCalls

theorem count_le (p : ℕ → Bool) (n : ℕ) : count p n ≤ n := by
  simpa [count,chosenIds] using List.length_filter_le p (List.range n)

theorem encodedIds_length_bound (p : ℕ → Bool) (n : ℕ) :
    (HeadScatterProgram.indices (chosenIds p n)).length ≤ n*(2*n+2)+1 := by
  calc
    _ ≤ (chosenIds p n).length*(2*n+2)+1 :=
      HeadScatterProgram.indices_length_bound n _ (chosenIds_bound p n)
    _ ≤ n*(2*n+2)+1 := Nat.add_le_add_right
      (Nat.mul_le_mul_right (2*n+2) (count_le p n)) 1

end SubexponentialSAT.SqrtLog.HeadIdentifierProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HeadIdentifierProgramFullTable
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.HeadIdentifierProgram.FullTable
open SubexponentialSAT BitProgram StructuredCalls SubexpScanPrimitives

theorem budget_polynomial (n totalRows W L z : ℕ) (hn : n ≤ totalRows) :
    budget n totalRows W L z ≤ 300*(totalRows+W+L+z+1)^3 := by
  calc
    _ ≤ HeadIdentifierProgram.budget totalRows W L z := by
      unfold budget HeadIdentifierProgram.budget
      gcongr
    _ ≤ _ := HeadIdentifierProgram.budget_polynomial totalRows W L z

end SubexponentialSAT.SqrtLog.HeadIdentifierProgram.FullTable

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafHeadFactorsProgramRun
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LeafHeadFactorsProgram
open SubexponentialSAT BitProgram StructuredCalls SubexpScanPrimitives

theorem budget_polynomial (A N M W z : ℕ) :
    budget A N M W z ≤ 1000*(A+N+M+W+z+1)^3 := by
  let s := A+N+M+W+z+1
  have hN : N ≤ s := by dsimp [s]; omega
  have hM : M ≤ s := by dsimp [s]; omega
  have hAM : A+M ≤ 2*s := by dsimp [s]; omega
  have hW : W ≤ s := by dsimp [s]; omega
  have hz : z ≤ s := by dsimp [s]; omega
  have hs : 1 ≤ s := by dsimp [s]; omega
  have hs2 : s ≤ s^2 := by nlinarith
  have hs23 : s^2 ≤ s^3 := Nat.pow_le_pow_right hs (by decide)
  have hv : visitBound A M W z ≤ 200*s^2 := by
    calc
      _ ≤ (2*s)*(14*s+17)+15*s+22+9*(2*s)+12*s+10*s+2*s+46 := by
        unfold visitBound lookupCost
        gcongr
      _ ≤ 200*s^2 := by nlinarith
  have hm : N*(visitBound A M W z+2) ≤ 202*s^3 := by
    calc
      _ ≤ s*(200*s^2+2) := Nat.mul_le_mul hN (by omega)
      _ ≤ 202*s^3 := by nlinarith
  unfold budget
  change N*(visitBound A M W z+2)+7*N+26 ≤ 1000*s^3
  nlinarith

end SubexponentialSAT.SqrtLog.LeafHeadFactorsProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafHeadFactorsProgramSemantics
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The physical row predicate selects exactly the computed factor colors. -/
namespace SubexponentialSAT.SqrtLog.LeafHeadFactorsProgram
open SubexponentialSAT BitProgram StructuredCalls MulticolorTypes

variable {I : Type*} [Fintype I] [DecidableEq I] {A N r Q : ℕ}

theorem chosenIds_bound (p : ℕ → Bool) (N : ℕ) : ∀ f ∈ chosenIds p N, f < N := by
  intro f hf
  exact List.mem_range.mp (List.mem_of_mem_filter hf)

theorem encodedIds_length_bound (p : ℕ → Bool) (N : ℕ) :
    (ProgramEncoding.encodeRecords ((chosenIds p N).map Encoding.encodeNat)).length ≤
      1 + (2 * N + 2) * N := by
  have h := ProgramEncoding.encodeRecords_length_le
    ((chosenIds p N).map Encoding.encodeNat) N (by
      intro payload hp
      obtain ⟨f, hf, rfl⟩ := List.mem_map.mp hp
      simpa using Nat.succ_le_of_lt (chosenIds_bound p N f hf))
  have hc : (chosenIds p N).length ≤ N := by
    simpa [chosenIds] using List.length_filter_le p (List.range N)
  simp only [List.length_map] at h
  exact h.trans (Nat.add_le_add_left (Nat.mul_le_mul_left _ hc) 1)

end SubexponentialSAT.SqrtLog.LeafHeadFactorsProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpSetupFrames
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.decidableMemJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.decidableMemSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Frame and value rules for the actual setup copy/cleanup routines. -/

namespace SubexponentialSAT.SubexpSetupStorage

open BitProgram StructuredCalls

theorem finish_value {S : ℕ} (ports : List (Fin S))
    (outputs : List (Fin S × Fin S)) (a : Data S)
    (hdup : (outputs.map Prod.snd).Nodup)
    (hsep : ∀ p ∈ outputs, ∀ q ∈ outputs, p.1 ≠ q.2)
    (p : Fin S × Fin S) (hp : p ∈ outputs) (hport : p.2 ∉ ports) :
    (finishState ports outputs a).stacks p.2 = a.stacks p.1 := by
  have hc : ∀ q ∈ outputs, (clearManyState (outputs.map Prod.snd) a).stacks q.2 = [] := by
    intro q hq
    rw [clearMany_stacks, ite_eq_left (List.mem_map.mpr ⟨q, hq, rfl⟩)]
  have hs : p.1 ∉ outputs.map Prod.snd := by
    intro hm
    obtain ⟨q, hq, he⟩ := List.mem_map.mp hm
    exact hsep p hp q hq he.symm
  unfold finishState
  rw [resetMany_stacks, clearMany_stacks, ite_eq_right hport,
    copyMany_value _ _ hdup hc hsep p hp, clearMany_stacks, ite_eq_right hs]

end SubexponentialSAT.SubexpSetupStorage

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpSetupStorageCost
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Cost of the concrete setup storage instructions

Copying and cleanup are charged by the lengths of the words physically read.
The final stage bound is linear in a common word bound; its coefficients depend
only on the statically allocated ports and copy lists.
-/

namespace SubexponentialSAT.SubexpSetupStorage

open BitProgram StructuredCalls

theorem resetMany_wordBound {S : ℕ} (rs : List (Fin 16)) (a : Data S) (B : ℕ)
    (ha : WordBound B a) : WordBound B (resetManyState rs a) := by
  intro i
  simpa only [resetMany_stacks] using ha i

theorem beforeCopies_wordBound {S : ℕ} (tmp : Fin S) (ports : List (Fin S))
    (a : Data S) (B : ℕ) (ha : WordBound B a) :
    WordBound B (beforeCopies tmp ports a) :=
  resetMany_wordBound _ _ B
    (clearMany_wordBound ports _ B (clearMany_wordBound [tmp] a B ha))

theorem prepare_wordBound {S : ℕ} (tmp : Fin S) (ports : List (Fin S))
    (inputs : List (Fin S × Fin S)) (a : Data S) (B : ℕ)
    (hd : (inputs.map Prod.snd).Nodup)
    (hp : ∀ p ∈ inputs, p.2 ∈ ports)
    (hsep : ∀ p ∈ inputs, ∀ q ∈ inputs, p.1 ≠ q.2)
    (ha : WordBound B a) : WordBound B (prepareState tmp ports inputs a) := by
  apply copyMany_wordBound inputs _ B hd _ hsep (beforeCopies_wordBound tmp ports a B ha)
  intro p hm
  simp only [beforeCopies, resetMany_stacks, clearMany_stacks, ite_eq_left (hp p hm)]

theorem finishCopies_wordBound {S : ℕ} (outputs : List (Fin S × Fin S))
    (a : Data S) (B : ℕ) (hd : (outputs.map Prod.snd).Nodup)
    (hsep : ∀ p ∈ outputs, ∀ q ∈ outputs, p.1 ≠ q.2)
    (ha : WordBound B a) :
    WordBound B (copyManyState outputs (clearManyState (outputs.map Prod.snd) a)) := by
  apply copyMany_wordBound outputs _ B hd _ hsep
    (clearMany_wordBound (outputs.map Prod.snd) a B ha)
  intro p hp
  rw [clearMany_stacks, ite_eq_left (List.mem_map.mpr ⟨p, hp, rfl⟩)]

theorem finish_wordBound {S : ℕ} (ports : List (Fin S))
    (outputs : List (Fin S × Fin S)) (a : Data S) (B : ℕ)
    (hd : (outputs.map Prod.snd).Nodup)
    (hsep : ∀ p ∈ outputs, ∀ q ∈ outputs, p.1 ≠ q.2)
    (ha : WordBound B a) : WordBound B (finishState ports outputs a) :=
  resetMany_wordBound _ _ B
    (clearMany_wordBound ports _ B (finishCopies_wordBound outputs a B hd hsep ha))

theorem embedState_wordBound {r s S : ℕ} (register : Fin r → Fin 16)
    (stack : Fin s → Fin S) (frame : Data S) (out : State r s) (B : ℕ)
    (hs : Function.Injective stack) (hf : WordBound B frame) (ho : WordBound B out) :
    WordBound B (embedState register stack frame out) := by
  intro i
  by_cases hm : ∃ j, stack j = i
  · obtain ⟨j, rfl⟩ := hm
    rw [embedState_stack register stack frame out hs j]
    exact ho j
  · rw [embedState_stack_frame register stack frame out i hm]
    exact hf i

end SubexponentialSAT.SubexpSetupStorage

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafHeadSetupProgramStorage
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Paid, isolated service calls in the leaf head-builder's reserved bank.
The entire local service bank is moved to340..627. In particular a matrix
entry bank cannot overwrite the persistent ring tables below340. -/
noncomputable section

namespace SubexponentialSAT.SqrtLog.LeafHeadSetupProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.SubexpSetupStorage

theorem workPort_injective {s : ℕ} (hs : s ≤ 288) : Function.Injective (workPort hs) := by
  intro i j h
  apply Fin.ext
  have := congrArg Fin.val h
  simp only [workPort] at this
  omega

theorem protected_ne_work {s : ℕ} (hs : s ≤ 288) {i : Fin 768}
    (hi : Protected i) (j : Fin s) : i ≠ workPort hs j := by
  intro h
  have := congrArg Fin.val h
  have := j.isLt
  simp only [workPort] at *
  rcases hi.1 with h | h <;> omega

theorem protected_not_workPorts {s : ℕ} (hs : s ≤ 288) {i : Fin 768}
    (hi : Protected i) : i ∉ workPorts hs := by
  simp only [workPorts,List.mem_ofFn,not_exists]
  intro j h
  exact protected_ne_work hs hi j h.symm

theorem work_mem_workPorts {s : ℕ} (hs : s ≤ 288) (j : Fin s) :
    workPort hs j ∈ workPorts hs := by
  simp only [workPorts,List.mem_ofFn]
  exact ⟨j,rfl⟩

theorem returned_word {r s : ℕ} (reg : Fin r → Fin 16) (hs : s ≤ 288)
    (ins : List (Fin 768 × Fin s)) (outs : List (Fin s × Fin 768))
    (a : Data) (b : State r s) (ho : ∀ q ∈ outs,Protected q.2)
    (hd : (outs.map Prod.snd).Nodup) (p : Fin s × Fin 768) (hp : p ∈ outs) :
    (returned reg hs ins outs a b).stacks p.2=b.stacks p.1 := by
  have hd' : ((outputCopies hs outs).map Prod.snd).Nodup := by
    simpa only [outputCopies,List.map_map,Function.comp_def] using hd
  have hsep : ∀ q ∈ outputCopies hs outs,∀ z ∈ outputCopies hs outs,q.1≠z.2 := by
    intro q hq z hz
    obtain ⟨q',hq',rfl⟩ := List.mem_map.mp hq
    obtain ⟨z',hz',rfl⟩ := List.mem_map.mp hz
    exact (protected_ne_work hs (ho z' hz') q'.1).symm
  exact (finish_value (workPorts hs) (outputCopies hs outs) _ hd' hsep
    (workPort hs p.1,p.2) (List.mem_map.mpr ⟨p,hp,rfl⟩)
    (protected_not_workPorts hs (ho p hp))).trans
      (embedState_stack reg (workPort hs) _ b (workPort_injective hs) p.1)

end SubexponentialSAT.SqrtLog.LeafHeadSetupProgram

end

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafHeadSetupProgramSelection
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Actual original/factor ID selection from the common full word table.
The input masters are copied into an isolated lookup program, and its output
records are copied back before the entire lookup workspace is cleared. -/
noncomputable section

namespace SubexponentialSAT.SqrtLog.LeafHeadSetupProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

theorem headInputs_protected : ∀ p ∈ headInputs,Protected p.1 := by simp [headInputs,Protected,temporary]
theorem headOutputs_protected : ∀ p ∈ headOutputs,Protected p.2 := by simp [headOutputs,Protected,temporary]

theorem headResult_count (a : Data) (n : ℕ) (rows : List (List Bool)) (low : List Bool) (W z : ℕ) :
    (headResult a n rows low W z).stacks 651=
      zeros (HeadIdentifierProgram.count (HeadIdentifierProgram.predicate rows low z) n) := by
  exact returned_word id (by decide) headInputs headOutputs a _ headOutputs_protected
    (by decide) (1,651) (by simp [headOutputs])

theorem factorInputs_protected : ∀ p ∈ factorInputs,Protected p.1 := by simp [factorInputs,Protected,temporary]
theorem factorOutputs_protected : ∀ p ∈ factorOutputs,Protected p.2 := by simp [factorOutputs,Protected,temporary]

end SubexponentialSAT.SqrtLog.LeafHeadSetupProgram

end

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafHeadSetupProgramSupport
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Construct the full ambient head-support mask from the IDs actually
selected. A low-variable mask alone is not a head-support mask. -/
noncomputable section

namespace SubexponentialSAT.SqrtLog.LeafHeadSetupProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

theorem countInputs_protected : ∀ p∈countInputs,Protected p.1 := by simp [countInputs,Protected,temporary]
theorem countOutputs_protected : ∀ p∈countOutputs,Protected p.2 := by simp [countOutputs,Protected,temporary]

theorem scatterInputs_protected : ∀ p∈scatterInputs,Protected p.1 := by simp [scatterInputs,Protected,temporary]
theorem scatterOutputs_protected : ∀ p∈scatterOutputs,Protected p.2 := by simp [scatterOutputs,Protected,temporary]

end SubexponentialSAT.SqrtLog.LeafHeadSetupProgram

end

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafHeadSetupProgramStorageBounds
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Linear paid staging overhead. This bound counts the copied words and
cleared cells, including produced output streams. It adds no unit-cost data
movement to any of the native service bounds. -/
noncomputable section
namespace SubexponentialSAT.SqrtLog.LeafHeadSetupProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.SubexpSetupStorage

theorem inputCopies_separated {s : ℕ} (hs : s ≤ 288) (ins : List (Fin 768 × Fin s))
    (hi : ∀ p∈ins,Protected p.1) :
    ∀ p∈inputCopies hs ins,∀ q∈inputCopies hs ins,p.1≠q.2 := by
  intro p hp q hq
  obtain ⟨p',hp',rfl⟩ := List.mem_map.mp hp
  obtain ⟨q',hq',rfl⟩ := List.mem_map.mp hq
  exact protected_ne_work hs (hi p' hp') q'.2

theorem outputCopies_separated {s : ℕ} (hs : s ≤ 288) (outs : List (Fin s × Fin 768))
    (ho : ∀ p∈outs,Protected p.2) :
    ∀ p∈outputCopies hs outs,∀ q∈outputCopies hs outs,p.1≠q.2 := by
  intro p hp q hq
  obtain ⟨p',hp',rfl⟩ := List.mem_map.mp hp
  obtain ⟨q',hq',rfl⟩ := List.mem_map.mp hq
  exact (protected_ne_work hs (ho q' hq') p'.1).symm

theorem prepared_wordBound {s : ℕ} (hs : s ≤ 288) (ins : List (Fin 768 × Fin s))
    (a : Data) (B : ℕ) (hi : ∀ p∈ins,Protected p.1) (hd : (ins.map Prod.snd).Nodup)
    (ha : WordBound B a) : WordBound B (prepared hs ins a) := by
  apply prepare_wordBound _ _ _ _ B _ _ (inputCopies_separated hs ins hi) ha
  · simpa only [inputCopies,List.map_map,Function.comp_def] using hd.map (workPort_injective hs)
  · intro p hp
    obtain ⟨p',hp',rfl⟩ := List.mem_map.mp hp
    exact work_mem_workPorts hs p'.2

theorem returned_wordBound {r s : ℕ} (reg : Fin r → Fin 16) (hs : s ≤ 288)
    (ins : List (Fin 768 × Fin s)) (outs : List (Fin s × Fin 768))
    (a : Data) (b : State r s) (B : ℕ)
    (hi : ∀ p∈ins,Protected p.1) (ho : ∀ p∈outs,Protected p.2)
    (hdi : (ins.map Prod.snd).Nodup) (hdo : (outs.map Prod.snd).Nodup)
    (ha : WordBound B a) (hb : WordBound B b) :
    WordBound B (returned reg hs ins outs a b) := by
  have hd : ((outputCopies hs outs).map Prod.snd).Nodup := by
    simpa only [outputCopies,List.map_map,Function.comp_def] using hdo
  exact finish_wordBound _ _ _ B hd (outputCopies_separated hs outs ho)
    (embedState_wordBound reg (workPort hs) (prepared hs ins a) b B
      (workPort_injective hs) (prepared_wordBound hs ins a B hi hdi ha) hb)

end SubexponentialSAT.SqrtLog.LeafHeadSetupProgram

end

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafHeadSetupProgramBoundsPrepare
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fixed polynomial cost of actual head-ID, support-mask, and factor-ID
preparation. Bounds include the real isolated-bank copy/cleanup costs. -/
noncomputable section
namespace SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.Bounds
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.SubexpSetupStorage

 theorem wordBound_mono {r s A B : ℕ} {a : State r s} (h : WordBound A a) (hab : A ≤ B) :
    WordBound B a := fun i => (h i).trans hab

 theorem selectedHeads_length (n : ℕ) (rows : List (List Bool)) (low : List Bool) (z : ℕ) :
    (selectedHeads n rows low z).length ≤ n :=
  HeadIdentifierProgram.count_le _ _

 theorem quadratic_ids (n s : ℕ) (hn : n ≤ s) (hs : 1 ≤ s) : n*(2*n+2)+1 ≤ 5*s^2 := by
  have hsq := Nat.mul_self_le_mul_self hn
  nlinarith only [hn,hs,hsq]

 theorem head_local_bound (n : ℕ) (rows : List (List Bool)) (low : List Bool)
    (W z s : ℕ) (hn : n ≤ s) (hr : rows.flatten.length ≤ s) (hl : low.length ≤ s)
    (hW : W ≤ s) (hz : z ≤ s) (hs : 1 ≤ s) :
    WordBound (5*s^2) (HeadIdentifierProgram.FullTable.result n rows low W z) := by
  have hsmall : s ≤ 5*s^2 := by nlinarith only [hs]
  have hi := (HeadIdentifierProgram.encodedIds_length_bound
    (HeadIdentifierProgram.predicate rows low z) n).trans (quadratic_ids n s hn hs)
  have hc := (HeadIdentifierProgram.count_le (HeadIdentifierProgram.predicate rows low z) n).trans hn
  intro i
  by_cases h0 : i=0
  · subst i
    exact hi
  by_cases h1 : i=1
  · subst i
    simpa [HeadIdentifierProgram.FullTable.result,HeadIdentifierProgram.zeros] using hc.trans hsmall
  simp only [HeadIdentifierProgram.FullTable.result,Function.update_of_ne h0,Function.update_of_ne h1]
  simp only [HeadIdentifierProgram.FullTable.baseStacks]
  split_ifs <;> (try simp only [List.length_replicate, List.length_nil]) <;> omega

 theorem factor_local_bound (n N : ℕ) (rows : List (List Bool)) (W z s : ℕ)
    (hn : n ≤ s) (hN : N ≤ s) (hr : rows.flatten.length ≤ s)
    (hW : W ≤ s) (hz : z ≤ s) (hs : 1 ≤ s) :
    WordBound (5*s^2) (LeafHeadFactorsProgram.result rows n N W z) := by
  have hsmall : s ≤ 5*s^2 := by nlinarith only [hs]
  have hi := LeafHeadFactorsProgram.encodedIds_length_bound
    (LeafHeadFactorsProgram.predicate rows n z) N
  have hi' : (SubexponentialSAT.ProgramEncoding.encodeRecords
      ((LeafHeadFactorsProgram.chosenIds (LeafHeadFactorsProgram.predicate rows n z) N).map
        SubexponentialSAT.Encoding.encodeNat)).length ≤ 5*s^2 := by
    apply hi.trans
    simpa only [Nat.mul_comm,Nat.add_comm] using quadratic_ids N s hN hs
  have hc : LeafHeadFactorsProgram.count (LeafHeadFactorsProgram.predicate rows n z) N ≤ N := by
    simpa [LeafHeadFactorsProgram.count,LeafHeadFactorsProgram.chosenIds] using
      List.length_filter_le (LeafHeadFactorsProgram.predicate rows n z) (List.range N)
  intro i
  by_cases h0 : i=0
  · subst i; exact hi'
  by_cases h1 : i=1
  · subst i
    simpa [LeafHeadFactorsProgram.result,LeafHeadFactorsProgram.zeros] using (hc.trans hN).trans hsmall
  simp only [LeafHeadFactorsProgram.result,Function.update_of_ne h0,Function.update_of_ne h1]
  simp only [LeafHeadFactorsProgram.baseStacks]
  split_ifs <;> (try simp only [List.length_replicate, List.length_nil]) <;> omega

 theorem scatter_local_bound (regs : Fin 8 → Bool) (n : ℕ) (rows : List (List Bool))
    (low : List Bool) (z s : ℕ) (hn : n ≤ s) (hs : 1 ≤ s) :
    WordBound (5*s^2) (HeadScatterProgram.result regs (selectedHeads n rows low z)
      (List.replicate (selectedHeads n rows low z).length true) n) := by
  have hsmall : s ≤ 5*s^2 := by nlinarith only [hs]
  have hi := (HeadIdentifierProgram.encodedIds_length_bound
    (HeadIdentifierProgram.predicate rows low z) n).trans (quadratic_ids n s hn hs)
  have hc := (selectedHeads_length n rows low z).trans hn
  have hm := HeadScatterProgram.mask_length n (selectedHeads n rows low z)
    (List.replicate (selectedHeads n rows low z).length true)
    (HeadIdentifierProgram.chosenIds_bound _ _)
  intro i
  fin_cases i <;> simp only [HeadScatterProgram.result,Matrix.cons_val_succ',Matrix.cons_val_zero',
    List.length_nil,List.length_replicate,HeadScatterProgram.unary] <;>
    first | exact hi | omega

 theorem prepareHead_bound_oai (a : Data) (regs : Fin 8 → Bool) (n N : ℕ)
    (rows : List (List Bool)) (low : List Bool) (W z A : ℕ)
    (ha : WordBound A a) (hsize : n ≤ rows.length) :
    let s := preparationSize n N rows low W z
    WordBound (A+5*s^2) (preparedHead a regs n N rows low W z) ∧
    prepareHeadCost a regs n N rows low W z ≤ 100000*(A+s^3+1) := by
  let s := preparationSize n N rows low W z
  let B := A+5*s^2
  have hs : 1 ≤ s := by dsimp [s,preparationSize]; omega
  have hn : n ≤ s := by dsimp [s,preparationSize]; omega
  have hN : N ≤ s := by dsimp [s,preparationSize]; omega
  have hr : rows.flatten.length ≤ s := by dsimp [s,preparationSize]; omega
  have hl : low.length ≤ s := by dsimp [s,preparationSize]; omega
  have hW : W ≤ s := by dsimp [s,preparationSize]; omega
  have hz : z ≤ s := by dsimp [s,preparationSize]; omega
  have hsmall : s ≤ 5*s^2 := by nlinarith only [hs]
  have ha' : WordBound B a := wordBound_mono ha (by dsimp [B]; omega)
  have hh : WordBound B (HeadIdentifierProgram.FullTable.result n rows low W z) :=
    wordBound_mono (head_local_bound n rows low W z s hn hr hl hW hz hs) (by dsimp [B]; omega)
  have hhead : WordBound B (headResult a n rows low W z) :=
    returned_wordBound id (by decide) headInputs headOutputs a _ B
      headInputs_protected headOutputs_protected (by decide) (by decide) ha' hh
  let b := headResult a n rows low W z
  have hbl : (b.stacks 651).length ≤ s := by
    rw [headResult_count]
    simpa [zeros] using (HeadIdentifierProgram.count_le _ n).trans hn
  have hcountLocal : WordBound B (PackingHeadProgramPrepareCount.state (fun _=>false) []
      (List.replicate (b.stacks 651).length true)) := by
    intro i; fin_cases i <;> simp [PackingHeadProgramPrepareCount.state] ;
      exact hbl.trans (hsmall.trans (by dsimp [B]; omega))
  have hcount : WordBound B (countResult b) :=
    returned_wordBound countRegs (by decide) countInputs countOutputs b _ B
      countInputs_protected countOutputs_protected (by decide) (by decide) hhead hcountLocal
  let c := countResult b
  let js := selectedHeads n rows low z
  have hscatterLocal : WordBound B (HeadScatterProgram.result regs js (List.replicate js.length true) n) :=
    wordBound_mono (scatter_local_bound regs n rows low z s hn hs) (by dsimp [B]; omega)
  have hscatter : WordBound B (scatterResult c regs n js) :=
    returned_wordBound scatterRegs (by decide) scatterInputs scatterOutputs c _ B
      scatterInputs_protected scatterOutputs_protected (by decide) (by decide) hcount hscatterLocal
  let d := scatterResult c regs n js
  have hf : WordBound B (LeafHeadFactorsProgram.result rows n N W z) :=
    wordBound_mono (factor_local_bound n N rows W z s hn hN hr hW hz hs) (by dsimp [B]; omega)
  have hfactor : WordBound B (factorResult d n N rows W z) :=
    returned_wordBound id (by decide) factorInputs factorOutputs d _ B
      factorInputs_protected factorOutputs_protected (by decide) (by decide) hscatter hf
  refine ⟨hfactor,?_⟩
  have ch := stageCost_linear id (by decide) headInputs headOutputs a _
    (HeadIdentifierProgram.FullTable.budget n rows.length W low.length z) B
    headInputs_protected headOutputs_protected (by decide) (by decide) ha' hh
  have cc := stageCost_linear countRegs (by decide) countInputs countOutputs b _
    (4*(b.stacks 651).length+4) B countInputs_protected countOutputs_protected
    (by decide) (by decide) hhead hcountLocal
  have cs := stageCost_linear scatterRegs (by decide) scatterInputs scatterOutputs c _
    (100*(n+1)*(js.length+1)) B scatterInputs_protected scatterOutputs_protected
    (by decide) (by decide) hcount hscatterLocal
  have cf := stageCost_linear id (by decide) factorInputs factorOutputs d _
    (LeafHeadFactorsProgram.budget n N rows.length W z) B
    factorInputs_protected factorOutputs_protected (by decide) (by decide) hscatter hf
  have hch : HeadIdentifierProgram.FullTable.budget n rows.length W low.length z ≤ 300*s^3 :=
    (HeadIdentifierProgram.FullTable.budget_polynomial n rows.length W low.length z hsize).trans
      (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by dsimp [s,preparationSize]; omega) 3))
  have hcf : LeafHeadFactorsProgram.budget n N rows.length W z ≤ 1000*s^3 :=
    (LeafHeadFactorsProgram.budget_polynomial n N rows.length W z).trans
      (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by dsimp [s,preparationSize]; omega) 3))
  have hjs : js.length ≤ s := (selectedHeads_length n rows low z).trans hn
  have hcs : 100*(n+1)*(js.length+1) ≤ 400*s^2 := by
    calc
      _ ≤ 100*(s+1)*(s+1) := by gcongr
      _ ≤ 400*s^2 := by nlinarith only [hs]
  have h23 : s^2 ≤ s^3 := pow_le_pow_right₀ hs (by decide)
  change headCost a n rows low W z+countCost b+scatterCost c regs n js+factorCost d n N rows W z ≤ _
  change headCost a n rows low W z ≤ _ at ch
  change countCost b ≤ _ at cc
  change scatterCost c regs n js ≤ _ at cs
  change factorCost d n N rows W z ≤ _ at cf
  norm_num [headInputs,headOutputs,countInputs,countOutputs,scatterInputs,scatterOutputs,
    factorInputs,factorOutputs] at ch cc cs cf
  dsimp [B] at ch cc cs cf
  nlinarith only [ch,cc,cs,cf,hch,hcf,hcs,hbl,hsmall,h23]

end SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.Bounds

end
end OAI.Algorithms
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.Bounds.prepareHead_bound_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.Bounds.prepareHead_bound_oai
