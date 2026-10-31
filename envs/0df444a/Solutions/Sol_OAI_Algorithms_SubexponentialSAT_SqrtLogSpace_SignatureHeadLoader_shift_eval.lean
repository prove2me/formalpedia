-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureHeadLoader.shift_eval
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T06:38:30.991345+00:00
-- url     : https://prove2.me/submissions/097ce61e-9218-4ba0-b5a5-a5ac989a95ea

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S132
import Definitions.Def_OAIQ081S136
import Definitions.Def_OAIQ081S142
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_BucketProgram_preMatrixProgram_runsIn
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_LeafHeadSetupProgram_stageCost_linear

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_BucketProgramPreprocessBounds
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Integer semantics and explicit polynomial bounds for the concrete
signed-coefficient preprocessing machine. -/
namespace SubexponentialSAT.SqrtLog.BucketProgram

open SubexponentialSAT.BitProgram SubexponentialSAT.Subexp.MatrixProgramSupport

theorem preStepCost_le (W : List Bool) (a : SignedWord) (L : ℕ)
    (hW : W.length ≤ L) (hP : a.1.length ≤ L) (hN : a.2.length ≤ L) :
    preStepCost W a ≤ 6000*(L+1)^2 := by
  have hsum : W.length+a.2.length+a.1.length+1 ≤ 3*L+1 := by omega
  have hsq := Nat.pow_le_pow_left hsum 2
  dsimp [preStepCost]
  nlinarith

theorem preRow_inputs (W : List Bool) (xs : List SignedWord) (L : ℕ)
    (hW : W.length ≤ L) (hb : preWordsBounded L xs) :
    preScanCost W xs ≤ (xs.length+1)*(6000*(L+1)^2+2) ∧
    preOutputLength W xs ≤ xs.length*(3*L+1) ∧
    (signedWords xs).length ≤ xs.length*(4*L+2) := by
  induction xs with
  | nil => simp [preScanCost,preOutputLength,signedWords]
  | cons a xs ih =>
      have ha := hb a (by simp)
      have ht := ih (fun x hx => hb x (by simp [hx]))
      have hc := preStepCost_le W a L hW ha.1 ha.2
      rcases a with ⟨P,N⟩
      simp only [preScanCost,preOutputLength,List.map_cons,List.sum_cons,
        List.length_cons,signedWords,List.length_append,Encoding.length_frame] at *
      constructor
      · nlinarith [ht.1]
      constructor
      · nlinarith [ht.2.1]
      · nlinarith [ht.2.2]

theorem preRowCost_le (W : List Bool) (xs : List SignedWord) (L : ℕ)
    (hW : W.length ≤ L) (hb : preWordsBounded L xs) :
    preRowCost W xs ≤ 7000*(xs.length+1)*(L+1)^2 := by
  have h := preRow_inputs W xs L hW hb
  have hlin : 3*L+1 ≤ 3*(L+1)^2 := by nlinarith
  have hh := Nat.mul_le_mul_left xs.length hlin
  have hs : 1 ≤ (L+1)^2 := by nlinarith
  have hn := Nat.mul_le_mul_left xs.length hs
  dsimp [preRowCost]
  nlinarith [h.1,h.2.1]

theorem preMatrixStepCost_le (W : List Bool) (row : List SignedWord) (L : ℕ)
    (hW : W.length ≤ L) (hb : preWordsBounded L row) :
    preMatrixStepCost W row ≤ 8000*(row.length+1)*(L+1)^2 := by
  have h := preRow_inputs W row L hW hb
  have hr := preRowCost_le W row L hW hb
  have hlin : 4*L+2 ≤ 4*(L+1)^2 := by nlinarith
  have hlin' : 3*L+1 ≤ 3*(L+1)^2 := by nlinarith
  have hh := Nat.mul_le_mul_left row.length hlin
  have hh' := Nat.mul_le_mul_left row.length hlin'
  have hs : 1 ≤ (L+1)^2 := by nlinarith
  have hn := Nat.mul_le_mul_left row.length hs
  dsimp [preMatrixStepCost]
  nlinarith [h.2.1,h.2.2]

theorem preMatrix_inputs (W : List Bool) (rows : List (List SignedWord)) (L h : ℕ)
    (hW : W.length ≤ L)
    (hb : ∀ row∈rows, preWordsBounded L row ∧ row.length ≤ h) :
    preMatrixScanCost W rows ≤ (rows.length+1)*(8000*(h+1)*(L+1)^2+2) ∧
    preMatrixPayload W rows ≤ rows.length*(2*h*(3*L+1)+h) := by
  induction rows with
  | nil => simp [preMatrixScanCost,preMatrixPayload]
  | cons row rows ih =>
      have hr := hb row (by simp)
      have ht := ih (fun r hr' => hb r (by simp [hr']))
      have hc := preMatrixStepCost_le W row L hW hr.1
      have hc' : preMatrixStepCost W row ≤ 8000*(h+1)*(L+1)^2 :=
        hc.trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (by omega)))
      have hl := (preRow_inputs W row L hW hr.1).2.1
      have hl' := Nat.mul_le_mul_right (3*L+1) hr.2
      simp only [preMatrixScanCost,preMatrixPayload,List.map_cons,List.sum_cons,List.length_cons] at *
      constructor
      · nlinarith [ht.1]
      · nlinarith [ht.2]

theorem preMatrixCost_polynomial (W : List Bool) (rows : List (List SignedWord)) (L h : ℕ)
    (hW : W.length ≤ L)
    (hb : ∀ row∈rows, preWordsBounded L row ∧ row.length ≤ h) :
    preMatrixCost W rows+1 ≤ 10000*(rows.length+1)*(h+1)*(L+1)^2 := by
  have hi := preMatrix_inputs W rows L h hW hb
  have hlin : 3*L+1 ≤ 3*(L+1)^2 := by nlinarith
  have hp := Nat.mul_le_mul_left (rows.length*(2*h)) hlin
  have hs : 1 ≤ (L+1)^2 := by nlinarith
  have hh := Nat.mul_le_mul_left (rows.length*h) hs
  have hn := Nat.mul_le_mul_left rows.length hs
  have hz := Nat.mul_le_mul_left h hs
  dsimp [preMatrixCost]
  nlinarith [hi.1,hi.2]

end SubexponentialSAT.SqrtLog.BucketProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutMatrixProgramCompatibility
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Exact serialization and state projection at the all-row bucket boundary. -/
namespace SubexponentialSAT.SqrtLog.LayoutMatrixProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

theorem pairWords_eq_signedWords (ps : List Pair) : pairWords ps=BucketProgram.signedWords ps := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    rcases p with ⟨P,N⟩
    simp [pairWords,BucketProgram.signedWords,ih]

theorem rowsWords_eq (rows : List (List Pair)) :
    rowsWords rows=Subexp.MatrixProgramSupport.words (rows.map BucketProgram.signedWords) := by
  have hf : pairWords=BucketProgram.signedWords := funext pairWords_eq_signedWords
  rw [rowsWords,hf]

end SubexponentialSAT.SqrtLog.LayoutMatrixProgram

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

theorem work_ne_temporary {s : ℕ} (hs : s ≤ 288) (i : Fin s) :
    workPort hs i ≠ temporary := by
  intro h
  have := congrArg Fin.val h
  have := i.isLt
  simp only [workPort,temporary] at *
  omega

theorem protected_not_workPorts {s : ℕ} (hs : s ≤ 288) {i : Fin 768}
    (hi : Protected i) : i ∉ workPorts hs := by
  simp only [workPorts,List.mem_ofFn,not_exists]
  intro j h
  exact protected_ne_work hs hi j h.symm

theorem work_mem_workPorts {s : ℕ} (hs : s ≤ 288) (j : Fin s) :
    workPort hs j ∈ workPorts hs := by
  simp only [workPorts,List.mem_ofFn]
  exact ⟨j,rfl⟩

theorem inputCopies_good {s : ℕ} (hs : s ≤ 288) (ins : List (Fin 768 × Fin s))
    (hi : ∀ p ∈ ins, Protected p.1) :
    ∀ p ∈ inputCopies hs ins, p.1 ≠ p.2 ∧ p.1 ≠ temporary ∧ temporary ≠ p.2 := by
  intro p hp
  obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hp
  exact ⟨protected_ne_work hs (hi q hq) q.2,(hi q hq).2,(work_ne_temporary hs q.2).symm⟩

theorem outputCopies_good {s : ℕ} (hs : s ≤ 288) (outs : List (Fin s × Fin 768))
    (ho : ∀ p ∈ outs, Protected p.2) :
    ∀ p ∈ outputCopies hs outs, p.1 ≠ p.2 ∧ p.1 ≠ temporary ∧ temporary ≠ p.2 := by
  intro p hp
  obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hp
  exact ⟨(protected_ne_work hs (ho q hq) q.1).symm,work_ne_temporary hs q.1,(ho q hq).2.symm⟩

theorem prepared_word {s : ℕ} (hs : s ≤ 288) (ins : List (Fin 768 × Fin s))
    (a : Data) (hi : ∀ p ∈ ins, Protected p.1) (hd : (ins.map Prod.snd).Nodup)
    (p : Fin 768 × Fin s) (hp : p ∈ ins) :
    (prepared hs ins a).stacks (workPort hs p.2) = a.stacks p.1 := by
  have hd' : ((inputCopies hs ins).map Prod.snd).Nodup := by
    simpa only [inputCopies,List.map_map,Function.comp_def] using
      hd.map (workPort_injective hs)
  have hc : ∀ q ∈ inputCopies hs ins,
      (beforeCopies temporary (workPorts hs) a).stacks q.2 = [] := by
    intro q hq
    obtain ⟨z,hz,rfl⟩ := List.mem_map.mp hq
    simp only [beforeCopies,resetMany_stacks,clearMany_stacks,
      ite_eq_left (work_mem_workPorts hs z.2)]
  have hsep : ∀ q ∈ inputCopies hs ins, ∀ z ∈ inputCopies hs ins, q.1 ≠ z.2 := by
    intro q hq z hz
    obtain ⟨q',hq',rfl⟩ := List.mem_map.mp hq
    obtain ⟨z',hz',rfl⟩ := List.mem_map.mp hz
    exact protected_ne_work hs (hi q' hq') z'.2
  have hv := copyMany_value (inputCopies hs ins) (beforeCopies temporary (workPorts hs) a)
    hd' hc hsep (p.1,workPort hs p.2) (List.mem_map.mpr ⟨p,hp,rfl⟩)
  change (prepared hs ins a).stacks (workPort hs p.2) = _ at hv
  rw [hv]
  simp only [beforeCopies,resetMany_stacks,clearMany_stacks,
    ite_eq_right (protected_not_workPorts hs (hi p hp))]
  simp [(hi p hp).2]

theorem prepared_empty {s : ℕ} (hs : s ≤ 288) (ins : List (Fin 768 × Fin s))
    (a : Data) (j : Fin s) (hj : ∀ p ∈ ins,j ≠ p.2) :
    (prepared hs ins a).stacks (workPort hs j) = [] := by
  have hn : ∀ p ∈ inputCopies hs ins,workPort hs j ≠ p.2 := by
    intro p hp
    obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hp
    exact fun h => hj q hq (workPort_injective hs h)
  unfold prepared prepareState
  rw [copyMany_frame _ _ _ hn]
  simp only [beforeCopies,resetMany_stacks,clearMany_stacks,ite_eq_left (work_mem_workPorts hs j)]

theorem prepared_eq {r s : ℕ} (reg : Fin r → Fin 16) (hs : s ≤ 288)
    (ins : List (Fin 768 × Fin s)) (a : Data) (b : State r s)
    (hi : ∀ p ∈ ins,Protected p.1) (hd : (ins.map Prod.snd).Nodup)
    (hr : ∀ j,(prepared hs ins a).regs (reg j)=b.regs j)
    (hw : ∀ p ∈ ins,b.stacks p.2=a.stacks p.1)
    (hz : ∀ j,(∀ p ∈ ins,j≠p.2)→b.stacks j=[]) :
    projectState reg (workPort hs) (prepared hs ins a)=b := by
  apply congrArg₂ StructuredProgram.State.mk
  · funext j; exact hr j
  · funext j
    by_cases hm : ∃ p ∈ ins,p.2=j
    · obtain ⟨p,hp,rfl⟩ := hm
      exact (prepared_word hs ins a hi hd p hp).trans (hw p hp).symm
    · have hj : ∀ p ∈ ins,j≠p.2 := by
        intro p hp h; exact hm ⟨p,hp,h.symm⟩
      exact (prepared_empty hs ins a j hj).trans (hz j hj).symm

theorem stage_eval {r s l : ℕ} (p : Program r s l) (reg : Fin r → Fin 16)
    (hr : Function.Injective reg) (hs : s ≤ 288)
    (ins : List (Fin 768 × Fin s)) (outs : List (Fin s × Fin 768))
    (a : Data) (b c : State r s) {t : ℕ}
    (hi : ∀ q ∈ ins,Protected q.1) (ho : ∀ q ∈ outs,Protected q.2)
    (hl : projectState reg (workPort hs) (prepared hs ins a)=b)
    (ht : Trace p t (b.withPC (some p.entry)) (c.withPC none)) :
    Eval (stage p reg hs ins outs) (stageCost reg hs ins outs a c t) a
      (returned reg hs ins outs a c) := by
  apply isolated_eval p reg (workPort hs) hr (workPort_injective hs)
    temporary (workPorts hs) (inputCopies hs ins) (outputCopies hs outs) a c
    (inputCopies_good hs ins hi) (outputCopies_good hs outs ho)
  · rintro ⟨j,hj⟩; exact work_ne_temporary hs j hj
  · change Trace p t ((projectState reg (workPort hs) (prepared hs ins a)).withPC _) _
    rw [hl]
    exact ht

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
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_SignatureHeadLoaderCore
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! The fixed head-loader table uses the actual integer entry program. Its
physical matrix view follows LeafHeadSetupProgramHead/MatrixRun exactly, while
its controller emits one matrix and never constructs assignment tables. -/
noncomputable section
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureHeadLoader
open OAI BitProgram StructuredCalls OAI.Algorithms.SubexponentialSAT.SqrtLog
open OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgram
open OAI.Algorithms.SubexponentialSAT.SubexpSetupStorage

theorem shiftInputs_protected : ∀ p∈shiftInputs,Protected p.1 := by
  simp [shiftInputs,Protected,temporary]

theorem shiftOutputs_protected : ∀ p∈shiftOutputs,Protected p.2 := by
  simp [shiftOutputs,Protected,temporary]

/-- A local polynomial run gives a polynomial bound for every paid stage,
including input copies, dirty work-bank clearing, and output copies. -/
theorem stage_trace_bound {r q l t T A : ℕ} (p : Program r q l)
    (reg : Fin r → Fin 16) (hs : q ≤ 288)
    (ins : List (Fin 768 × Fin q)) (outs : List (Fin q × Fin 768))
    (a : Data) (b : State r q)
    (hi : ∀ v∈ins,Protected v.1) (ho : ∀ v∈outs,Protected v.2)
    (hdi : (ins.map Prod.snd).Nodup) (hdo : (outs.map Prod.snd).Nodup)
    (ha : WordBound A a) (ht : t ≤ T)
    (tr : Trace p t
      ((projectState reg (workPort hs) (prepared hs ins a)).withPC (some p.entry))
      (b.withPC none)) :
    stageCost reg hs ins outs a b t ≤ T+(6*q+7*ins.length+10*outs.length+21)*(A+T+1) ∧
    WordBound (A+T) (returned reg hs ins outs a b) := by
  have hp := prepared_wordBound hs ins a A hi hdi ha
  have hb : WordBound (A+T) b := by
    intro i
    have h := OAI.Algorithms.SubexponentialSAT.Subexp.SequentialProgram.trace_stack_length_le tr i
    change (b.stacks i).length ≤ ((prepared hs ins a).stacks (workPort hs i)).length + t at h
    exact h.trans (Nat.add_le_add (hp _) ht)
  have ha' : WordBound (A+T) a := fun i => (ha i).trans (Nat.le_add_right _ _)
  refine ⟨?_,returned_wordBound reg hs ins outs a b (A+T) hi ho hdi hdo ha' hb⟩
  exact (stageCost_linear reg hs ins outs a b t (A+T) hi ho hdi hdo ha' hb).trans
    (Nat.add_le_add_right ht _)

/-- Exact projection into the 17-stack preprocessing machine. -/
theorem shift_prepared (a : Data) (rows : List (List BucketProgram.SignedWord))
    (hr : a.stacks 669=LayoutMatrixProgram.rowsWords rows) :
    projectState shiftRegs (workPort (by decide)) (prepared (by decide) shiftInputs a)=
      BucketProgram.preMatrixState ((prepared (by decide) shiftInputs a).regs ∘ shiftRegs)
        (a.stacks 141) rows [] := by
  apply prepared_eq shiftRegs (by decide) shiftInputs a _ shiftInputs_protected (by decide)
  · intro j
    rfl
  · intro p hp
    simp only [shiftInputs,List.mem_cons,List.not_mem_nil,or_false] at hp
    rcases hp with rfl|rfl
    · simp [BucketProgram.preMatrixState]
    · simp [BucketProgram.preMatrixState,hr,LayoutMatrixProgram.rowsWords_eq]
  · intro j hj
    have h0 : j≠0 := hj (141,0) (by simp [shiftInputs])
    have h14 : j≠14 := hj (669,14) (by simp [shiftInputs])
    fin_cases j <;> simp_all [BucketProgram.preMatrixState]

/-- Paid shift staging reads the physically emitted signed rows. -/
theorem shift_eval_oai (a : Data) (rows : List (List BucketProgram.SignedWord))
    (hr : a.stacks 669=LayoutMatrixProgram.rowsWords rows) :
    ∃ rf ys t,
      List.Forall₂ (List.Forall₂ (BucketProgram.shiftedWord (a.stacks 141))) rows ys ∧
      t ≤ stageCost shiftRegs (by decide) shiftInputs shiftOutputs a
        (BucketProgram.preMatrixState rf (a.stacks 141) []
          (Subexp.MatrixProgramSupport.words (ys.map Subexp.MatrixProgramSupport.words)))
        (BucketProgram.preMatrixCost (a.stacks 141) rows+1) ∧
      Eval shiftCommand t a (returned shiftRegs (by decide) shiftInputs shiftOutputs a
        (BucketProgram.preMatrixState rf (a.stacks 141) []
          (Subexp.MatrixProgramSupport.words (ys.map Subexp.MatrixProgramSupport.words)))) ∧
      (returned shiftRegs (by decide) shiftInputs shiftOutputs a
        (BucketProgram.preMatrixState rf (a.stacks 141) []
          (Subexp.MatrixProgramSupport.words (ys.map Subexp.MatrixProgramSupport.words)))).stacks 668=
            Subexp.MatrixProgramSupport.words (ys.map Subexp.MatrixProgramSupport.words) ∧
      ∀ A L h,WordBound A a → (a.stacks 141).length ≤ L →
        (∀ row∈rows,BucketProgram.preWordsBounded L row ∧ row.length ≤ h) →
        let work := 10000*(rows.length+1)*(h+1)*(L+1)^2
        t ≤ work+147*(A+work+1) ∧
        WordBound (A+work) (returned shiftRegs (by decide) shiftInputs shiftOutputs a
          (BucketProgram.preMatrixState rf (a.stacks 141) []
            (Subexp.MatrixProgramSupport.words (ys.map Subexp.MatrixProgramSupport.words)))) := by
  obtain ⟨rf,ys,⟨t,ht,he⟩,hy⟩ := BucketProgram.preMatrixProgram_runsIn
    ((prepared (by decide) shiftInputs a).regs ∘ shiftRegs) (a.stacks 141) rows
  have hs := stage_eval BucketProgram.preMatrixProgram shiftRegs (Fin.castAdd_injective _ _)
    (by decide) shiftInputs shiftOutputs a _ _ shiftInputs_protected shiftOutputs_protected
    (shift_prepared a rows hr) he
  refine ⟨rf,ys,_,hy,?_,hs,?_,?_⟩
  · unfold stageCost
    omega
  · exact returned_word shiftRegs (by decide) shiftInputs shiftOutputs a _
      shiftOutputs_protected (by decide) (15,668) (by simp [shiftOutputs])
  · intro A L h ha hW hb
    have htime := ht.trans (BucketProgram.preMatrixCost_polynomial (a.stacks 141) rows L h hW hb)
    have hex := he
    rw [←shift_prepared a rows hr] at hex
    have hh := stage_trace_bound BucketProgram.preMatrixProgram shiftRegs
      (by decide) shiftInputs shiftOutputs a _ shiftInputs_protected shiftOutputs_protected
      (by decide) (by decide) ha htime hex
    simpa only [shiftInputs,shiftOutputs,List.length_cons,List.length_nil] using hh

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureHeadLoader
end
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureHeadLoader.shift_eval_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureHeadLoader.shift_eval_oai
