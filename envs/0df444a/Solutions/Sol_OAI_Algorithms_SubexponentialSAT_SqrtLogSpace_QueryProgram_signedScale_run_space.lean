-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryProgram.signedScale_run_space
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T09:50:42.673248+00:00
-- url     : https://prove2.me/submissions/375676c0-9c52-441c-8552-b5c51853e01a

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S178
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_StructuredSpace_local_stack_bound

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_SquarefreeProgramFrame
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A fixed frame emitter. The source is a reversed payload. It is consumed
and the forward framed payload is prepended to the destination. -/
namespace SubexponentialSAT.SqrtLog.Squarefree.Program
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredProgram

theorem frameBody_eval (regs : Fin 3 → Bool) (b : Bool)
    (source output : List Bool) (htrue : regs 2 = true) :
    Eval frameBody 3 (frameReady regs (b :: source) output)
      (frameReady (readRegs regs 0 1 (some b)) source (true :: b :: output)) := by
  let d := frameReady regs (b :: source) output
  let d1 := (Atom.push (1 : Fin 2) (0 : Fin 3)).eval d
  let d2 := (Atom.push (1 : Fin 2) (2 : Fin 3)).eval d1
  have hh := Eval.seq (Eval.atom (Atom.push (1 : Fin 2) (0 : Fin 3)) d)
    (Eval.seq (Eval.atom (Atom.push (1 : Fin 2) (2 : Fin 3)) d1)
      (Eval.atom (Atom.pop (0 : Fin 2) (0 : Fin 3) 1) d2))
  convert hh using 1 ;
    simp [ frameReady, frameData, d, d1, d2, Atom.eval, Atom.instr,
      State.ofCfg, execInstr, readRegs, htrue] ;
    try (first | done | (funext i; fin_cases i <;> rfl))

theorem frameLoop_eval (source output : List Bool) (regs : Fin 3 → Bool)
    (htrue : regs 2 = true) :
    ∃ final, final 2 = true ∧ Eval frameLoop (4 * source.length + 1)
      (frameReady regs source output) (frameData final [] (emitPairs source output)) := by
  induction source generalizing regs output with
  | nil =>
    refine ⟨readRegs regs 0 1 none, by simpa [readRegs] using htrue, ?_⟩
    apply Eval.while_false
    simp [frameReady, frameData, readRegs]
  | cons b bs ih =>
    have hr : (readRegs regs 0 1 (some b)) 2 = true := by simpa [readRegs] using htrue
    obtain ⟨final, hf, he⟩ := ih (true :: b :: output) (readRegs regs 0 1 (some b)) hr
    refine ⟨final, hf, ?_⟩
    have hh := Eval.while_true
      (by simp [frameReady, frameData, readRegs] : (frameReady regs (b :: bs) output).regs 1 = true)
      (frameBody_eval regs b bs output htrue) he
    have hc : 3 + (4 * bs.length + 1) + 1 = 4 * (b :: bs).length + 1 := by simp; omega
    rw [hc] at hh
    exact hh

theorem emitPairs_append (a b out : List Bool) :
    emitPairs (a ++ b) out = emitPairs b (emitPairs a out) := by
  induction a generalizing out with
  | nil => rfl
  | cons x xs ih => simpa [emitPairs] using ih (true :: x :: out)

theorem emitPairs_frame (source out : List Bool) :
    emitPairs source.reverse (false :: out) = Encoding.frame source ++ out := by
  induction source with
  | nil => rfl
  | cons b bs ih =>
    simp [List.reverse_cons, emitPairs_append, emitPairs, ih, Encoding.frame ]

theorem frameEmit_eval (source output : List Bool) (regs : Fin 3 → Bool) :
    ∃ final, Eval frameEmit (4 * source.length + 5)
      (frameData regs source.reverse output)
      (frameData final [] (Encoding.frame source ++ output)) := by
  let r0 := Function.update regs (2 : Fin 3) false
  let r1 := Function.update r0 (2 : Fin 3) true
  have h0 : Eval (.atom (.set 2 false)) 1 (frameData regs source.reverse output)
      (frameData r0 source.reverse output) := Eval.atom _ _
  have h1 : Eval (.atom (.push 1 2)) 1 (frameData r0 source.reverse output)
      (frameData r0 source.reverse (false :: output)) := by
    convert Eval.atom (Atom.push (1 : Fin 2) (2 : Fin 3)) (frameData r0 source.reverse output) using 1
    all_goals try with_reducible_and_instances rfl
    simp [Atom.eval, Atom.instr, State.ofCfg, execInstr, frameData, r0]
    first | done | (first | done | (funext i; fin_cases i <;> rfl))
  have h2 : Eval (.atom (.set 2 true)) 1 (frameData r0 source.reverse (false :: output))
      (frameData r1 source.reverse (false :: output)) := Eval.atom _ _
  have h3 : Eval (.atom (.pop 0 0 1)) 1 (frameData r1 source.reverse (false :: output))
      (frameReady r1 source.reverse (false :: output)) := by
    convert Eval.atom (Atom.pop (0 : Fin 2) (0 : Fin 3) 1) (frameData r1 source.reverse (false :: output)) using 1
    all_goals try with_reducible_and_instances rfl
    cases source.reverse <;>
      simp [Atom.eval, Atom.instr, State.ofCfg, execInstr, frameData, frameReady] ;
      (first | done | (funext i; fin_cases i <;> rfl))
  obtain ⟨final, _, hf⟩ := frameLoop_eval source.reverse (false :: output) r1 (by simp [r1])
  rw [emitPairs_frame] at hf
  refine ⟨final, ?_⟩
  have hh := h0.seq (h1.seq (h2.seq (h3.seq hf)))
  convert hh using 1 ; simp [] ; omega

theorem frameEmit_trace (source output : List Bool) (regs : Fin 3 → Bool) :
    ∃ final, Trace frameEmitProgram (4 * source.length + 6)
      ((frameData regs source.reverse output).withPC (some frameEmitProgram.entry))
      ((frameData final [] (Encoding.frame source ++ output)).withPC none) := by
  obtain ⟨final,hf⟩ := frameEmit_eval source output regs
  refine ⟨final, ?_⟩
  simpa [frameEmitProgram, Nat.add_assoc] using compiled_halt_trace hf 0 1
end SubexponentialSAT.SqrtLog.Squarefree.Program

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_SquarefreeSparse
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Computable normalized sparse coefficient lists. Zero coefficients may stay
in the list; keys are unique, so this does not enlarge the finite index bound.
No equality decision for coefficients or full ambient Boolean table is used. -/

namespace SubexponentialSAT.SqrtLog.Squarefree.Sparse

open scoped BigOperators

variable {K R A : Type*} [DecidableEq K] [AddCommMonoid R]

omit [AddCommMonoid R] in
theorem length_le_card (l : Data K R) (s : Finset K) (hn : (keys l).Nodup)
    (hs : ∀ k ∈ keys l, k ∈ s) : l.length ≤ s.card := by
  have hsub : (keys l).toFinset ⊆ s := by
    intro k hk
    exact hs k (List.mem_toFinset.mp hk)
  have hcard := Finset.card_le_card hsub
  rw [List.toFinset_card_of_nodup hn] at hcard
  simpa only [keys, List.length_map] using hcard

end SubexponentialSAT.SqrtLog.Squarefree.Sparse

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_SquarefreeProgramRead
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A native two-frame reader for the 28-stack dictionary normalization ABI.
All ports outside 16,17,18,27 and registers outside 0,1 are preserved. -/
namespace SubexponentialSAT.SqrtLog.Squarefree.Program
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

theorem frameReadRegs_injective : Function.Injective frameReadRegs := Fin.castAdd_injective _ _
theorem frameReadPorts_injective {s : ℕ} (src dst : Fin s) (h : src ≠ dst) :
    Function.Injective (frameReadPorts src dst) := by
  intro a b hab
  fin_cases a <;> fin_cases b <;> simp_all [frameReadPorts, ParserProgram.pair]

theorem readFrame8_eval {s : ℕ} (d : State 8 s) (src dst : Fin s) (hsd : src ≠ dst)
    (bits : List Bool) (rest : List Bool) (hin : d.stacks src = Encoding.frame bits ++ rest) :
    Eval (readFrame8 src dst) (6 * bits.length + 4) d (afterFrame8 d src dst bits rest) := by
  let a : State 2 2 := ⟨ParserProgram.pair (d.regs 0) (d.regs 1),
    ParserProgram.pair (Encoding.frame bits ++ rest) (d.stacks dst)⟩
  let b : State 2 2 := ⟨ParserProgram.pair false true,
    ParserProgram.pair rest (bits.reverse ++ d.stacks dst)⟩
  have ha : embedState frameReadRegs (frameReadPorts src dst) d a = d := by
    apply embedState_eq_of_ports _ _ _ _ _ frameReadRegs_injective (frameReadPorts_injective src dst hsd)
    · intro i; fin_cases i <;> rfl
    · intros; rfl
    · intro i; fin_cases i
      · exact hin
      · rfl
    · intros; rfl
  have hb : embedState frameReadRegs (frameReadPorts src dst) d b = afterFrame8 d src dst bits rest := by
    apply embedState_eq_of_ports _ _ _ _ _ frameReadRegs_injective (frameReadPorts_injective src dst hsd)
    · intro i; fin_cases i <;> simp [afterFrame8, frameReadRegs, readRegs, b, ParserProgram.pair]
    · intro j hj
      have h0 : j ≠ 0 := fun h => hj ⟨0, by simpa [frameReadRegs] using h.symm⟩
      have h1 : j ≠ 1 := fun h => hj ⟨1, by simpa [frameReadRegs] using h.symm⟩
      simp [afterFrame8, readRegs, h0, h1]
    · intro i; fin_cases i <;> simp [afterFrame8, frameReadPorts, ParserProgram.pair, b, hsd]
    · intro j hj
      have hsrc : j ≠ src := fun h => hj ⟨0, by simpa [frameReadPorts] using h.symm⟩
      have hdst : j ≠ dst := fun h => hj ⟨1, by simpa [frameReadPorts] using h.symm⟩
      simp [afterFrame8, hsrc, hdst]
  have ht : Trace ParserProgram.frameProgram (6 * bits.length + 4)
      (a.withPC (some ParserProgram.frameProgram.entry)) (b.withPC none) :=
    ParserProgram.frame_trace bits rest (d.stacks dst) (d.regs 0) (d.regs 1)
  have h := eval_call_lifted ParserProgram.frameProgram frameReadRegs
    (frameReadPorts src dst) d frameReadRegs_injective (frameReadPorts_injective src dst hsd) ht
  simpa only [ha,hb,readFrame8] using h

theorem transfer8_eval {s : ℕ} (d : State 8 s) (src dst : Fin s) (hsd : src ≠ dst) :
    Eval (transfer8 src dst) (3*(d.stacks src).length+3) d (afterTransfer8 d src dst) := by
  apply Eval.call
  have h := StackRoutines.transferProgram_trace src dst (0 : Fin 8) 1 hsd (by decide) d.regs d.stacks
  have hh := StackRoutines.halt_after_trace _ h 3 rfl rfl
  simpa [afterTransfer8,StackRoutines.transferResult,StructuredProgram.State.withPC,
    StackRoutines.transferProgram,Nat.add_assoc] using hh

end SubexponentialSAT.SqrtLog.Squarefree.Program

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_MomentsProgramNormalize
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms



namespace SubexponentialSAT.SqrtLog.MomentsProgram.Dictionary
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

variable {K C R A : Type*} [DecidableEq K] [CommRing R] [AddCommMonoid A]

omit [DecidableEq K] [CommRing R] in
theorem denoteTable_keys (f : C → R) (entries : List (K × C)) :
    Squarefree.Sparse.keys (denoteTable f entries) = Squarefree.Sparse.keys entries := by
  simp [denoteTable,Squarefree.Sparse.keys,List.map_map,Function.comp_def]

end SubexponentialSAT.SqrtLog.MomentsProgram.Dictionary


namespace SubexponentialSAT.SqrtLog.MomentsProgram.Dictionary

 theorem rawEntries_length_le (entries : List (List Bool × List Bool)) (W C : ℕ)
    (hk : ∀ a ∈ entries, a.1.length ≤ W) (hc : ∀ a ∈ entries, a.2.length ≤ C) :
    (Squarefree.Program.rawEntries entries).length ≤ entries.length * (2*W+2*C+2) := by
  induction entries with
  | nil => simp [Squarefree.Program.rawEntries]
  | cons a entries ih =>
    have h1 := hk a (by simp)
    have h2 := hc a (by simp)
    have h3 := ih (fun b hb => hk b (by simp [hb])) (fun b hb => hc b (by simp [hb]))
    simp only [Squarefree.Program.rawEntries,List.length_append,Encoding.length_frame,List.length_cons]
    nlinarith

end SubexponentialSAT.SqrtLog.MomentsProgram.Dictionary

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_SquarefreeIndexEncoding
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A self-delimiting encoding of sparse keys: two unary numeric fields,
followed by exactly n support bits. The encoding works without precision
assumptions; the precision assumptions only bound its length. -/

namespace SubexponentialSAT.SqrtLog.Squarefree

theorem encodeIndex_length_le {n t J : ℕ} (a : Index (Fin n))
    (h : a.Kept t J) : (encodeIndex a).length ≤ t + J + n := by
  rw [encodeIndex_length]
  obtain ⟨hu, hz⟩ := h
  omega

end SubexponentialSAT.SqrtLog.Squarefree

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_SquarefreeSparseBounds
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.Squarefree

open scoped BigOperators

namespace Sparse

variable {V R : Type*} [DecidableEq V] [CommSemiring R]

theorem mem_indexUniverse (vars : Finset V) (t J : ℕ) (a : Index V) :
    a ∈ indexUniverse vars t J ↔ a.Kept t J ∧ a.vars ⊆ vars ∧ a.vars.card < J := by
  rcases a with ⟨u, z, s⟩
  simp [indexUniverse, supportUniverse, Index.Kept, Finset.mem_image]

theorem indexUniverse_card_le (vars : Finset V) (t J : ℕ) :
    (indexUniverse vars t J).card ≤ t * J * (supportUniverse vars J).card := by
  exact (Finset.card_image_le).trans (by simp)

omit [CommSemiring R] in
theorem ValidData.in_universe {vars : Finset V} {t J : ℕ} {l : Data (Index V) R}
    (h : ValidData vars t J l) : ∀ a ∈ keys l, a ∈ indexUniverse vars t J := by
  intro a ha
  rcases h a ha with ⟨hk, hv, hs⟩
  exact (mem_indexUniverse vars t J a).mpr ⟨hk, hs, hv.trans_lt hk.2⟩

omit [CommSemiring R] in
theorem ValidData.length_le {vars : Finset V} {t J : ℕ} {l : Data (Index V) R}
    (h : ValidData vars t J l) (hn : (keys l).Nodup) :
    l.length ≤ t * J * (supportUniverse vars J).card :=
  (length_le_card l _ hn h.in_universe).trans (indexUniverse_card_le vars t J)

end Sparse
end SubexponentialSAT.SqrtLog.Squarefree

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_SquarefreeScaleProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Base stage. -/
/-! Fixed physical ABI for scaling all coefficients in a sparse dictionary.
The low 32 stacks are the common coefficient-ring service. The eight high
stacks hold source, reversed output, scalar, key, coefficient staging, frame
staging, final output, and a preserved copy of the unary degree. -/

namespace SubexponentialSAT.SqrtLog.Squarefree.ScaleProgram

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.StackRoutines

theorem nativePorts_injective : Function.Injective nativePorts :=
  Fin.castAdd_injective _ _

theorem embed_native (regs rr : Fin 8 → Bool) (s : Store) (native : RingScan.ServiceStore) :
    embedState id nativePorts (state regs s) (RingScan.serviceWorkState rr native) =
      state rr {s with native := native} := by
  apply embedState_eq_of_ports _ _ _ _ _ Function.injective_id nativePorts_injective
  · intros; rfl
  · intro i hi; exact False.elim (hi ⟨i, rfl⟩)
  · intro i; fin_cases i <;>
      simp [state, tapes, nativePorts, RingScan.serviceWorkState, RingScan.serviceTapes]
  · intro i hi
    apply Fin.addCases (m := 32) (n := 8) (motive := fun i =>
      i ∉ Set.range nativePorts → (state rr {s with native := native}).stacks i =
        (state regs s).stacks i) ?_ ?_ i hi
    · intro j hj; exact False.elim (hj ⟨j, rfl⟩)
    · intro j _; fin_cases j <;> simp [state, tapes]

theorem copy_eval (d : Data) (src dst : Fin 40)
    (hsd : src ≠ dst) (hst : src ≠ 31) (htd : (31 : Fin 40) ≠ dst)
    (htmp : d.stacks 31 = []) :
    Eval (copy src dst) (7 * (d.stacks src).length + 5) d (copied d src dst) := by
  exact .call _ (ListRegisterProgram.copy_run src dst 31 0 1
    hsd hst htd (by decide) d.regs d.stacks htmp)

theorem peek_eval (d : Data) : Eval peek 1 d (peeked d) :=
  .base (.atom _ _)

theorem frameRegs_injective : Function.Injective frameRegs := Fin.castAdd_injective _ _

theorem framePorts_injective (src : Fin 40) (h : src ≠ 37) :
    Function.Injective (framePorts src) := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all [framePorts]

theorem emitFrame_eval (d : Data) (src : Fin 40) (h : src ≠ 37)
    (bits : List Bool) (hs : d.stacks src = bits.reverse) :
    ∃ rr, Eval (emitFrame src) (4 * bits.length + 6) d
      ⟨rr, Function.update (Function.update d.stacks src []) 37
        (Encoding.frame bits ++ d.stacks 37)⟩ := by
  obtain ⟨rf, ht⟩ := Program.frameEmit_trace bits (d.stacks 37) (d.regs ∘ frameRegs)
  let b := Program.frameData rf [] (Encoding.frame bits ++ d.stacks 37)
  let final := embedState frameRegs (framePorts src) d b
  have ha : embedState frameRegs (framePorts src) d
      (Program.frameData (d.regs ∘ frameRegs) bits.reverse (d.stacks 37)) = d := by
    apply embedState_eq_of_ports _ _ _ _ _ frameRegs_injective (framePorts_injective src h)
    · intros; rfl
    · intros; rfl
    · intro i; fin_cases i <;> simp [framePorts, Program.frameData, hs]
    · intros; rfl
  have hb : final =
      (⟨final.regs, Function.update (Function.update d.stacks src []) 37
        (Encoding.frame bits ++ d.stacks 37)⟩ : Data) := by
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · funext i
      by_cases hi37 : i = 37
      · subst i
        have hh := embedState_stack frameRegs (framePorts src) d b (framePorts_injective src h) 1
        simp only [Function.update_self]
        calc
          final.stacks 37 = b.stacks 1 := by
            rw [← show framePorts src (1 : Fin 2) = 37 by rfl]
            exact hh
          _ = Encoding.frame bits ++ d.stacks 37 := by rfl
      · by_cases his : i = src
        · subst i
          have hh := embedState_stack frameRegs (framePorts src) d b (framePorts_injective src h) 0
          simp only [Function.update_of_ne h, Function.update_self]
          calc
            final.stacks src = b.stacks 0 := by
              rw [← show framePorts src (0 : Fin 2) = src by rfl]
              exact hh
            _ = [] := by rfl
        · have hh := embedState_stack_frame frameRegs (framePorts src) d b i (by
            rintro ⟨j, hj⟩; fin_cases j <;> simp_all [framePorts])
          simp only [Function.update_of_ne hi37, Function.update_of_ne his]
          exact hh
  have he := eval_call_lifted Program.frameEmitProgram frameRegs (framePorts src) d
    frameRegs_injective (framePorts_injective src h) ht
  rw [ha] at he
  change Eval (emitFrame src) _ d final at he
  rw [hb] at he
  exact ⟨final.regs, he⟩

end SubexponentialSAT.SqrtLog.Squarefree.ScaleProgram

/-! Moves stage. -/
namespace SubexponentialSAT.SqrtLog.Squarefree.ScaleProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.StackRoutines

theorem read_store (regs : Fin 8 → Bool) (a b : Store) (src dst : Fin 40)
    (hsd : src ≠ dst) (bits tail : List Bool)
    (hin : tapes a src = Encoding.frame bits ++ tail)
    (hout : Function.update (Function.update (tapes a) src tail) dst
      (bits.reverse ++ tapes a dst) = tapes b) :
    Eval (Program.readFrame8 src dst) (6*bits.length+4) (state regs a)
      (state (readRegs regs 0 1 (some false)) b) := by
  simpa only [state, Program.afterFrame8, hout] using
    Program.readFrame8_eval (state regs a) src dst hsd bits tail hin

theorem transfer_store (regs : Fin 8 → Bool) (a b : Store) (src dst : Fin 40)
    (hsd : src ≠ dst) (hout : transferStacks src dst (tapes a) = tapes b) :
    Eval (Program.transfer8 src dst) (3*(tapes a src).length+3) (state regs a)
      (state (readRegs regs 0 1 none) b) := by
  simpa only [state, Program.afterTransfer8, hout] using
    Program.transfer8_eval (state regs a) src dst hsd

theorem copy_store (regs : Fin 8 → Bool) (a b : Store) (src dst : Fin 40)
    (hsd : src ≠ dst) (hst : src ≠ 31) (htd : (31 : Fin 40) ≠ dst)
    (hout : copyStacks src dst (tapes a) = tapes b) :
    Eval (copy src dst) (7*(tapes a src).length+5) (state regs a)
      (state (readRegs regs 0 1 none) b) := by
  have hz : (state regs a).stacks 31 = [] := rfl
  simpa only [state, copied, hout] using
    copy_eval (state regs a) src dst hsd hst htd hz

theorem frame_store (regs : Fin 8 → Bool) (a b : Store) (src : Fin 40)
    (hne : src ≠ 37) (bits : List Bool) (hin : tapes a src = bits.reverse)
    (hout : Function.update (Function.update (tapes a) src []) 37
      (Encoding.frame bits ++ tapes a 37) = tapes b) :
    ∃ rr, Eval (emitFrame src) (4*bits.length+6) (state regs a) (state rr b) := by
  obtain ⟨rr, he⟩ := emitFrame_eval (state regs a) src hne bits hin
  exact ⟨rr, by simpa only [state, hout] using he⟩

theorem prepare_eval (regs : Fin 8 → Bool) (e : Environment)
    (key coeff tail accum : List Bool) :
    ∃ rr, Eval prepare
      (6*key.length+9*coeff.length+7*e.scalar.length+7*e.count.length+21)
      (state regs (idle e (Encoding.frame key ++ Encoding.frame coeff ++ tail) accum))
      (state rr (prepared e key coeff tail accum)) := by
  let a := idle e (Encoding.frame key ++ Encoding.frame coeff ++ tail) accum
  let b := {a with source := Encoding.frame coeff ++ tail, key := key.reverse}
  let c := {b with source := tail, coeff := coeff.reverse}
  let d := {c with coeff := [], native := {nativeIdle e with y := coeff}}
  let f := {d with native := {nativeIdle e with x := e.scalar, y := coeff}}
  let g := prepared e key coeff tail accum
  have h1 := read_store regs a b 32 35 (by decide) key (Encoding.frame coeff ++ tail)
    (by simp [a, idle, tapes, List.append_assoc])
    (by funext i; fin_cases i <;> simp [a,b,idle,tapes])
  have h2 := read_store (readRegs regs 0 1 (some false)) b c 32 36 (by decide) coeff tail
    (by rfl)
    (by funext i; fin_cases i <;> simp [b,c,a,idle,tapes])
  have h3 := transfer_store (readRegs (readRegs regs 0 1 (some false)) 0 1 (some false))
    c d 36 9 (by decide)
    (by funext i; fin_cases i <;>
      simp [a,b,c,d,idle,nativeIdle,tapes,transferStacks])
  let r3 := readRegs (readRegs (readRegs regs 0 1 (some false)) 0 1 (some false)) 0 1 none
  have h4 := copy_store r3 d f 34 8 (by decide) (by decide) (by decide)
    (by funext i; fin_cases i <;>
      simp [a,b,c,d,f,idle,nativeIdle,tapes,copyStacks])
  have h5 := copy_store (readRegs r3 0 1 none) f g 39 11 (by decide) (by decide) (by decide)
    (by funext i; fin_cases i <;>
      simp [a,b,c,d,f,g,prepared,idle,nativeIdle,tapes,copyStacks])
  refine ⟨readRegs (readRegs r3 0 1 none) 0 1 none, ?_⟩
  have he := h1.seq (h2.seq (h3.seq (h4.seq h5)))
  convert he using 1 ;
    simp [a,b,c,d,f,idle,tapes] ; omega

end SubexponentialSAT.SqrtLog.Squarefree.ScaleProgram

/-! Emit stage. -/
namespace SubexponentialSAT.SqrtLog.Squarefree.ScaleProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.StackRoutines

theorem emit_eval (regs : Fin 8 → Bool) (e : Environment)
    (key result tail accum : List Bool) :
    ∃ rr, Eval emit (10*key.length+13*result.length+27)
      (state regs (productReady e key result tail accum))
      (state rr (idle e tail ((Encoding.frame key ++ Encoding.frame result).reverse ++ accum))) := by
  let a := productReady e key result tail accum
  let b := {idle e tail accum with key := key.reverse, coeff := result.reverse}
  let c := {idle e tail accum with coeff := result.reverse, frame := Encoding.frame key}
  let d := {idle e tail ((Encoding.frame key).reverse ++ accum) with coeff := result.reverse}
  let f := {idle e tail ((Encoding.frame key).reverse ++ accum) with frame := Encoding.frame result}
  let g := idle e tail ((Encoding.frame key ++ Encoding.frame result).reverse ++ accum)
  have h1 := transfer_store regs a b 0 36 (by decide)
    (by funext i; fin_cases i <;>
      simp [a,b,productReady,idle,nativeIdle,tapes,transferStacks])
  obtain ⟨r1,h2⟩ := frame_store (readRegs regs 0 1 none) b c 35 (by decide) key rfl
    (by funext i; fin_cases i <;>
      simp [b,c,idle,nativeIdle,tapes])
  have h3 := transfer_store r1 c d 37 33 (by decide)
    (by funext i; fin_cases i <;>
      simp [c,d,idle,nativeIdle,tapes,transferStacks])
  obtain ⟨r2,h4⟩ := frame_store (readRegs r1 0 1 none) d f 36 (by decide) result rfl
    (by funext i; fin_cases i <;>
      simp [d,f,idle,nativeIdle,tapes])
  have h5 := transfer_store r2 f g 37 33 (by decide)
    (by funext i; fin_cases i <;>
      simp [f,g,idle,nativeIdle,tapes,transferStacks,
        List.reverse_append,List.append_assoc])
  refine ⟨readRegs r2 0 1 none, ?_⟩
  have he := h1.seq (h2.seq (h3.seq (h4.seq h5)))
  convert he using 1 ;
    simp [a,c,f,productReady,idle,nativeIdle,tapes] ; omega

theorem finish_eval (regs : Fin 8 → Bool) (e : Environment) (output : List Bool) :
    Eval finish (3*output.length+3)
      (state regs (idle e [] output.reverse))
      (state (readRegs regs 0 1 none) {idle e [] [] with output := output}) := by
  have he := transfer_store regs (idle e [] output.reverse)
    {idle e [] [] with output := output} 33 38 (by decide)
    (by funext i; fin_cases i <;>
      simp [idle,nativeIdle,tapes,transferStacks])
  simpa [finish,idle,tapes,Fin.addCases] using he

end SubexponentialSAT.SqrtLog.Squarefree.ScaleProgram

/-! Native stage. -/
namespace SubexponentialSAT.SqrtLog.Squarefree.ScaleProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

theorem multiply_eval (p t : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p t)
    (cache : RingProgram.ScalarCache p t) (hz : BinaryArithmetic.toNat cache.zero.val < p^t)
    {d : ℕ} (table : Fin d → Fin d → Fin d → Word (baseWidth p t))
    (scalar x : RingProgram.Code (Word (baseWidth p t)) d)
    (degree width : List Bool) (hd : degree.length = d) (hw : width.length = baseWidth p t)
    (regs : Fin 8 → Bool) (key tail accum : List Bool) :
    ∃ n ≤ RingScan.serviceMulBudget (baseWidth p t) d + 1, ∃ rr,
      Eval multiply n
        (state regs (prepared (environment p t M cache table scalar degree width)
          key (RingProgram.flat x) tail accum))
        (state rr (productReady (environment p t M cache table scalar degree width)
          key (RingProgram.flat (valueMul p t M cache table scalar x)) tail accum)) := by
  obtain ⟨n,hn,rr,he⟩ := RingScan.serviceMul_eval p t M cache hz table scalar x regs degree width hd hw
  let start := prepared (environment p t M cache table scalar degree width)
    key (RingProgram.flat x) tail accum
  have hh := eval_call_lifted RingScan.serviceMulProgram id nativePorts (state regs start)
    Function.injective_id nativePorts_injective (compiled_halt_trace he 8 0)
  refine ⟨n+1, Nat.add_le_add_right hn 1, rr, ?_⟩
  simpa only [multiply, RingScan.serviceState, embed_native, start, prepared,
    productReady, environment, idle, nativeIdle, valueMul] using hh

theorem step_eval (p t : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p t)
    (cache : RingProgram.ScalarCache p t) (hz : BinaryArithmetic.toNat cache.zero.val < p^t)
    {d : ℕ} (table : Fin d → Fin d → Fin d → Word (baseWidth p t))
    (scalar x : RingProgram.Code (Word (baseWidth p t)) d)
    (degree width : List Bool) (hd : degree.length = d) (hw : width.length = baseWidth p t)
    (regs : Fin 8 → Bool) (key tail accum : List Bool) :
    ∃ n ≤ stepBudget (baseWidth p t) d key.length, ∃ rr,
      Eval step n
        (state regs (idle (environment p t M cache table scalar degree width)
          (Encoding.frame key ++ Encoding.frame (RingProgram.flat x) ++ tail) accum))
        (state rr (idle (environment p t M cache table scalar degree width) tail
          ((Encoding.frame key ++ Encoding.frame
            (RingProgram.flat (valueMul p t M cache table scalar x))).reverse ++ accum))) := by
  let e := environment p t M cache table scalar degree width
  obtain ⟨r1,h1⟩ := prepare_eval regs e key (RingProgram.flat x) tail accum
  obtain ⟨n,hn,r2,h2⟩ := multiply_eval p t M cache hz table scalar x degree width hd hw r1 key tail accum
  obtain ⟨r3,h3⟩ := emit_eval r2 e key
    (RingProgram.flat (valueMul p t M cache table scalar x)) tail accum
  refine ⟨_, ?_, r3, h1.seq (h2.seq h3)⟩
  simp only [RingProgram.flat_length]
  dsimp only [e,environment]
  simp only [RingProgram.flat_length]
  rw [hd]
  unfold stepBudget
  omega

end SubexponentialSAT.SqrtLog.Squarefree.ScaleProgram

/-! Loop stage. -/
namespace SubexponentialSAT.SqrtLog.Squarefree.ScaleProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

variable {K : Type*}

theorem scaled_keys (p t : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p t)
    (cache : RingProgram.ScalarCache p t) {d : ℕ}
    (table : Fin d → Fin d → Fin d → Word (baseWidth p t))
    (scalar : RingProgram.Code (Word (baseWidth p t)) d) (entries) :
    (scaled (K := K) p t M cache table scalar entries).map Prod.fst = entries.map Prod.fst := by
  simp [scaled, List.map_map, Function.comp_def]

theorem loop_eval (p t : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p t)
    (cache : RingProgram.ScalarCache p t) (hz : BinaryArithmetic.toNat cache.zero.val < p^t)
    {d : ℕ} (table : Fin d → Fin d → Fin d → Word (baseWidth p t))
    (scalar : RingProgram.Code (Word (baseWidth p t)) d)
    (degree width : List Bool) (hd : degree.length = d) (hw : width.length = baseWidth p t)
    (key : K → List Bool) (entries) (regs : Fin 8 → Bool) (accum : List Bool) :
    ∃ n ≤ loopBudget key entries, ∃ rr,
      Eval loop n
        (peeked (state regs (idle (environment p t M cache table scalar degree width)
          (encode key entries) accum)))
        (state rr (idle (environment p t M cache table scalar degree width) []
          ((encode key (scaled p t M cache table scalar entries)).reverse ++ accum))) := by
  induction entries generalizing regs accum with
  | nil =>
      refine ⟨1, le_rfl, readRegs regs 0 7 none, ?_⟩
      have hh : (peeked (state regs (idle (environment p t M cache table scalar degree width)
          (encode (B := baseWidth p t) (d := d) key []) accum))).regs 7 = false := by
        simp [peeked,state,idle,tapes,readRegs]
      simpa [scaled,encode,Program.encodeDictionary,Program.rawEntries,
        peeked,state,idle,tapes,Fin.addCases] using (Eval.while_false (body := .seq step peek) hh)
  | cons a entries ih =>
      let e := environment p t M cache table scalar degree width
      let input := encode key (a :: entries)
      let recordBits := Encoding.frame (key a.1) ++
        Encoding.frame (RingProgram.flat (valueMul p t M cache table scalar a.2))
      let r0 := readRegs regs 0 7 input.head?
      obtain ⟨n,hn,r1,h1⟩ := step_eval p t M cache hz table scalar a.2 degree width hd hw r0
        (key a.1) (encode key entries) accum
      have hpeek := peek_eval (state r1 (idle e (encode key entries) (recordBits.reverse ++ accum)))
      obtain ⟨m,hm,r2,h2⟩ := ih r1 (recordBits.reverse ++ accum)
      have hflag : (peeked (state regs (idle e input accum))).regs 7 = true := by
        cases hk : key a.1 <;>
          simp [peeked,state,idle,tapes,input,encode_cons,Encoding.frame,hk,readRegs]
      have hstep : Eval step n (peeked (state regs (idle e input accum)))
          (state r1 (idle e (encode key entries) (recordBits.reverse ++ accum))) := by
        simpa [e, recordBits, peeked, state, idle, tapes, Fin.addCases, input, encode_cons, r0] using h1
      have hh := Eval.while_true hflag (hstep.seq hpeek) h2
      refine ⟨n+1+m+1, ?_, r2, ?_⟩
      · simp only [loopBudget]
        omega
      · simpa only [loop, scaled, List.map_cons, encode_cons, List.reverse_append,
          List.append_assoc, e, recordBits, input] using hh

theorem encode_scaled_length (p t : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p t)
    (cache : RingProgram.ScalarCache p t) {d : ℕ}
    (table : Fin d → Fin d → Fin d → Word (baseWidth p t))
    (scalar : RingProgram.Code (Word (baseWidth p t)) d) (key : K → List Bool) (entries) :
    (encode key (scaled p t M cache table scalar entries)).length = (encode key entries).length := by
  induction entries with
  | nil => rfl
  | cons a entries ih =>
      simp only [scaled,List.map_cons,encode_cons,List.length_append,Encoding.length_frame,
        RingProgram.flat_length]
      simpa only [scaled] using congrArg (fun n => (2*(key a.1).length+1)+(2*(d*baseWidth p t)+1)+n) ih

theorem command_eval (p t : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p t)
    (cache : RingProgram.ScalarCache p t) (hz : BinaryArithmetic.toNat cache.zero.val < p^t)
    {d : ℕ} (table : Fin d → Fin d → Fin d → Word (baseWidth p t))
    (scalar : RingProgram.Code (Word (baseWidth p t)) d)
    (degree width : List Bool) (hd : degree.length = d) (hw : width.length = baseWidth p t)
    (key : K → List Bool) (entries) (regs : Fin 8 → Bool) :
    ∃ n ≤ budget key entries, ∃ rr,
      Eval command n
        (state regs (idle (environment p t M cache table scalar degree width) (encode key entries) []))
        (state rr {idle (environment p t M cache table scalar degree width) [] [] with
          output := encode key (scaled p t M cache table scalar entries)}) := by
  let e := environment p t M cache table scalar degree width
  have h1 := peek_eval (state regs (idle e (encode key entries) []))
  obtain ⟨n,hn,r1,h2⟩ := loop_eval p t M cache hz table scalar degree width hd hw key entries regs []
  simp only [List.append_nil] at h2
  have h3 := finish_eval r1 e (encode key (scaled p t M cache table scalar entries))
  refine ⟨_, ?_, _, h1.seq (h2.seq h3)⟩
  rw [encode_scaled_length]
  dsimp only [budget]
  omega

theorem program_runsIn (p t : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p t)
    (cache : RingProgram.ScalarCache p t) (hz : BinaryArithmetic.toNat cache.zero.val < p^t)
    {d : ℕ} (table : Fin d → Fin d → Fin d → Word (baseWidth p t))
    (scalar : RingProgram.Code (Word (baseWidth p t)) d)
    (degree width : List Bool) (hd : degree.length = d) (hw : width.length = baseWidth p t)
    (key : K → List Bool) (entries) (regs : Fin 8 → Bool) :
    ∃ rr, RunsIn program (budget key entries + 1)
      ((state regs (idle (environment p t M cache table scalar degree width) (encode key entries) [])).withPC
        (some program.entry))
      ((state rr {idle (environment p t M cache table scalar degree width) [] [] with
        output := encode key (scaled p t M cache table scalar entries)}).withPC none) := by
  obtain ⟨n,hn,rr,he⟩ := command_eval p t M cache hz table scalar degree width hd hw key entries regs
  exact ⟨rr,n+1,Nat.add_le_add_right hn 1,compiled_halt_trace he 32 38⟩

end SubexponentialSAT.SqrtLog.Squarefree.ScaleProgram

/-! Cost stage. -/
namespace SubexponentialSAT.SqrtLog.Squarefree.ScaleProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

variable {K : Type*}

theorem encode_length {B d : ℕ} (key : K → List Bool)
    (entries : List (K × RingProgram.Code (Word B) d)) :
    (encode key entries).length = 2*keyBits key entries + entries.length*(2*(d*B)+2) := by
  induction entries with
  | nil => simp [encode,keyBits,Program.rawEntries,Program.encodeDictionary]
  | cons a entries ih =>
      simp only [encode_cons,List.length_append,Encoding.length_frame,RingProgram.flat_length,
        ih,keyBits,List.length_cons]
      ring

theorem loopBudget_eq {B d : ℕ} (key : K → List Bool)
    (entries : List (K × RingProgram.Code (Word B) d)) :
    loopBudget key entries = entries.length*(RingScan.serviceMulBudget B d+29*(d*B)+7*d+51) +
      16*keyBits key entries+1 := by
  induction entries with
  | nil => simp [loopBudget,keyBits]
  | cons a entries ih => simp only [loopBudget,stepBudget,ih,keyBits,List.length_cons]; ring

theorem budget_eq {B d : ℕ} (key : K → List Bool)
    (entries : List (K × RingProgram.Code (Word B) d)) :
    budget key entries + 1 =
      entries.length*(RingScan.serviceMulBudget B d+35*(d*B)+7*d+57) +
      22*keyBits key entries+6 := by
  rw [budget,loopBudget_eq,encode_length]
  ring

theorem keyBits_le {C : Type*} (key : K → List Bool) (entries : List (K × C))
    (L : ℕ) (h : ∀ a ∈ entries, (key a.1).length ≤ L) :
    keyBits key entries ≤ entries.length*L := by
  induction entries with
  | nil => simp [keyBits]
  | cons a entries ih =>
      have ha := h a (by simp)
      have ht := ih (fun a ha => h a (by simp [ha]))
      simp only [keyBits,List.length_cons,Nat.add_mul,Nat.one_mul]
      omega

theorem budget_le {B d : ℕ} (key : K → List Bool)
    (entries : List (K × RingProgram.Code (Word B) d))
    (L : ℕ) (h : ∀ a ∈ entries, (key a.1).length ≤ L) :
    budget key entries + 1 ≤
      entries.length*(40000*(d+1)^3*(B+1)^2+35*(d*B)+7*d+22*L+57)+6 := by
  rw [budget_eq]
  have hk := keyBits_le key entries L h
  have hs := RingScan.serviceMulBudget_le B d
  calc
    _ ≤ entries.length*(40000*(d+1)^3*(B+1)^2+35*(d*B)+7*d+57) +
        22*(entries.length*L)+6 :=
      Nat.add_le_add_right
        (Nat.add_le_add (Nat.mul_le_mul_left _ (by omega)) (Nat.mul_le_mul_left 22 hk)) 6
    _ = _ := by ring

end SubexponentialSAT.SqrtLog.Squarefree.ScaleProgram

/-! Semantics stage. -/
namespace SubexponentialSAT.SqrtLog.Squarefree.ScaleProgram
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing
open scoped BigOperators

variable {K V R : Type*} [DecidableEq V] [CommRing R]

theorem scaled_nodup (p t : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p t)
    (cache : RingProgram.ScalarCache p t) {d : ℕ}
    (table : Fin d → Fin d → Fin d → Word (baseWidth p t))
    (constant : RingProgram.Code (Word (baseWidth p t)) d) (entries)
    (h : (entries.map Prod.fst).Nodup) :
    ((scaled (K := K) p t M cache table constant entries).map Prod.fst).Nodup := by
  rwa [scaled_keys]

end SubexponentialSAT.SqrtLog.Squarefree.ScaleProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_MomentsProgramProductBounds
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.MomentsProgram.Product
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

theorem bytes_length_le {n B d : ℕ} (entries : List (Entry n B d)) (W : ℕ)
    (h : Normalize.KeyBound Squarefree.encodeIndex W entries) :
    (bytes entries).length ≤ entries.length*(2*W+2*(d*B)+2) := by
  have hh := Dictionary.rawEntries_length_le
    (Squarefree.Program.encodeDictionary Squarefree.encodeIndex RingProgram.flat entries) W (d*B)
    (by intro a ha; obtain ⟨b,hb,rfl⟩ := List.mem_map.mp ha; exact h b hb)
    (by intro a ha; obtain ⟨b,hb,rfl⟩ := List.mem_map.mp ha; exact le_of_eq (RingProgram.flat_length b.2))
  simpa [bytes,Normalize.bytes,Squarefree.Program.encodeDictionary] using hh

end SubexponentialSAT.SqrtLog.MomentsProgram.Product

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_MomentsProgramValidity
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.MomentsProgram
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

namespace Product

theorem decoded_valid {R : Type*} [CommRing R] {n B d : ℕ}
    (f : RingProgram.Code (Word B) d → R) (vars : Finset (Fin n)) (u J : ℕ)
    (entries : List (Entry n B d)) (h : ∀ a ∈ entries, ValidKey vars u J a.1) :
    Squarefree.Sparse.ValidData vars u J (Dictionary.denoteTable f entries) := by
  intro k hk
  simp only [Squarefree.Sparse.keys,Dictionary.denoteTable,List.map_map,Function.comp_def] at hk
  obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hk
  exact h a ha

end Product
end SubexponentialSAT.SqrtLog.MomentsProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_TruncatedRingProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Native arithmetic after immediate Boolean specialization

The existing finite sparse-product program is used with empty formal support.
Its keys still carry the ambient input coordinate type; this does not compress
the declared variables. There are at most `u * J` retained entries, including
zero cutoffs. Polynomial local time therefore bounds all its source prefixes,
including the table, inputs, output, normalization copies and arithmetic scratch.
-/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.TruncatedRingProgram

open scoped BigOperators
open OAI OAI.Algorithms.SubexponentialSAT.SqrtLog OAI.Algorithms.SubexponentialSAT.SubexpLiftRing OAI.Algorithms.SubexponentialSAT.SubexpQuarticRing
open MomentsProgram BitProgram

/- The two fields coincide with LeafProgram.NativeSemantics.Good. The
arithmetic layer states them transparently to avoid importing the factor
interpreter. Conversion in either direction supplies `valid` and `nodup`.
The proof bodies below are the original finite-program validity arguments. -/
section NativeValidity

namespace Good

variable {n B d u J : ℕ} {vars : Finset (Fin n)}

theorem decoded_valid {R : Type*} [CommRing R]
    {a : List (Product.Entry n B d)} (h : Good vars u J a)
    (f : RingProgram.Code (Word B) d → R) :
    Squarefree.Sparse.ValidData vars u J (Dictionary.denoteTable f a) :=
  Product.decoded_valid f vars u J a h.valid

theorem length_le {a : List (Product.Entry n B d)} (h : Good vars u J a) :
    a.length ≤ u*J*(Squarefree.Sparse.supportUniverse vars J).card := by
  have hv := h.decoded_valid (fun _ => (0 : ℤ))
  have hn : (Squarefree.Sparse.keys (Dictionary.denoteTable (fun _ => (0 : ℤ)) a)).Nodup := by
    simpa only [Dictionary.denoteTable_keys] using h.nodup
  simpa only [Dictionary.denoteTable,List.length_map] using hv.length_le hn

end Good

variable (p t : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p t)
variable (cache : RingProgram.ScalarCache p t) {n d : ℕ}
variable (table : Fin d → Fin d → Fin d → Word (baseWidth p t))
variable (vars : Finset (Fin n)) (u J : ℕ)

 theorem scaled_good (c : RingProgram.Code (Word (baseWidth p t)) d)
    (a : List (Product.Entry n (baseWidth p t) d)) (h : Good vars u J a) :
    Good vars u J (Squarefree.ScaleProgram.scaled p t M cache table c a) := by
  constructor
  · intro x hx
    obtain ⟨y,hy,rfl⟩ := List.mem_map.mp hx
    exact h.valid y hy
  · exact Squarefree.ScaleProgram.scaled_nodup p t M cache table c a h.nodup


end NativeValidity

variable {V R : Type*} [DecidableEq V] [CommRing R]

omit [DecidableEq V] in
/-- Empty formal support has at most one possible support, also when `J = 0`. -/
theorem empty_support_card_le (J : ℕ) :
    (Squarefree.Sparse.supportUniverse (∅ : Finset V) J).card ≤ 1 := by
  calc
    _ ≤ ((∅ : Finset V).powerset).card := Finset.card_filter_le _ _
    _ = 1 := by simp

theorem empty_length_le {n B d u J : ℕ} {a : List (Product.Entry n B d)}
    (ha : Good ∅ u J a) : a.length ≤ u * J := by
  exact ha.length_le.trans (by
    simpa only [Nat.mul_one] using Nat.mul_le_mul_left (u * J)
      (empty_support_card_le (V := Fin n) J))

theorem empty_bytes_length_le {n B d u J : ℕ} {a : List (Product.Entry n B d)}
    (ha : Good ∅ u J a) :
    (Product.bytes a).length ≤ u * J * (2 * (u + J + n) + 2 * (d * B) + 2) := by
  exact (Product.bytes_length_le a (u + J + n)
    (fun x hx => Squarefree.encodeIndex_length_le x.1 (ha.valid x hx).1)).trans
      (Nat.mul_le_mul_right _ (empty_length_le ha))

/-- Scalar multiplication also implements signs using the cached negative unit. -/
theorem scaling_run_space (p t : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p t) (cache : RingProgram.ScalarCache p t)
    (hz : BinaryArithmetic.toNat cache.zero.val < p ^ t)
    {n d u J : ℕ} (table : Fin d → Fin d → Fin d → Word (baseWidth p t))
    (c : RingProgram.Code (Word (baseWidth p t)) d)
    (a : List (Product.Entry n (baseWidth p t) d)) (ha : Good ∅ u J a)
    (degree width : List Bool) (hd : degree.length = d) (hw : width.length = baseWidth p t)
    (regs : Fin 8 → Bool) :
    let e := Squarefree.ScaleProgram.environment p t M cache table c degree width
    let start := (Squarefree.ScaleProgram.state regs
      (Squarefree.ScaleProgram.idle e (Product.bytes a) [])).withPC
        (some Squarefree.ScaleProgram.program.entry)
    let result := Squarefree.ScaleProgram.scaled p t M cache table c a
    ∃ steps rr,
      steps ≤ scalingBudget n (baseWidth p t) d u J ∧
      Trace Squarefree.ScaleProgram.program steps start
        ((Squarefree.ScaleProgram.state rr
          {Squarefree.ScaleProgram.idle e [] [] with output := Product.bytes result}).withPC none) ∧
      Good ∅ u J result ∧
      ∀ prefixSteps intermediate, prefixSteps ≤ steps →
        Trace Squarefree.ScaleProgram.program prefixSteps start intermediate →
        ∀ i, (intermediate.stacks i).length ≤
          dataBits start + scalingBudget n (baseWidth p t) d u J := by
  dsimp only
  have hlen := empty_length_le ha
  have hc := Squarefree.ScaleProgram.budget_le Squarefree.encodeIndex a (n + u + J) (by
    intro x hx
    have h := Squarefree.encodeIndex_length_le x.1 (ha.valid x hx).1
    omega)
  have hbudget : Squarefree.ScaleProgram.budget Squarefree.encodeIndex a + 1 ≤
      scalingBudget n (baseWidth p t) d u J := by
    apply hc.trans
    exact Nat.add_le_add_right (Nat.mul_le_mul_right _ hlen) 6
  obtain ⟨rr, steps, hsteps, htrace⟩ := Squarefree.ScaleProgram.program_runsIn p t M cache hz
    table c degree width hd hw Squarefree.encodeIndex a regs
  have hb := hsteps.trans hbudget
  refine ⟨steps, rr, hb, htrace, scaled_good p t M cache table ∅ u J c a ha, ?_⟩
  intro prefixSteps intermediate hprefix hp
  exact StructuredSpace.local_stack_bound Squarefree.ScaleProgram.program le_rfl
    prefixSteps intermediate (hprefix.trans hb) hp

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.TruncatedRingProgram
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_QueryProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Concrete bit primitives for streamed finite-difference queries. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryProgram

open OAI BitProgram
open scoped BigOperators

open StructuredCalls

section SignedArray

attribute [local simp] Fin.coe_ofNat_eq_mod

open OAI.Algorithms.SubexponentialSAT.SqrtLog OAI.Algorithms.SubexponentialSAT.SubexpLiftRing OAI.Algorithms.SubexponentialSAT.SubexpQuarticRing
open MomentsProgram TruncatedRingProgram

theorem scalePorts_injective : Function.Injective scalePorts := Fin.castAdd_injective _ _

theorem embed_signedState (regs rr : Fin 8 → Bool)
    (s t : Squarefree.ScaleProgram.Store) (sign : Bool) :
    embedState id scalePorts (signedState regs s sign) (Squarefree.ScaleProgram.state rr t) =
      signedState rr t sign := by
  apply SubexpScanPrimitives.embedState_eq _ _ Function.injective_id scalePorts_injective
  · intro i; rfl
  · intro i
    simp [signedState, scalePorts, Squarefree.ScaleProgram.state]
  · intro i hi; exact False.elim (hi ⟨i, rfl⟩)
  · intro i hi
    apply Fin.addCases (m := 40) (n := 1) (motive := fun i =>
      (¬ ∃ j, scalePorts j = i) →
        (signedState rr t sign).stacks i = (signedState regs s sign).stacks i) ?_ ?_ i hi
    · intro j hj; exact False.elim (hj ⟨j, rfl⟩)
    · intro j _; simp [signedState]

theorem signed_peek_eval (regs : Fin 8 → Bool) (s : Squarefree.ScaleProgram.Store)
    (sign : Bool) :
    Eval (.base (.atom (.peek 40 6 7))) 1 (signedState regs s sign)
      (signedState (readRegs regs 6 7 (some sign)) s sign) := by
  simpa [signedState, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
    StructuredProgram.State.ofCfg, StructuredProgram.State.withPC, execInstr]
    using (Eval.base (StructuredProgram.Eval.atom (.peek 40 6 7)
      (signedState regs s sign)))

theorem positiveScale_eval (regs : Fin 8 → Bool)
    (e : Squarefree.ScaleProgram.Environment) (bits : List Bool) :
    Eval (.seq (.call (StackRoutines.transferProgram 32 33 0 1))
      (.call (StackRoutines.transferProgram 33 38 0 1))) (6 * bits.length + 6)
      (signedState regs (Squarefree.ScaleProgram.idle e bits []) false)
      (signedState (readRegs (readRegs regs 0 1 none) 0 1 none)
        {Squarefree.ScaleProgram.idle e [] [] with output := bits} false) := by
  let a := signedState regs (Squarefree.ScaleProgram.idle e bits []) false
  let b := SubexpScanPrimitives.afterTransfer a 32 33 0 1
  have h₁ := SubexpScanPrimitives.transfer_eval a 32 33 0 1 (by decide) (by decide)
  have h₂ := SubexpScanPrimitives.transfer_eval b 33 38 0 1 (by decide) (by decide)
  have hb : SubexpScanPrimitives.afterTransfer b 33 38 0 1 =
      signedState (readRegs (readRegs regs 0 1 none) 0 1 none)
        {Squarefree.ScaleProgram.idle e [] [] with output := bits} false := by
    apply SubexpScanPrimitives.state_ext
    · rfl
    · funext i
      have h32 : a.stacks 32 = bits := rfl
      have h33 : a.stacks 33 = [] := rfl
      have h38 : a.stacks 38 = [] := rfl
      simp only [b, SubexpScanPrimitives.afterTransfer, StackRoutines.transferStacks,
        Function.update_apply, h32, h33, h38]
      by_cases hi32 : i = 32
      · subst i; simp [signedState, Squarefree.ScaleProgram.idle, Squarefree.ScaleProgram.tapes]
      by_cases hi33 : i = 33
      · subst i; simp [signedState, Squarefree.ScaleProgram.idle, Squarefree.ScaleProgram.tapes]
      by_cases hi38 : i = 38
      · subst i; simp [signedState, Squarefree.ScaleProgram.idle, Squarefree.ScaleProgram.tapes]
      simp only [hi32, hi33, hi38, ite_false]
      simp only [a, signedState]
      split_ifs with hi
      · simp only [Squarefree.ScaleProgram.tapes, Squarefree.ScaleProgram.idle]
        have hj32 : (⟨i.val, hi⟩ : Fin 40) ≠ 32 := by simpa [Fin.ext_iff] using hi32
        have hj38 : (⟨i.val, hi⟩ : Fin 40) ≠ 38 := by simpa [Fin.ext_iff] using hi38
        simp only [hj32, hj38, ite_false]
      · rfl
  have h := h₁.seq h₂
  rw [hb] at h
  have ha32 : a.stacks 32 = bits := rfl
  have hb33 : b.stacks 33 = bits.reverse := by
    simp [b, SubexpScanPrimitives.afterTransfer, StackRoutines.transferStacks, a,
      signedState, Squarefree.ScaleProgram.idle, Squarefree.ScaleProgram.tapes]
  simpa only [ha32, hb33, List.length_reverse, show
    3 * bits.length + 3 + (3 * bits.length + 3) = 6 * bits.length + 6 by omega] using h

/-- The sign branch executes a fixed native program; readiness consists only
of the concrete scalar-ring data and bounded empty-support input dictionary. -/
theorem signedScale_eval (p t : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p t) (cache : RingProgram.ScalarCache p t)
    (hz : BinaryArithmetic.toNat cache.zero.val < p ^ t)
    {n d u J : ℕ} (table : Fin d → Fin d → Fin d → Word (baseWidth p t))
    (minusOne : RingProgram.Code (Word (baseWidth p t)) d)
    (a : List (Product.Entry n (baseWidth p t) d)) (ha : Good ∅ u J a)
    (degree width : List Bool) (hd : degree.length = d) (hw : width.length = baseWidth p t)
    (regs : Fin 8 → Bool) (sign : Bool) :
    let e := Squarefree.ScaleProgram.environment p t M cache table minusOne degree width
    let result := signedEntries p t M cache table minusOne sign a
    ∃ steps rr, steps + 1 ≤ signedScalingBudget n (baseWidth p t) d u J ∧
      Eval signedScale steps
        (signedState regs (Squarefree.ScaleProgram.idle e (Product.bytes a) []) sign)
        (signedState rr {Squarefree.ScaleProgram.idle e [] [] with
          output := Product.bytes result} sign) ∧ Good ∅ u J result := by
  dsimp only
  let e := Squarefree.ScaleProgram.environment p t M cache table minusOne degree width
  have hp := signed_peek_eval regs (Squarefree.ScaleProgram.idle e (Product.bytes a) []) sign
  cases sign with
  | false =>
    have hh := positiveScale_eval (readRegs regs 6 7 (some false)) e (Product.bytes a)
    have he := hp.seq (Eval.ite_false (test := 6) (yes := .call (ProgramLinking.liftProgram Squarefree.ScaleProgram.program id scalePorts)) (by simp [signedState, readRegs]) hh)
    refine ⟨6 * (Product.bytes a).length + 8, readRegs (readRegs (readRegs regs 6 7 (some false)) 0 1 none) 0 1 none, ?_, ?_, ha⟩
    · have hb := TruncatedRingProgram.empty_bytes_length_le ha
      unfold signedScalingBudget
      omega
    · simpa only [signedScale, signedEntries, Bool.false_eq_true, ite_false, e, show 1 + (6 * (Product.bytes a).length + 6 + 1) = 6 * (Product.bytes a).length + 8 by omega] using he
  | true =>
    obtain ⟨steps, rr, hb, ht, hg, _⟩ := TruncatedRingProgram.scaling_run_space p t M cache hz
      table minusOne a ha degree width hd hw (readRegs regs 6 7 (some true))
    have hh := eval_call_lifted Squarefree.ScaleProgram.program id scalePorts
      (signedState (readRegs regs 6 7 (some true))
        (Squarefree.ScaleProgram.idle e (Product.bytes a) []) true)
      Function.injective_id scalePorts_injective ht
    rw [embed_signedState, embed_signedState] at hh
    have he := hp.seq (Eval.ite_true (test := 6) (no := .seq (.call (StackRoutines.transferProgram 32 33 0 1)) (.call (StackRoutines.transferProgram 33 38 0 1))) (by simp [signedState, readRegs]) hh)
    refine ⟨steps + 2, rr, ?_, ?_, hg⟩
    · unfold signedScalingBudget
      omega
    · simpa only [signedScale, signedEntries, Bool.true_eq, ite_true, if_true, e, Nat.add_assoc,
        Nat.add_comm, Nat.add_left_comm] using he

theorem signedScale_run_space_oai (p t : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p t) (cache : RingProgram.ScalarCache p t)
    (hz : BinaryArithmetic.toNat cache.zero.val < p ^ t)
    {n d u J : ℕ} (table : Fin d → Fin d → Fin d → Word (baseWidth p t))
    (minusOne : RingProgram.Code (Word (baseWidth p t)) d)
    (a : List (Product.Entry n (baseWidth p t) d)) (ha : Good ∅ u J a)
    (degree width : List Bool) (hd : degree.length = d) (hw : width.length = baseWidth p t)
    (regs : Fin 8 → Bool) (sign : Bool) :
    let e := Squarefree.ScaleProgram.environment p t M cache table minusOne degree width
    let start := (signedState regs (Squarefree.ScaleProgram.idle e (Product.bytes a) []) sign).withPC
      (some signedScaleProgram.entry)
    let result := signedEntries p t M cache table minusOne sign a
    ∃ steps rr, steps ≤ signedScalingBudget n (baseWidth p t) d u J ∧
      Trace signedScaleProgram steps start
        ((signedState rr {Squarefree.ScaleProgram.idle e [] [] with
          output := Product.bytes result} sign).withPC none) ∧ Good ∅ u J result ∧
      ∀ prefixSteps intermediate, prefixSteps ≤ steps →
        Trace signedScaleProgram prefixSteps start intermediate →
        ∀ i, (intermediate.stacks i).length ≤
          dataBits start + signedScalingBudget n (baseWidth p t) d u J := by
  dsimp only
  obtain ⟨steps, rr, hb, he, hg⟩ := signedScale_eval p t M cache hz table minusOne a ha
    degree width hd hw regs sign
  have ht := compiled_halt_trace he 32 38
  refine ⟨steps + 1, rr, hb, ht, hg, ?_⟩
  intro prefixSteps intermediate hp htrace
  exact StructuredSpace.local_stack_bound signedScaleProgram le_rfl prefixSteps intermediate
    (hp.trans hb) htrace


end SignedArray

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryProgram
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryProgram.signedScale_run_space_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryProgram.signedScale_run_space_oai
