-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DifferencePairsSpace.program_stack_bound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T03:54:53.901607+00:00
-- url     : https://prove2.me/submissions/8dc073e8-f46f-4161-9780-dd56dcf916b2

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S067
import Definitions.Def_OAIQ081S081
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_StructuredSpace_local_stack_bound

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_ProgramStateFrames
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Reusable data projection and framing for genuine finite subroutine calls.
The projection/embedding functions specify states; executable code uses only
the fixed instruction-port relocation already proved by ProgramLinking. -/

namespace SubexponentialSAT.StructuredCalls

open SubexponentialSAT.BitProgram

/-- Different finite execution derivations of the same structured command
must have the same final data. The existing source port supplies a concrete
compiled machine, and determinism is inherited from its actual transition. -/
theorem Eval.final_unique {r s : ℕ} (port : Fin s) {c : Cmd r s}
    {n m : ℕ} {a b d : State r s} (h : Eval c n a b) (g : Eval c m a d) : b = d := by
  have hb := compiled_halt_trace h port port
  have hd := compiled_halt_trace g port port
  have heq := Computation.RunsIn.terminal_unique
    (show RunsIn (compiled c port port) (n + 1)
      (a.withPC (some (compiled c port port).entry)) (b.withPC none) from
      ⟨n + 1, le_rfl, hb⟩)
    (show RunsIn (compiled c port port) (m + 1)
      (a.withPC (some (compiled c port port).entry)) (d.withPC none) from
      ⟨m + 1, le_rfl, hd⟩)
    (by simp [step, StructuredProgram.State.withPC])
    (by simp [step, StructuredProgram.State.withPC])
  exact congrArg StructuredProgram.State.ofCfg heq

end SubexponentialSAT.StructuredCalls

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_DifferencePairsProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Fixed finite control for the pruned pair DFS. Four protected stacks hold
remaining depth, remaining strict budget, and the two current masks. The masks
also encode the DFS phases `00`, `10`, `11`; no completed-pair list is retained.
The callback receives the masks in reverse coordinate order. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DifferencePairsProgram

open OAI.Algorithms.SubexponentialSAT.StructuredProgram (Atom)
open OAI.Algorithms.SubexponentialSAT.StructuredCalls

variable {r s : ℕ}

theorem atoms_eval (code : List (Atom r s)) (a : State r s) :
    Eval (atoms code) code.length a (code.foldl (fun d op => op.eval d) a) := by
  apply Eval.base
  induction code generalizing a with
  | nil => exact StructuredProgram.Eval.skip a
  | cons op code ih =>
      simpa only [List.foldr_cons, List.foldl_cons, List.length_cons, Nat.add_comm]
        using (StructuredProgram.Eval.atom op a).seq (ih (op.eval a))

theorem pushBit_eval (p : Ports r s) (i : Fin 4) (b : Bool) (d : State r s) :
    Eval (pushBit p i b) 2 d (pushed p i b d) := by
  simpa [pushBit, pushed, Atom.eval, Atom.instr, StructuredProgram.State.ofCfg,
    StructuredProgram.State.withPC, BitProgram.execInstr] using
    atoms_eval [.set (p.register 2) b, .push (p.stack i) (p.register 2)] d

theorem enter_eval (p : Ports r s) (e u : Bool) (d : State r s) :
    Eval (enter p e u) 5 d (entered p e u d) :=
  (pushBit_eval p 2 e d).seq
    ((pushBit_eval p 3 u _).seq (atoms_eval [.set (p.register 0) true] _))

theorem body_descend (p : Ports r s) (callback : Cmd r s) (d : State r s)
    (hd : d.regs (p.register 0) = true) (b : Bool) (rest : List Bool)
    (hn : d.stacks (p.stack 0) = b :: rest) :
    Eval (body p callback) 8 d (descended p d) := by
  have hp : (popped p 0 2 d).regs (p.register 3) = true := by
    simp [popped, Atom.eval, Atom.instr, StructuredProgram.State.ofCfg,
      BitProgram.execInstr, BitProgram.readRegs, hn]
  exact .ite_true hd ((atoms_eval [.pop (p.stack 0) (p.register 2) (p.register 3)] d).seq
    (.ite_true hp (enter_eval p false false (popped p 0 2 d))))

theorem body_callback (p : Ports r s) (callback : Cmd r s) (d e : State r s)
    (hd : d.regs (p.register 0) = true) (hn : d.stacks (p.stack 0) = [])
    (t : ℕ) (hc : Eval callback t (popped p 0 2 d) e) :
    Eval (body p callback) (t + 5) d (returned p e) := by
  have h := Eval.ite_true (yes := descend p callback) (no := backtrack p) hd
    (Eval.seq (atoms_eval [.pop (p.stack 0) (p.register 2) (p.register 3)] d)
      (Eval.ite_false (yes := enter p false false) (test := p.register 3)
        (by simp [Atom.eval, Atom.instr, StructuredProgram.State.ofCfg,
          BitProgram.execInstr, BitProgram.readRegs, hn])
        (hc.seq (atoms_eval [.set (p.register 0) false, .set (p.register 1) true] e))))
  convert h using 1
  · rfl
  · simp only [List.length_cons, List.length_nil]
    omega
  · rfl

theorem body_finish (p : Ports r s) (callback : Cmd r s) (d : State r s)
    (hd : d.regs (p.register 0) = false) (es us : List Bool)
    (he : d.stacks (p.stack 2) = true :: es)
    (hu : d.stacks (p.stack 3) = true :: us) :
    Eval (body p callback) 10 d (finished p d) := by
  have hp : (popped p 2 4 d).regs (p.register 3) = true := by
    simp [popped, Atom.eval, Atom.instr, StructuredProgram.State.ofCfg,
      BitProgram.execInstr, BitProgram.readRegs, he]
  have he' : (backed p d).regs (p.register 4) = true := by
    simp [backed, popped, Atom.eval, Atom.instr, StructuredProgram.State.ofCfg,
      BitProgram.execInstr, BitProgram.readRegs, he]
  have hu' : (backed p d).regs (p.register 2) = true := by
    simp [backed, popped, Atom.eval, Atom.instr, StructuredProgram.State.ofCfg,
      BitProgram.execInstr, BitProgram.readRegs, hu]
  exact .ite_false hd
    ((atoms_eval [.pop (p.stack 2) (p.register 4) (p.register 3)] d).seq
      (.ite_true hp
        ((atoms_eval [.pop (p.stack 3) (p.register 2) (p.register 3)] _).seq
          (.ite_true he' (.ite_true hu'
            ((pushBit_eval p 1 true _).seq (pushBit_eval p 0 true _)))))))

theorem body_next_inner (p : Ports r s) (callback : Cmd r s) (d : State r s)
    (hd : d.regs (p.register 0) = false) (es us : List Bool)
    (he : d.stacks (p.stack 2) = true :: es)
    (hu : d.stacks (p.stack 3) = false :: us) :
    Eval (body p callback) 11 d (entered p true true (backed p d)) := by
  have hp : (popped p 2 4 d).regs (p.register 3) = true := by
    simp [popped, Atom.eval, Atom.instr, StructuredProgram.State.ofCfg,
      BitProgram.execInstr, BitProgram.readRegs, he]
  have he' : (backed p d).regs (p.register 4) = true := by
    simp [backed, popped, Atom.eval, Atom.instr, StructuredProgram.State.ofCfg,
      BitProgram.execInstr, BitProgram.readRegs, he]
  have hu' : (backed p d).regs (p.register 2) = false := by
    simp [backed, popped, Atom.eval, Atom.instr, StructuredProgram.State.ofCfg,
      BitProgram.execInstr, BitProgram.readRegs, hu]
  exact .ite_false hd
    ((atoms_eval [.pop (p.stack 2) (p.register 4) (p.register 3)] d).seq
      (.ite_true hp
        ((atoms_eval [.pop (p.stack 3) (p.register 2) (p.register 3)] _).seq
          (.ite_true he' (.ite_false hu' (enter_eval p true true _))))))

theorem body_next_outer (p : Ports r s) (callback : Cmd r s) (d : State r s)
    (hd : d.regs (p.register 0) = false) (es bs : List Bool) (b c : Bool)
    (he : d.stacks (p.stack 2) = false :: es)
    (hb : d.stacks (p.stack 1) = b :: c :: bs) :
    Eval (body p callback) 13 d (entered p true false (testedOutside p d)) := by
  have hp : (popped p 2 4 d).regs (p.register 3) = true := by
    simp [popped, Atom.eval, Atom.instr, StructuredProgram.State.ofCfg,
      BitProgram.execInstr, BitProgram.readRegs, he]
  have he' : (backed p d).regs (p.register 4) = false := by
    simp [backed, popped, Atom.eval, Atom.instr, StructuredProgram.State.ofCfg,
      BitProgram.execInstr, BitProgram.readRegs, he]
  have hb' : (testedOutside p d).regs (p.register 3) = true := by
    simp [testedOutside, backed, popped, Atom.eval, Atom.instr, StructuredProgram.State.ofCfg,
      BitProgram.execInstr, BitProgram.readRegs, hb]
  exact .ite_false hd
    ((atoms_eval [.pop (p.stack 2) (p.register 4) (p.register 3)] d).seq
      (.ite_true hp
        ((atoms_eval [.pop (p.stack 3) (p.register 2) (p.register 3)] _).seq
          (.ite_false he'
            ((atoms_eval [.pop (p.stack 1) (p.register 2) (p.register 3),
              .peek (p.stack 1) (p.register 2) (p.register 3)] _).seq
              (.ite_true hb' (enter_eval p true false _)))))))

theorem body_prune (p : Ports r s) (callback : Cmd r s) (d : State r s)
    (hd : d.regs (p.register 0) = false) (es : List Bool) (b : Bool)
    (he : d.stacks (p.stack 2) = false :: es) (hb : d.stacks (p.stack 1) = [b]) :
    Eval (body p callback) 12 d (pruned p d) := by
  have hp : (popped p 2 4 d).regs (p.register 3) = true := by
    simp [popped, Atom.eval, Atom.instr, StructuredProgram.State.ofCfg,
      BitProgram.execInstr, BitProgram.readRegs, he]
  have he' : (backed p d).regs (p.register 4) = false := by
    simp [backed, popped, Atom.eval, Atom.instr, StructuredProgram.State.ofCfg,
      BitProgram.execInstr, BitProgram.readRegs, he]
  have hb' : (testedOutside p d).regs (p.register 3) = false := by
    simp [testedOutside, backed, popped, Atom.eval, Atom.instr, StructuredProgram.State.ofCfg,
      BitProgram.execInstr, BitProgram.readRegs, hb]
  exact .ite_false hd
    ((atoms_eval [.pop (p.stack 2) (p.register 4) (p.register 3)] d).seq
      (.ite_true hp
        ((atoms_eval [.pop (p.stack 3) (p.register 2) (p.register 3)] _).seq
          (.ite_false he'
            ((atoms_eval [.pop (p.stack 1) (p.register 2) (p.register 3),
              .peek (p.stack 1) (p.register 2) (p.register 3)] _).seq
              (.ite_false hb' ((pushBit_eval p 1 true _).seq (pushBit_eval p 0 true _))))))))

theorem body_stop (p : Ports r s) (callback : Cmd r s) (d : State r s)
    (hd : d.regs (p.register 0) = false) (he : d.stacks (p.stack 2) = []) :
    Eval (body p callback) 4 d (stopped p d) := by
  have hp : (popped p 2 4 d).regs (p.register 3) = false := by
    simp [popped, Atom.eval, Atom.instr, StructuredProgram.State.ofCfg,
      BitProgram.execInstr, BitProgram.readRegs, he]
  exact .ite_false hd
    ((atoms_eval [.pop (p.stack 2) (p.register 4) (p.register 3)] d).seq
      (.ite_false hp (atoms_eval [.set (p.register 1) false] _)))

theorem cursor_descend (p : Ports r s) (n J : ℕ) (pre : List (Option Bool))
    (d : State r s) (h : Cursor p (n + 1) J pre true d) :
    Cursor p n J (pre ++ [none]) true (descended p d) := by
  rcases h with ⟨h0, h1, h2, h3, hm, ha⟩
  constructor <;>
    simp [descended, entered, popped, pushed, Atom.eval, Atom.instr,
      StructuredProgram.State.ofCfg, BitProgram.execInstr,
      BitProgram.readRegs, h0, h1, h2, h3, ha, List.replicate_succ]

theorem cursor_next_inner (p : Ports r s) (n J : ℕ) (pre : List (Option Bool))
    (d : State r s) (h : Cursor p n J (pre ++ [some false]) false d) :
    Cursor p n J (pre ++ [some true]) true (entered p true true (backed p d)) := by
  rcases h with ⟨h0, h1, h2, h3, hm, ha⟩
  constructor <;>
    simp [entered, backed, popped, pushed, Atom.eval, Atom.instr,
      StructuredProgram.State.ofCfg, BitProgram.execInstr,
      BitProgram.readRegs, h0, h1, h2, h3, ha]

theorem cursor_next_outer (p : Ports r s) (n J : ℕ) (pre : List (Option Bool))
    (d : State r s) (h : Cursor p n (J + 2) (pre ++ [none]) false d) :
    Cursor p n (J + 1) (pre ++ [some false]) true
      (entered p true false (testedOutside p d)) := by
  rcases h with ⟨h0, h1, h2, h3, hm, ha⟩
  constructor <;>
    simp [entered, testedOutside, backed, popped, pushed, Atom.eval, Atom.instr,
      StructuredProgram.State.ofCfg, BitProgram.execInstr,
      BitProgram.readRegs, h0, h1, h2, h3, ha, List.replicate_succ]

theorem cursor_finished (p : Ports r s) (n J : ℕ) (pre : List (Option Bool))
    (d : State r s) (h : Cursor p n J (pre ++ [some true]) false d) :
    Cursor p (n + 1) (J + 1) pre false (finished p d) := by
  rcases h with ⟨h0, h1, h2, h3, hm, ha⟩
  constructor <;>
    simp [finished, backed, popped, pushed, Atom.eval, Atom.instr,
      StructuredProgram.State.ofCfg, BitProgram.execInstr,
      BitProgram.readRegs, h0, h1, h2, h3, hm, ha, List.replicate_succ]

theorem cursor_pruned (p : Ports r s) (n : ℕ) (pre : List (Option Bool))
    (d : State r s) (h : Cursor p n 1 (pre ++ [none]) false d) :
    Cursor p (n + 1) 1 pre false (pruned p d) := by
  rcases h with ⟨h0, h1, h2, h3, hm, ha⟩
  constructor <;>
    simp [pruned, testedOutside, backed, popped, pushed, Atom.eval, Atom.instr,
      StructuredProgram.State.ofCfg, BitProgram.execInstr,
      BitProgram.readRegs, h0, h1, h2, h3, hm, ha, List.replicate_succ]

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DifferencePairsProgram
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_VisitedTape
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Passive absolute-coordinate instrumentation for the primitive machine.
The interval on every tape includes its initial input cells and every visited
head coordinate. The instrumentation never changes a primitive transition. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

open OAI.Algorithms.SubexponentialSAT.Computation
open scoped BigOperators

theorem trace_suffix {α : Type*} {step : α → Option α}
    {c d intermediate : α} {steps prefixSteps : ℕ}
    (tr : Computation.Trace step steps c d)
    (hp : Computation.Trace step prefixSteps c intermediate)
    (hle : prefixSteps ≤ steps) :
    Computation.Trace step (steps - prefixSteps) intermediate d := by
  apply Computation.Trace.of_iterate
  have h := tr.iterate
  conv_lhs at h => rw [← Nat.sub_add_cancel hle]
  rw [Function.iterate_add_apply, hp.iterate] at h
  exact h

theorem trace_prefix_bound_trans {α : Type*} {step : α → Option α}
    {a b : α} {firstSteps secondSteps : ℕ} {P : α → Prop}
    (first : Computation.Trace step firstSteps a b)
    (hfirst : ∀ prefixSteps intermediate, prefixSteps ≤ firstSteps →
      Computation.Trace step prefixSteps a intermediate → P intermediate)
    (hsecond : ∀ prefixSteps intermediate, prefixSteps ≤ secondSteps →
      Computation.Trace step prefixSteps b intermediate → P intermediate) :
    ∀ prefixSteps intermediate, prefixSteps ≤ firstSteps + secondSteps →
      Computation.Trace step prefixSteps a intermediate → P intermediate := by
  intro prefixSteps intermediate hle htrace
  by_cases hprefix : prefixSteps ≤ firstSteps
  · exact hfirst prefixSteps intermediate hprefix htrace
  · exact hsecond (prefixSteps - firstSteps) intermediate (by omega)
      (trace_suffix htrace first (by omega))

theorem trace_prefix_bound_cons {α : Type*} {step : α → Option α}
    {a b : α} {steps : ℕ} {P : α → Prop}
    (hs : step a = some b) (ha : P a)
    (htail : ∀ prefixSteps intermediate, prefixSteps ≤ steps →
      Computation.Trace step prefixSteps b intermediate → P intermediate) :
    ∀ prefixSteps intermediate, prefixSteps ≤ steps + 1 →
      Computation.Trace step prefixSteps a intermediate → P intermediate := by
  intro prefixSteps intermediate hle hp
  cases hp with
  | refl => exact ha
  | cons hs' ht =>
      have heq := Option.some.inj (hs.symm.trans hs')
      subst b
      exact htail _ _ (by omega) ht


end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_StructuredSpace
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Prefix resource preservation for the actual finite instruction linker.
The source bound concerns every intermediate configuration. Unassigned caller
stacks retain their original contents. Local runtime bounds may be used for
polynomial subroutines, but no accumulated outer-loop time appears here. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.StructuredSpace

open BitProgram

private theorem base_entry_map {r s l L : ℕ} (c : StructuredProgram.Cmd r s)
    (label : Fin l → Fin L) (embed : StructuredProgram.Site c → Fin l) (exit : Fin l) :
    StructuredProgram.entry c (label ∘ embed) (label exit) =
      label (StructuredProgram.entry c embed exit) := by
  induction c generalizing l L with
  | skip => rfl
  | atom => rfl
  | seq first second ihf ihs =>
      change StructuredProgram.entry first (label ∘ (embed ∘ Sum.inl))
        (StructuredProgram.entry second (label ∘ (embed ∘ Sum.inr)) (label exit)) = _
      rw [ihs, ihf]
  | ite => rfl
  | «while» => rfl

private theorem base_code_map {r s l L : ℕ} (c : StructuredProgram.Cmd r s)
    (label : Fin l → Fin L) (embed : StructuredProgram.Site c → Fin l) (exit : Fin l)
    (site : StructuredProgram.Site c) :
    ProgramLinking.relocateInstr id id label none (StructuredProgram.code c embed exit site) =
      StructuredProgram.code c (label ∘ embed) (label exit) site := by
  induction c generalizing l L with
  | skip => exact site.elim
  | atom op => cases op <;> rfl
  | seq first second ihf ihs =>
      cases site with
      | inl q =>
          change _ = StructuredProgram.code first (label ∘ (embed ∘ Sum.inl))
            (StructuredProgram.entry second (label ∘ (embed ∘ Sum.inr)) (label exit)) q
          rw [base_entry_map]
          exact ihf label (embed ∘ Sum.inl)
            (StructuredProgram.entry second (embed ∘ Sum.inr) exit) q
      | inr q => exact ihs label (embed ∘ Sum.inr) exit q
  | ite test yes no ihy ihn =>
      rcases site with _ | (q | q)
      · exact congrArg₂ (Instr.branch test)
          (base_entry_map yes label (fun x => embed (some (.inl x))) exit).symm
          (base_entry_map no label (fun x => embed (some (.inr x))) exit).symm
      · exact ihy label (fun x => embed (some (.inl x))) exit q
      · exact ihn label (fun x => embed (some (.inr x))) exit q
  | «while» test body ih =>
      cases site with
      | none =>
          exact congrArg₂ (Instr.branch test)
            (base_entry_map body label (embed ∘ some) (embed none)).symm rfl
      | some q => exact ih label (embed ∘ some) (embed none) q

private theorem entry_map {r s l L : ℕ} (c : StructuredCalls.Cmd r s)
    (label : Fin l → Fin L) (embed : StructuredCalls.Site c → Fin l) (exit : Fin l) :
    StructuredCalls.entry c (label ∘ embed) (label exit) =
      label (StructuredCalls.entry c embed exit) := by
  induction c generalizing l L with
  | base c => exact base_entry_map c label embed exit
  | call => rfl
  | seq first second ihf ihs =>
      change StructuredCalls.entry first (label ∘ (embed ∘ Sum.inl))
        (StructuredCalls.entry second (label ∘ (embed ∘ Sum.inr)) (label exit)) = _
      rw [ihs, ihf]
  | ite => rfl
  | «while» => rfl

private theorem code_map {r s l L : ℕ} (c : StructuredCalls.Cmd r s)
    (label : Fin l → Fin L) (embed : StructuredCalls.Site c → Fin l) (exit : Fin l)
    (site : StructuredCalls.Site c) :
    ProgramLinking.relocateInstr id id label none (StructuredCalls.code c embed exit site) =
      StructuredCalls.code c (label ∘ embed) (label exit) site := by
  induction c generalizing l L with
  | base c => exact base_code_map c label embed exit site
  | call p =>
      simp only [StructuredCalls.code]
      cases p.code site <;> rfl
  | seq first second ihf ihs =>
      cases site with
      | inl q =>
          change _ = StructuredCalls.code first (label ∘ (embed ∘ Sum.inl))
            (StructuredCalls.entry second (label ∘ (embed ∘ Sum.inr)) (label exit)) q
          rw [entry_map]
          exact ihf label (embed ∘ Sum.inl)
            (StructuredCalls.entry second (embed ∘ Sum.inr) exit) q
      | inr q => exact ihs label (embed ∘ Sum.inr) exit q
  | ite test yes no ihy ihn =>
      rcases site with _ | (q | q)
      · exact congrArg₂ (Instr.branch test)
          (entry_map yes label (fun x => embed (some (.inl x))) exit).symm
          (entry_map no label (fun x => embed (some (.inr x))) exit).symm
      · exact ihy label (fun x => embed (some (.inl x))) exit q
      · exact ihn label (fun x => embed (some (.inr x))) exit q
  | «while» test body ih =>
      cases site with
      | none =>
          exact congrArg₂ (Instr.branch test)
            (entry_map body label (embed ∘ some) (embed none)).symm rfl
      | some q => exact ih label (embed ∘ some) (embed none) q

private theorem commandLabel_sites {r s L : ℕ} (c : StructuredCalls.Cmd r s)
    (embed : StructuredCalls.Site c → Fin L) (exit : Fin L) :
    commandLabel c embed exit ∘ StructuredCalls.siteAddress c = embed := by
  funext site
  exact commandLabel_site c embed exit site

private theorem commandLabel_entry {r s L : ℕ} (c : StructuredCalls.Cmd r s)
    (embed : StructuredCalls.Site c → Fin L) (exit : Fin L)
    (inputStack outputStack : Fin s) :
    commandLabel c embed exit (StructuredCalls.compiled c inputStack outputStack).entry =
      StructuredCalls.entry c embed exit := by
  change commandLabel c embed exit
    (StructuredCalls.entry c (StructuredCalls.siteAddress c) (StructuredCalls.exitAddress c)) = _
  rw [← entry_map c (commandLabel c embed exit) (StructuredCalls.siteAddress c)
    (StructuredCalls.exitAddress c), commandLabel_sites, commandLabel_exit]

private theorem commandLabel_code {r s L : ℕ} (c : StructuredCalls.Cmd r s)
    (caller : Program r s L) (embed : StructuredCalls.Site c → Fin L) (exit : Fin L)
    (inputStack outputStack : Fin s)
    (hcode : ∀ site, caller.code (embed site) = StructuredCalls.code c embed exit site)
    (pc : Fin (StructuredCalls.size c + 1)) (hpc : pc ≠ StructuredCalls.exitAddress c) :
    caller.code (commandLabel c embed exit pc) =
      ProgramLinking.relocateInstr id id (commandLabel c embed exit) none
        ((StructuredCalls.compiled c inputStack outputStack).code pc) := by
  obtain ⟨site, rfl⟩ : ∃ site, pc = StructuredCalls.siteAddress c site := by
    cases heq : (StructuredCalls.labelEquiv c).symm pc with
    | none =>
        have hp := congrArg (StructuredCalls.labelEquiv c) heq
        exact (hpc (by simpa [StructuredCalls.exitAddress] using hp)).elim
    | some site =>
        exact ⟨site, by simpa [StructuredCalls.siteAddress] using
          (congrArg (StructuredCalls.labelEquiv c) heq)⟩
  rw [commandLabel_site, StructuredCalls.compiled_site, code_map,
    commandLabel_sites, commandLabel_exit]
  exact hcode site

/-- A bound proved for one compiled structured block transfers to every
installation of that same block in a finite caller table. No bound on the
caller's total runtime is used. -/
theorem command_stack_bound {r s L : ℕ} {c : StructuredCalls.Cmd r s}
    {steps bound : ℕ} {a b : StructuredCalls.State r s}
    (heval : StructuredCalls.Eval c steps a b) (inputStack outputStack : Fin s)
    (hsource : ∀ prefixSteps intermediate, prefixSteps ≤ steps →
      Trace (StructuredCalls.compiled c inputStack outputStack) prefixSteps
        (a.withPC (some (StructuredCalls.compiled c inputStack outputStack).entry)) intermediate →
      ∀ i, (intermediate.stacks i).length ≤ bound)
    (caller : Program r s L) (embed : StructuredCalls.Site c → Fin L) (exit : Fin L)
    (hcode : ∀ site, caller.code (embed site) = StructuredCalls.code c embed exit site) :
    ∀ prefixSteps intermediate, prefixSteps ≤ steps →
      Trace caller prefixSteps
        (a.withPC (some (StructuredCalls.entry c embed exit))) intermediate →
      ∀ i, (intermediate.stacks i).length ≤ bound := by
  intro prefixSteps intermediate hle hp i
  let routine := StructuredCalls.compiled c inputStack outputStack
  let label := commandLabel c embed exit
  let frame := a.withPC (some (StructuredCalls.entry c embed exit))
  have full := StructuredCalls.compiled_trace heval inputStack outputStack
  obtain ⟨source, hs⟩ := trace_prefix_exists full hle
  have hactive : source.pc ≠ none := by
    intro hnone
    have halted := ProgramLinking.trace_from_halted routine (trace_suffix full hs hle) hnone
    change some (StructuredCalls.exitAddress c) = none at halted
    cases halted
  have htable : ∀ pc, routine.code pc ≠ .halt →
      caller.code (label pc) = ProgramLinking.relocateInstr id id label none (routine.code pc) := by
    intro pc hnot
    apply commandLabel_code c caller embed exit inputStack outputStack hcode pc
    intro heq
    subst pc
    exact hnot (StructuredCalls.compiled_exit c inputStack outputStack)
  have hrelocated := ProgramLinking.relocate_trace_before_halt routine caller id id
    label none frame Function.injective_id Function.injective_id htable hs hactive
  have hinitial : ProgramLinking.embedCfg id id label none frame
      (a.withPC (some routine.entry)) = frame := by
    simp [ProgramLinking.embedCfg, ProgramLinking.relocatePc, routine, label, frame,
      StructuredProgram.State.withPC, commandLabel_entry]
  rw [hinitial] at hrelocated
  have heq := trace_same_length_unique hp hrelocated
  rw [heq]
  simpa [ProgramLinking.embedCfg] using hsource prefixSteps source hle hs i

/-- Sequential command blocks share one uniform space bound. -/
theorem sequence_stack_bound {r s L : ℕ} {first second : StructuredCalls.Cmd r s}
    {n m bound : ℕ} {a b c : StructuredCalls.State r s}
    (hf : StructuredCalls.Eval first n a b) (hs : StructuredCalls.Eval second m b c)
    (inputStack outputStack : Fin s)
    (hfirst : ∀ prefixSteps intermediate, prefixSteps ≤ n →
      Trace (StructuredCalls.compiled first inputStack outputStack) prefixSteps
        (a.withPC (some (StructuredCalls.compiled first inputStack outputStack).entry)) intermediate →
      ∀ i, (intermediate.stacks i).length ≤ bound)
    (hsecond : ∀ prefixSteps intermediate, prefixSteps ≤ m →
      Trace (StructuredCalls.compiled second inputStack outputStack) prefixSteps
        (b.withPC (some (StructuredCalls.compiled second inputStack outputStack).entry)) intermediate →
      ∀ i, (intermediate.stacks i).length ≤ bound)
    (caller : Program r s L) (embed : StructuredCalls.Site (.seq first second) → Fin L)
    (exit : Fin L)
    (hcode : ∀ site, caller.code (embed site) =
      StructuredCalls.code (.seq first second) embed exit site) :
    ∀ prefixSteps intermediate, prefixSteps ≤ n + m →
      Trace caller prefixSteps
        (a.withPC (some (StructuredCalls.entry (.seq first second) embed exit))) intermediate →
      ∀ i, (intermediate.stacks i).length ≤ bound := by
  exact trace_prefix_bound_trans
    (StructuredCalls.eval_trace hf caller (embed ∘ Sum.inl)
      (StructuredCalls.entry second (embed ∘ Sum.inr) exit) (fun q => hcode (.inl q)))
    (command_stack_bound hf inputStack outputStack hfirst caller (embed ∘ Sum.inl)
      (StructuredCalls.entry second (embed ∘ Sum.inr) exit) (fun q => hcode (.inl q)))
    (command_stack_bound hs inputStack outputStack hsecond caller (embed ∘ Sum.inr)
      exit (fun q => hcode (.inr q)))

/-- A loop induction combines its current body and remaining iterations by
maximum space; the number of completed iterations never multiplies the bound. -/
theorem while_true_stack_bound {r s L : ℕ} {body : StructuredCalls.Cmd r s}
    {test : Fin r} {n m bound : ℕ} {a b c : StructuredCalls.State r s}
    (htest : a.regs test = true)
    (hb : StructuredCalls.Eval body n a b)
    (hw : StructuredCalls.Eval (.while test body) m b c)
    (inputStack outputStack : Fin s)
    (hbody : ∀ prefixSteps intermediate, prefixSteps ≤ n →
      Trace (StructuredCalls.compiled body inputStack outputStack) prefixSteps
        (a.withPC (some (StructuredCalls.compiled body inputStack outputStack).entry)) intermediate →
      ∀ i, (intermediate.stacks i).length ≤ bound)
    (hwhile : ∀ prefixSteps intermediate, prefixSteps ≤ m →
      Trace (StructuredCalls.compiled (.while test body) inputStack outputStack) prefixSteps
        (b.withPC (some (StructuredCalls.compiled (.while test body) inputStack outputStack).entry))
        intermediate → ∀ i, (intermediate.stacks i).length ≤ bound)
    (caller : Program r s L)
    (embed : StructuredCalls.Site (.while test body) → Fin L) (exit : Fin L)
    (hcode : ∀ site, caller.code (embed site) =
      StructuredCalls.code (.while test body) embed exit site) :
    ∀ prefixSteps intermediate, prefixSteps ≤ n + m + 1 →
      Trace caller prefixSteps
        (a.withPC (some (StructuredCalls.entry (.while test body) embed exit))) intermediate →
      ∀ i, (intermediate.stacks i).length ≤ bound := by
  refine trace_prefix_bound_cons (steps := n + m)
    (P := fun x : Cfg r s L => ∀ i, (x.stacks i).length ≤ bound)
    (b := a.withPC (some (StructuredCalls.entry body (embed ∘ some) (embed none)))) ?_ ?_ ?_
  · simp [step, StructuredProgram.State.withPC, StructuredCalls.entry,
      hcode none, StructuredCalls.code, execInstr, htest]
  · exact hbody 0 _ (Nat.zero_le n) (.refl _)
  · exact trace_prefix_bound_trans
      (StructuredCalls.eval_trace hb caller (embed ∘ some) (embed none)
        (fun q => hcode (some q)))
      (command_stack_bound hb inputStack outputStack hbody caller (embed ∘ some)
        (embed none) (fun q => hcode (some q)))
      (command_stack_bound hw inputStack outputStack hwhile caller embed exit hcode)

theorem while_false_stack_bound {r s L : ℕ} (body : StructuredCalls.Cmd r s)
    (test : Fin r) {bound : ℕ} (a : StructuredCalls.State r s)
    (htest : a.regs test = false) (hstart : ∀ i, (a.stacks i).length ≤ bound)
    (caller : Program r s L)
    (embed : StructuredCalls.Site (.while test body) → Fin L) (exit : Fin L)
    (hcode : ∀ site, caller.code (embed site) =
      StructuredCalls.code (.while test body) embed exit site) :
    ∀ prefixSteps intermediate, prefixSteps ≤ 1 →
      Trace caller prefixSteps
        (a.withPC (some (StructuredCalls.entry (.while test body) embed exit))) intermediate →
      ∀ i, (intermediate.stacks i).length ≤ bound := by
  refine trace_prefix_bound_cons (steps := 0)
    (P := fun x : Cfg r s L => ∀ i, (x.stacks i).length ≤ bound)
    (b := a.withPC (some exit)) ?_ hstart ?_
  · simp [step, StructuredProgram.State.withPC, StructuredCalls.entry,
      hcode none, StructuredCalls.code, execInstr, htest]
  · intro prefixSteps intermediate hle hp
    have hz : prefixSteps = 0 := by omega
    subst prefixSteps
    cases hp
    exact hstart

theorem conditional_true_stack_bound {r s L : ℕ} {yes no : StructuredCalls.Cmd r s}
    {test : Fin r} {steps bound : ℕ} {a b : StructuredCalls.State r s}
    (htest : a.regs test = true) (heval : StructuredCalls.Eval yes steps a b)
    (inputStack outputStack : Fin s)
    (hsource : ∀ prefixSteps intermediate, prefixSteps ≤ steps →
      Trace (StructuredCalls.compiled yes inputStack outputStack) prefixSteps
        (a.withPC (some (StructuredCalls.compiled yes inputStack outputStack).entry)) intermediate →
      ∀ i, (intermediate.stacks i).length ≤ bound)
    (caller : Program r s L) (embed : StructuredCalls.Site (.ite test yes no) → Fin L)
    (exit : Fin L)
    (hcode : ∀ site, caller.code (embed site) =
      StructuredCalls.code (.ite test yes no) embed exit site) :
    ∀ prefixSteps intermediate, prefixSteps ≤ steps + 1 →
      Trace caller prefixSteps
        (a.withPC (some (StructuredCalls.entry (.ite test yes no) embed exit))) intermediate →
      ∀ i, (intermediate.stacks i).length ≤ bound := by
  refine trace_prefix_bound_cons (steps := steps)
    (P := fun x : Cfg r s L => ∀ i, (x.stacks i).length ≤ bound)
    (b := a.withPC (some (StructuredCalls.entry yes (fun q => embed (some (.inl q))) exit)))
    ?_ ?_ ?_
  · simp [step, StructuredProgram.State.withPC, StructuredCalls.entry,
      hcode none, StructuredCalls.code, execInstr, htest]
  · exact hsource 0 _ (Nat.zero_le steps) (.refl _)
  · exact command_stack_bound heval inputStack outputStack hsource caller
      (fun q => embed (some (.inl q))) exit (fun q => hcode (some (.inl q)))

theorem conditional_false_stack_bound {r s L : ℕ} {yes no : StructuredCalls.Cmd r s}
    {test : Fin r} {steps bound : ℕ} {a b : StructuredCalls.State r s}
    (htest : a.regs test = false) (heval : StructuredCalls.Eval no steps a b)
    (inputStack outputStack : Fin s)
    (hsource : ∀ prefixSteps intermediate, prefixSteps ≤ steps →
      Trace (StructuredCalls.compiled no inputStack outputStack) prefixSteps
        (a.withPC (some (StructuredCalls.compiled no inputStack outputStack).entry)) intermediate →
      ∀ i, (intermediate.stacks i).length ≤ bound)
    (caller : Program r s L) (embed : StructuredCalls.Site (.ite test yes no) → Fin L)
    (exit : Fin L)
    (hcode : ∀ site, caller.code (embed site) =
      StructuredCalls.code (.ite test yes no) embed exit site) :
    ∀ prefixSteps intermediate, prefixSteps ≤ steps + 1 →
      Trace caller prefixSteps
        (a.withPC (some (StructuredCalls.entry (.ite test yes no) embed exit))) intermediate →
      ∀ i, (intermediate.stacks i).length ≤ bound := by
  refine trace_prefix_bound_cons (steps := steps)
    (P := fun x : Cfg r s L => ∀ i, (x.stacks i).length ≤ bound)
    (b := a.withPC (some (StructuredCalls.entry no (fun q => embed (some (.inr q))) exit)))
    ?_ ?_ ?_
  · simp [step, StructuredProgram.State.withPC, StructuredCalls.entry,
      hcode none, StructuredCalls.code, execInstr, htest]
  · exact hsource 0 _ (Nat.zero_le steps) (.refl _)
  · exact command_stack_bound heval inputStack outputStack hsource caller
      (fun q => embed (some (.inr q))) exit (fun q => hcode (some (.inr q)))

/-- A boundary invariant and a uniform actual-body prefix bound establish the
same space bound through any finite number of loop iterations. -/
theorem loop_stack_bound {r s : ℕ} (body : StructuredCalls.Cmd r s) (test : Fin r)
    (inputStack outputStack : Fin s) (I : StructuredCalls.State r s → Prop) (bound : ℕ)
    (hinitial : ∀ a, I a → ∀ i, (a.stacks i).length ≤ bound)
    (hpreserve : ∀ n a b, StructuredCalls.Eval body n a b → I a →
      a.regs test = true → I b)
    (hbody : ∀ n a b, StructuredCalls.Eval body n a b → I a → a.regs test = true →
      ∀ prefixSteps intermediate, prefixSteps ≤ n →
        Trace (StructuredCalls.compiled body inputStack outputStack) prefixSteps
          (a.withPC (some (StructuredCalls.compiled body inputStack outputStack).entry))
          intermediate → ∀ i, (intermediate.stacks i).length ≤ bound)
    {steps : ℕ} {a b : StructuredCalls.State r s}
    (heval : StructuredCalls.Eval (.while test body) steps a b) (ha : I a) :
    ∀ prefixSteps intermediate, prefixSteps ≤ steps →
      Trace (StructuredCalls.compiled (.while test body) inputStack outputStack) prefixSteps
        (a.withPC (some (StructuredCalls.compiled (.while test body) inputStack outputStack).entry))
        intermediate → ∀ i, (intermediate.stacks i).length ≤ bound := by
  induction steps using Nat.strong_induction_on generalizing a b with
  | h steps ih =>
      cases heval with
      | while_false htest =>
          exact while_false_stack_bound body test a htest (hinitial a ha)
            _ _ _ (StructuredCalls.compiled_site _ inputStack outputStack)
      | @while_true _ _ n m a middle b htest hb hw =>
          have hmiddle := hpreserve n a middle hb ha htest
          exact while_true_stack_bound htest hb hw inputStack outputStack
            (hbody n a middle hb ha htest) (ih m (by omega) hw hmiddle)
            _ _ _ (StructuredCalls.compiled_site _ inputStack outputStack)

/-- The final concrete halt instruction changes no stack and preserves the
bound already established through the command's exit boundary. -/
theorem compiled_halt_stack_bound {r s : ℕ} {command : StructuredCalls.Cmd r s}
    {steps bound : ℕ} {a b : StructuredCalls.State r s}
    (heval : StructuredCalls.Eval command steps a b) (inputStack outputStack : Fin s)
    (hsource : ∀ prefixSteps intermediate, prefixSteps ≤ steps →
      Trace (StructuredCalls.compiled command inputStack outputStack) prefixSteps
        (a.withPC (some (StructuredCalls.compiled command inputStack outputStack).entry))
        intermediate → ∀ i, (intermediate.stacks i).length ≤ bound) :
    ∀ prefixSteps intermediate, prefixSteps ≤ steps + 1 →
      Trace (StructuredCalls.compiled command inputStack outputStack) prefixSteps
        (a.withPC (some (StructuredCalls.compiled command inputStack outputStack).entry))
        intermediate → ∀ i, (intermediate.stacks i).length ≤ bound := by
  intro prefixSteps intermediate hle hp
  by_cases hbefore : prefixSteps ≤ steps
  · exact hsource prefixSteps intermediate hbefore hp
  · have hlast : prefixSteps = steps + 1 := by omega
    subst prefixSteps
    have heq := trace_same_length_unique hp
      (StructuredCalls.compiled_halt_trace heval inputStack outputStack)
    rw [heq]
    have hend := hsource steps (b.withPC (some (StructuredCalls.exitAddress command))) le_rfl
      (StructuredCalls.compiled_trace heval inputStack outputStack)
    exact hend

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.StructuredSpace
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_StreamResources
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FiniteField.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Uniform storage rules for concrete streaming loops. A local runtime bound
is used only for one invocation whose entire initial storage is uniformly
bounded; neither bound depends on the number of loop iterations. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.StreamResources

open BitProgram

/-- Summing the port bounds counts every simultaneously live buffer. -/
theorem dataBits_le_mul {r s l bound : ℕ} (c : Cfg r s l)
    (h : ∀ i, (c.stacks i).length ≤ bound) : dataBits c ≤ s * bound := by
  simpa [dataBits, stackBits] using Finset.sum_le_card_nsmul Finset.univ
    (fun i => (c.stacks i).length) bound (fun i _ => h i)

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.StreamResources
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_DifferencePairsSpace
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Every source prefix of the actual pruned pair traversal. The two masks
carry the DFS phases; the resource invariant counts all caller stacks as well
as the four controller stacks. Callback time never contributes to the space
bound. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DifferencePairsSpace

open BitProgram StructuredCalls DifferencePairsProgram

variable {r s : ℕ}

private theorem short_prefix (p : Ports r s) {c : Cmd r s} {d : State r s}
    {B t : ℕ} (hb : ∀ i, (d.stacks i).length ≤ B) (ht : t ≤ 13) :
    ∀ q e, q ≤ t →
      Trace (compiled c (p.stack 0) (p.stack 2)) q
        (d.withPC (some (compiled c (p.stack 0) (p.stack 2)).entry)) e →
      ∀ i, (e.stacks i).length ≤ s * B + 13 := by
  intro q e hq he i
  exact StructuredSpace.local_stack_bound (compiled c (p.stack 0) (p.stack 2))
    (steps := 13) (StreamResources.dataBits_le_mul _ hb) q e (hq.trans ht) he i

private theorem cursor_bound (p : Ports r s) {N J B n j : ℕ}
    {pre : List (Option Bool)} {down : Bool} {a d : State r s}
    (hN : N ≤ B) (hJ : J ≤ B) (hn : n + pre.length = N)
    (hj : j + pre.countP Option.isSome = J) (hc : Cursor p n j pre down d)
    (ha : ∀ i, (a.stacks i).length ≤ B)
    (hf : ∀ i, (∀ k, i ≠ p.stack k) → d.stacks i = a.stacks i) :
    ∀ i, (d.stacks i).length ≤ B := by
  intro i
  by_cases h : ∃ k, i = p.stack k
  · obtain ⟨k, rfl⟩ := h
    fin_cases k
    · change (d.stacks (p.stack 0)).length ≤ B
      rw [hc.depth, List.length_replicate]; omega
    · change (d.stacks (p.stack 1)).length ≤ B
      rw [hc.budget, List.length_replicate]; omega
    · change (d.stacks (p.stack 2)).length ≤ B
      rw [hc.outer, List.length_reverse, List.length_map]; omega
    · change (d.stacks (p.stack 3)).length ≤ B
      rw [hc.inner, List.length_reverse, List.length_map]; omega
  · rw [hf i (by simpa using h)]
    exact ha i

/-- The callback branch has three control instructions before the callback and
two register updates after it. The callback's own uniform bound is retained. -/
theorem callback_prefix (p : Ports r s) (callback : Cmd r s)
    {d e : State r s} {t B D : ℕ}
    (hd : d.regs (p.register 0) = true) (hn : d.stacks (p.stack 0) = [])
    (hb : ∀ i, (d.stacks i).length ≤ B)
    (he : ∀ i, (e.stacks i).length ≤ B)
    (hc : Eval callback t (popped p 0 2 d) e)
    (hp : ∀ q z, q ≤ t →
      Trace (compiled callback (p.stack 0) (p.stack 2)) q
        ((popped p 0 2 d).withPC
          (some (compiled callback (p.stack 0) (p.stack 2)).entry)) z →
      ∀ i, (z.stacks i).length ≤ D) :
    ∀ q z, q ≤ t + 5 →
      Trace (compiled (body p callback) (p.stack 0) (p.stack 2)) q
        (d.withPC (some (compiled (body p callback) (p.stack 0) (p.stack 2)).entry)) z →
      ∀ i, (z.stacks i).length ≤ max D (s * B + 13) := by
  let tail : Cmd r s := atoms [.set (p.register 0) false, .set (p.register 1) true]
  have htail : Eval tail 2 e (returned p e) := atoms_eval _ e
  have ht := short_prefix p (c := tail) he (show 2 ≤ 13 by omega)
  have ht' : ∀ q z, q ≤ 2 →
      Trace (compiled tail (p.stack 0) (p.stack 2)) q
        (e.withPC (some (compiled tail (p.stack 0) (p.stack 2)).entry)) z →
      ∀ i, (z.stacks i).length ≤ max D (s * B + 13) := by
    intro q z hq hz i
    exact (ht q z hq hz i).trans (Nat.le_max_right _ _)
  have hp' : ∀ q z, q ≤ t →
      Trace (compiled callback (p.stack 0) (p.stack 2)) q
        ((popped p 0 2 d).withPC
          (some (compiled callback (p.stack 0) (p.stack 2)).entry)) z →
      ∀ i, (z.stacks i).length ≤ max D (s * B + 13) := by
    intro q z hq hz i
    exact (hp q z hq hz i).trans (Nat.le_max_left _ _)
  have hseq := StructuredSpace.sequence_stack_bound hc htail (p.stack 0) (p.stack 2)
    hp' ht' (compiled (.seq callback tail) (p.stack 0) (p.stack 2))
    (siteAddress (.seq callback tail)) (exitAddress (.seq callback tail))
    (compiled_site _ (p.stack 0) (p.stack 2))
  have hfalse : (popped p 0 2 d).regs (p.register 3) = false := by
    simp [popped, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
      StructuredProgram.State.ofCfg, execInstr, readRegs, hn]
  have hcond := StructuredSpace.conditional_false_stack_bound
    (yes := enter p false false) hfalse (hc.seq htail) (p.stack 0) (p.stack 2) hseq
    (compiled (.ite (p.register 3) (enter p false false) (.seq callback tail))
      (p.stack 0) (p.stack 2))
    (siteAddress _) (exitAddress _) (compiled_site _ (p.stack 0) (p.stack 2))
  have hpop : Eval (atoms [.pop (p.stack 0) (p.register 2) (p.register 3)])
      1 d (popped p 0 2 d) := atoms_eval _ d
  have hpop' : ∀ q z, q ≤ 1 →
      Trace (compiled (atoms [.pop (p.stack 0) (p.register 2) (p.register 3)])
        (p.stack 0) (p.stack 2)) q
        (d.withPC (some (compiled
          (atoms [.pop (p.stack 0) (p.register 2) (p.register 3)])
          (p.stack 0) (p.stack 2)).entry)) z →
      ∀ i, (z.stacks i).length ≤ max D (s * B + 13) := by
    intro q z hq hz i
    exact (short_prefix p hb (show 1 ≤ 13 by omega) q z hq hz i).trans
      (Nat.le_max_right _ _)
  have hdesc := StructuredSpace.sequence_stack_bound hpop
    (Eval.ite_false hfalse (hc.seq htail)) (p.stack 0) (p.stack 2) hpop' hcond
    (compiled (descend p callback) (p.stack 0) (p.stack 2))
    (siteAddress _) (exitAddress _) (compiled_site _ (p.stack 0) (p.stack 2))
  have h := StructuredSpace.conditional_true_stack_bound (no := backtrack p) hd
    (hpop.seq (Eval.ite_false hfalse (hc.seq htail))) (p.stack 0) (p.stack 2) hdesc
    (compiled (body p callback) (p.stack 0) (p.stack 2))
    (siteAddress _) (exitAddress _) (compiled_site _ (p.stack 0) (p.stack 2))
  intro q z hq hz
  exact h q z (by omega) hz

/-- One real DFS body step preserves the bounded controller geometry and all
persistent stack bounds. The only unbounded-time branch is split around its
actual callback. -/
theorem body_resources (p : Ports r s) (callback : Cmd r s) (output : Fin s)
    (visit : List (Option Bool) → List Bool → List Bool) (I : State r s → Prop)
    (C N J B D : ℕ)
    (spec : CallbackSpec p callback output visit C N I) (hN : N ≤ B) (hJ : J ≤ B)
    (hcallback : ∀ j pre a b t, pre.length = N →
      (j + 1) + pre.countP Option.isSome = J → Cursor p 0 (j + 1) pre true a → I a →
      (∀ i, (a.stacks i).length ≤ B) → Eval callback t (popped p 0 2 a) b →
      (∀ i, (b.stacks i).length ≤ B) ∧
      ∀ q z, q ≤ t → Trace (compiled callback (p.stack 0) (p.stack 2)) q
        ((popped p 0 2 a).withPC
          (some (compiled callback (p.stack 0) (p.stack 2)).entry)) z →
        ∀ i, (z.stacks i).length ≤ D)
    {n j : ℕ} {pre : List (Option Bool)} {down : Bool} {d : State r s}
    (hc : Cursor p n (j + 1) pre down d) (hn : n + pre.length = N)
    (hj : (j + 1) + pre.countP Option.isSome = J)
    (hb : ∀ i, (d.stacks i).length ≤ B) (hI : I d) :
    ∃ t e, Eval (body p callback) t d e ∧ I e ∧
      (∀ i, (e.stacks i).length ≤ B) ∧
      (e.regs (p.register 1) = true →
        ∃ n j pre down, Cursor p n (j + 1) pre down e ∧
          n + pre.length = N ∧ (j + 1) + pre.countP Option.isSome = J) ∧
      ∀ q z, q ≤ t → Trace (compiled (body p callback) (p.stack 0) (p.stack 2)) q
        (d.withPC (some (compiled (body p callback) (p.stack 0) (p.stack 2)).entry)) z →
        ∀ i, (z.stacks i).length ≤ max D (s * B + 13) := by
  have short {e : State r s} {t n' j' : ℕ} {pre' : List (Option Bool)} {down' : Bool}
      (heval : Eval (body p callback) t d e) (ht : t ≤ 13)
      (hc' : Cursor p n' (j' + 1) pre' down' e)
      (hn' : n' + pre'.length = N)
      (hj' : (j' + 1) + pre'.countP Option.isSome = J)
      (hf : ∀ i, (∀ k, i ≠ p.stack k) → e.stacks i = d.stacks i) :
      ∃ t e, Eval (body p callback) t d e ∧ I e ∧
        (∀ i, (e.stacks i).length ≤ B) ∧
        (e.regs (p.register 1) = true →
          ∃ n j pre down, Cursor p n (j + 1) pre down e ∧
            n + pre.length = N ∧ (j + 1) + pre.countP Option.isSome = J) ∧
        ∀ q z, q ≤ t → Trace (compiled (body p callback) (p.stack 0) (p.stack 2)) q
          (d.withPC (some (compiled (body p callback) (p.stack 0) (p.stack 2)).entry)) z →
          ∀ i, (z.stacks i).length ≤ max D (s * B + 13) := by
    refine ⟨t, e, heval, spec.stable d e hf hI, cursor_bound p hN hJ hn' hj' hc' hb hf,
      (fun _ => ⟨n', j', pre', down', hc', hn', hj'⟩), ?_⟩
    intro q z hq hz i
    exact (short_prefix p hb ht q z hq hz i).trans (Nat.le_max_right _ _)
  cases down with
  | true =>
      cases n with
      | zero =>
          obtain ⟨t, e, _, he, hf, _, hIe⟩ := spec.run j pre d (by omega) hc hI
          obtain ⟨heB, heD⟩ := hcallback j pre d e t (by simpa using hn) hj hc hI hb he
          have hr : Cursor p 0 (j + 1) pre false (returned p e) :=
            ⟨(hf 0).trans hc.depth, (hf 1).trans hc.budget, (hf 2).trans hc.outer,
              (hf 3).trans hc.inner, returned_descending p e, returned_active p e⟩
          refine ⟨t + 5, returned p e,
            body_callback p callback d e hc.descending (by simpa using hc.depth) t he,
            spec.stable e (returned p e) (by intros; rfl) hIe,
            heB, (fun _ => ⟨0, j, pre, false, hr, hn, hj⟩), ?_⟩
          exact callback_prefix p callback hc.descending (by simpa using hc.depth) hb heB he heD
      | succ n =>
          apply short (body_descend p callback d hc.descending true (List.replicate n true)
            (by simpa [List.replicate_succ] using hc.depth)) (by omega)
            (cursor_descend p n (j + 1) pre d hc)
          · simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hn
          · simpa using hj
          · intro i hi
            simp [descended, entered_frame _ _ _ _ _ (hi 2) (hi 3), popped_frame,
              hi 0]
  | false =>
      rcases List.eq_nil_or_concat' pre with rfl | ⟨pre, last, rfl⟩
      · have hs : (stopped p d).stacks = d.stacks := by
          funext i
          simp [stopped, popped, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
            StructuredProgram.State.ofCfg, execInstr,
            hc.outer]
          rw [← (show d.stacks (p.stack 2) = [] from by simpa using hc.outer),
            Function.update_eq_self]
        refine ⟨4, stopped p d, body_stop p callback d hc.descending
          (by simpa using hc.outer), ?_, ?_, ?_, ?_⟩
        · exact spec.stable d (stopped p d) (by intros; simp only [hs]) hI
        · simpa only [hs] using hb
        · intro hactive
          simp [stopped, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
            StructuredProgram.State.ofCfg, execInstr] at hactive
        · intro q z hq hz i
          exact (short_prefix p hb (show 4 ≤ 13 by omega) q z hq hz i).trans
            (Nat.le_max_right _ _)
      · cases last with
        | none =>
            cases j with
            | zero =>
                apply short (body_prune p callback d hc.descending
                  (pre.map Option.isSome).reverse true (by simpa using hc.outer)
                  (by simpa using hc.budget)) (by omega) (cursor_pruned p n pre d hc)
                · simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hn
                · simpa using hj
                · intro i hi
                  simp [pruned, testedOutside_stacks, backed, pushed_frame, popped_frame,
                    hi 0, hi 1, hi 2, hi 3]
            | succ j =>
                apply short (body_next_outer p callback d hc.descending
                  (pre.map Option.isSome).reverse (List.replicate j true) true true
                  (by simpa using hc.outer) (by simpa [List.replicate_succ] using hc.budget))
                  (by omega) (cursor_next_outer p n j pre d hc)
                · simpa using hn
                · simp at hj ⊢
                  omega
                · intro i hi
                  simp [testedOutside_stacks, backed, popped_frame, hi 1, hi 2, hi 3]
        | some bit =>
            cases bit with
            | false =>
                apply short (body_next_inner p callback d hc.descending
                  (pre.map Option.isSome).reverse (pre.map (fun a => a.getD false)).reverse
                  (by simpa using hc.outer) (by simpa using hc.inner)) (by omega)
                  (cursor_next_inner p n (j + 1) pre d hc)
                · simpa using hn
                · simpa using hj
                · intro i hi
                  simp [backed, popped_frame, hi 2, hi 3]
            | true =>
                apply short (body_finish p callback d hc.descending
                  (pre.map Option.isSome).reverse (pre.map (fun a => a.getD false)).reverse
                  (by simpa using hc.outer) (by simpa using hc.inner)) (by omega)
                  (cursor_finished p n (j + 1) pre d hc)
                · simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hn
                · simp at hj ⊢
                  omega
                · intro i hi
                  simp [finished, backed, pushed_frame, popped_frame, hi 0, hi 1, hi 2, hi 3]

/-- The complete actual loop has a bound independent of the number of pairs.
The conserved depth and strict budget bound every DFS controller word. -/
theorem loop_stack_bound (p : Ports r s) (callback : Cmd r s) (output : Fin s)
    (visit : List (Option Bool) → List Bool → List Bool) (I : State r s → Prop)
    (C N J B D : ℕ)
    (spec : CallbackSpec p callback output visit C N I) (hN : N ≤ B) (hJ : J ≤ B)
    (hcallback : ∀ j pre a b t, pre.length = N →
      (j + 1) + pre.countP Option.isSome = J → Cursor p 0 (j + 1) pre true a → I a →
      (∀ i, (a.stacks i).length ≤ B) → Eval callback t (popped p 0 2 a) b →
      (∀ i, (b.stacks i).length ≤ B) ∧
      ∀ q z, q ≤ t → Trace (compiled callback (p.stack 0) (p.stack 2)) q
        ((popped p 0 2 a).withPC
          (some (compiled callback (p.stack 0) (p.stack 2)).entry)) z →
        ∀ i, (z.stacks i).length ≤ D)
    {steps : ℕ} {a b : State r s}
    (heval : Eval (.while (p.register 1) (body p callback)) steps a b)
    (ha : ∀ i, (a.stacks i).length ≤ B) (hIa : I a)
    (hcursor : a.regs (p.register 1) = true →
      ∃ n j pre down, Cursor p n (j + 1) pre down a ∧
        n + pre.length = N ∧ (j + 1) + pre.countP Option.isSome = J) :
    ∀ q z, q ≤ steps →
      Trace (compiled (.while (p.register 1) (body p callback)) (p.stack 0) (p.stack 2)) q
        (a.withPC (some (compiled (.while (p.register 1) (body p callback))
          (p.stack 0) (p.stack 2)).entry)) z →
        ∀ i, (z.stacks i).length ≤ max D (s * B + 13) := by
  let Inv := fun a : State r s => I a ∧ (∀ i, (a.stacks i).length ≤ B) ∧
    (a.regs (p.register 1) = true →
      ∃ n j pre down, Cursor p n (j + 1) pre down a ∧
        n + pre.length = N ∧ (j + 1) + pre.countP Option.isSome = J)
  have hB : B ≤ max D (s * B + 13) := by
    have hs : 1 ≤ s := by have := (p.stack 0).isLt; omega
    have hm : B ≤ s * B := by simpa using Nat.mul_le_mul_right B hs
    exact hm.trans ((Nat.le_add_right _ _).trans (Nat.le_max_right _ _))
  apply StructuredSpace.loop_stack_bound (body p callback) (p.register 1)
    (p.stack 0) (p.stack 2) Inv (max D (s * B + 13)) _ _ _ heval ⟨hIa, ha, hcursor⟩
  · intro d hd i
    exact (hd.2.1 i).trans hB
  · intro t d e he hd hactive
    obtain ⟨n, j, pre, down, hc, hn, hj⟩ := hd.2.2 hactive
    obtain ⟨t', e', he', hIe, hb', hc', _⟩ :=
      body_resources p callback output visit I C N J B D spec hN hJ hcallback hc hn hj hd.2.1 hd.1
    have heq := Eval.final_unique (p.stack 0) he he'
    subst e'
    exact ⟨hIe, hb', hc'⟩
  · intro t d e he hd hactive
    obtain ⟨n, j, pre, down, hc, hn, hj⟩ := hd.2.2 hactive
    obtain ⟨t', e', he', _, _, _, hp⟩ :=
      body_resources p callback output visit I C N J B D spec hN hJ hcallback hc hn hj hd.2.1 hd.1
    have heq := StreamResources.eval_steps_eq (p.stack 0) (p.stack 2) he he'
    subst t'
    exact hp

/-- Initialization, every DFS iteration, and the concrete final halt share one
space bound on the same actual source execution. Zero budget performs no
callback and is covered as well. -/
theorem program_stack_bound_oai (p : Ports r s) (callback : Cmd r s) (output : Fin s)
    (visit : List (Option Bool) → List Bool → List Bool) (I : State r s → Prop)
    (C N J B D : ℕ)
    (spec : CallbackSpec p callback output visit C N I)
    (hcallback : ∀ j pre a b t, pre.length = N →
      (j + 1) + pre.countP Option.isSome = J → Cursor p 0 (j + 1) pre true a → I a →
      (∀ i, (a.stacks i).length ≤ B) → Eval callback t (popped p 0 2 a) b →
      (∀ i, (b.stacks i).length ≤ B) ∧
      ∀ q z, q ≤ t → Trace (compiled callback (p.stack 0) (p.stack 2)) q
        ((popped p 0 2 a).withPC
          (some (compiled callback (p.stack 0) (p.stack 2)).entry)) z →
        ∀ i, (z.stacks i).length ≤ D)
    {steps : ℕ} {a b : State r s} (heval : Eval (command p callback) steps a b)
    (ha : ∀ i, (a.stacks i).length ≤ B) (hIa : I a)
    (hdepth : a.stacks (p.stack 0) = List.replicate N true)
    (hbudget : a.stacks (p.stack 1) = List.replicate J true)
    (houter : a.stacks (p.stack 2) = []) (hinner : a.stacks (p.stack 3) = []) :
    ∀ q z, q ≤ steps + 1 → Trace (program p callback) q
      (a.withPC (some (program p callback).entry)) z →
      ∀ i, (z.stacks i).length ≤ max D (s * B + 13) := by
  have hN : N ≤ B := by simpa [hdepth] using ha (p.stack 0)
  have hJ : J ≤ B := by simpa [hbudget] using ha (p.stack 1)
  apply StructuredSpace.compiled_halt_stack_bound heval (p.stack 0) (p.stack 2)
  change Eval (.seq _ _) steps a b at heval
  cases heval with
  | @seq first second n m a middle b hinit hwhile =>
      have hi := atoms_eval [.peek (p.stack 1) (p.register 2) (p.register 3),
        .copy (p.register 1) (p.register 3), .set (p.register 0) true] a
      have hmid : middle = initialized p a := Eval.final_unique (p.stack 0) hinit hi
      subst middle
      have hn : n = 3 := StreamResources.eval_steps_eq (p.stack 0) (p.stack 2) hinit hi
      subst n
      have hcursor : (initialized p a).regs (p.register 1) = true →
          ∃ n j pre down, Cursor p n (j + 1) pre down (initialized p a) ∧
            n + pre.length = N ∧ (j + 1) + pre.countP Option.isSome = J := by
        intro hactive
        cases J with
        | zero =>
            simp [initialized, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
              StructuredProgram.State.ofCfg, execInstr,
              readRegs, hbudget] at hactive
        | succ J =>
            refine ⟨N, J, [], true, ?_, by simp, by simp⟩
            refine ⟨hdepth, hbudget, houter, hinner, ?_, hactive⟩
            simp [initialized, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
              StructuredProgram.State.ofCfg, execInstr]
      have hloop := loop_stack_bound p callback output visit I C N J B D spec hN hJ
        hcallback hwhile ha (spec.stable a (initialized p a) (by intros; rfl) hIa) hcursor
      have hp : ∀ q z, q ≤ 3 → Trace (compiled
          (atoms [.peek (p.stack 1) (p.register 2) (p.register 3),
            .copy (p.register 1) (p.register 3), .set (p.register 0) true])
          (p.stack 0) (p.stack 2)) q
          (a.withPC (some (compiled
            (atoms [.peek (p.stack 1) (p.register 2) (p.register 3),
              .copy (p.register 1) (p.register 3), .set (p.register 0) true])
            (p.stack 0) (p.stack 2)).entry)) z →
          ∀ i, (z.stacks i).length ≤ max D (s * B + 13) := by
        intro q z hq hz i
        exact (short_prefix p ha (show 3 ≤ 13 by omega) q z hq hz i).trans
          (Nat.le_max_right _ _)
      exact StructuredSpace.sequence_stack_bound hinit hwhile (p.stack 0) (p.stack 2)
        hp hloop (program p callback) (siteAddress (command p callback))
        (exitAddress (command p callback)) (compiled_site _ (p.stack 0) (p.stack 2))

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DifferencePairsSpace
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DifferencePairsSpace.program_stack_bound_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DifferencePairsSpace.program_stack_bound_oai
