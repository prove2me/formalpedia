-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SubexpRowPostfixInterpreter.global_complete_runsIn
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T04:39:52.708564+00:00
-- url     : https://prove2.me/submissions/390648c9-34e4-4307-8dc3-57bbdc8ddcbc

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S099

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpPostfixControl
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Concrete postfix instruction dispatch and literal push

The fixed prefix tags are push `0`, add `10`, and multiply `11`.
A push tag is followed by an `Encoding.frame` coefficient payload. End of
the code stack ends the instruction stream. The base dispatcher exposes
explicit service exits. The linked program implements literal push through
the actual frame parser and a Boolean-stack encoding loop; scalar arithmetic
remains at explicit service boundaries.

Registers: 0 last bit, 1 successful-pop flag, 2 binary-operation flag.
Stacks: 0 serialized code, 1 unary operand depth, 2 framed operand data.
The operand data stack is preserved throughout dispatch. On a successful
dispatch the depth stack has already been adjusted for the pending service.
The linked literal service uses stack 3 as initially empty scratch and returns
to dispatch with that scratch empty and the framed operand list updated.
-/

namespace SubexponentialSAT.SubexpPostfixControl

open BitProgram

theorem tag_pop (b v p op : Bool) (code depth operands : List Bool) :
    step program (cfg (some 0) v p op (b :: code) depth operands) =
      some (cfg (some 1) b true op code depth operands) := by
  simp [step, cfg, execInstr, readRegs]

theorem tag_present (v op : Bool) (code depth operands : List Bool) :
    step program (cfg (some 1) v true op code depth operands) =
      some (cfg (some 2) v true op code depth operands) := by
  simp [step, cfg, execInstr]

theorem push_tag (op : Bool) (code depth operands : List Bool) :
    step program (cfg (some 2) false true op code depth operands) =
      some (cfg (some 3) false true op code depth operands) := by
  simp [step, cfg, execInstr]

theorem push_set (op : Bool) (code depth operands : List Bool) :
    step program (cfg (some 3) false true op code depth operands) =
      some (cfg (some 4) true true op code depth operands) := by
  simp [step, cfg, execInstr]

theorem push_depth (op : Bool) (code depth operands : List Bool) :
    step program (cfg (some 4) true true op code depth operands) =
      some (cfg (some pushService) true true op code (true :: depth) operands) := by
  simp [step, cfg, execInstr]

/-- Five actual transitions decode push and reserve one new operand slot. -/
theorem prepare_push_trace (v p op : Bool) (code depth operands : List Bool) :
    Trace program 5 (cfg (some 0) v p op (false :: code) depth operands)
      (cfg (some pushService) true true op code (true :: depth) operands) :=
  .cons (tag_pop false v p op code depth operands)
    (.cons (tag_present false op code depth operands)
      (.cons (push_tag op code depth operands)
        (.cons (push_set op code depth operands)
          (.cons (push_depth op code depth operands) (.refl _)))))

theorem binary_tag (op : Bool) (code depth operands : List Bool) :
    step program (cfg (some 2) true true op code depth operands) =
      some (cfg (some 5) true true op code depth operands) := by
  simp [step, cfg, execInstr]

theorem operation_pop (b v p op : Bool) (code depth operands : List Bool) :
    step program (cfg (some 5) v p op (b :: code) depth operands) =
      some (cfg (some 6) b true op code depth operands) := by
  simp [step, cfg, execInstr, readRegs]

theorem operation_present (b op : Bool) (code depth operands : List Bool) :
    step program (cfg (some 6) b true op code depth operands) =
      some (cfg (some 7) b true op code depth operands) := by
  simp [step, cfg, execInstr]

theorem operation_copy (b op : Bool) (code depth operands : List Bool) :
    step program (cfg (some 7) b true op code depth operands) =
      some (cfg (some 8) b true b code depth operands) := by
  simp [step, cfg, execInstr]

theorem first_operand_pop (a v p op : Bool) (code depth operands : List Bool) :
    step program (cfg (some 8) v p op code (a :: depth) operands) =
      some (cfg (some 9) a true op code depth operands) := by
  simp [step, cfg, execInstr, readRegs]

theorem first_operand_present (a op : Bool) (code depth operands : List Bool) :
    step program (cfg (some 9) a true op code depth operands) =
      some (cfg (some 10) a true op code depth operands) := by
  simp [step, cfg, execInstr]

theorem second_operand_pop (a v p op : Bool) (code depth operands : List Bool) :
    step program (cfg (some 10) v p op code (a :: depth) operands) =
      some (cfg (some 11) a true op code depth operands) := by
  simp [step, cfg, execInstr, readRegs]

theorem second_operand_present (a op : Bool) (code depth operands : List Bool) :
    step program (cfg (some 11) a true op code depth operands) =
      some (cfg (some 12) a true op code depth operands) := by
  simp [step, cfg, execInstr]

theorem result_set (a op : Bool) (code depth operands : List Bool) :
    step program (cfg (some 12) a true op code depth operands) =
      some (cfg (some 13) true true op code depth operands) := by
  simp [step, cfg, execInstr]

theorem result_push (op : Bool) (code depth operands : List Bool) :
    step program (cfg (some 13) true true op code depth operands) =
      some (cfg (some 14) true true op code (true :: depth) operands) := by
  simp [step, cfg, execInstr]

theorem operation_dispatch (op : Bool) (code depth operands : List Bool) :
    step program (cfg (some 14) true true op code depth operands) =
      some (cfg (some (if op then mulService else addService)) true true op code depth operands) := by
  simp [step, cfg, execInstr]

/-- Thirteen actual transitions prepare either binary operation and check depth two. -/
theorem prepare_binary_trace (b a₀ a₁ v p op : Bool) (code depth operands : List Bool) :
    Trace program 13
      (cfg (some 0) v p op (true :: b :: code) (a₀ :: a₁ :: depth) operands)
      (cfg (some (if b then mulService else addService)) true true b code (true :: depth) operands) :=
  .cons (tag_pop true v p op (b :: code) (a₀ :: a₁ :: depth) operands)
    (.cons (tag_present true op (b :: code) (a₀ :: a₁ :: depth) operands)
      (.cons (binary_tag op (b :: code) (a₀ :: a₁ :: depth) operands)
        (.cons (operation_pop b true true op code (a₀ :: a₁ :: depth) operands)
          (.cons (operation_present b op code (a₀ :: a₁ :: depth) operands)
            (.cons (operation_copy b op code (a₀ :: a₁ :: depth) operands)
              (.cons (first_operand_pop a₀ b true b code (a₁ :: depth) operands)
                (.cons (first_operand_present a₀ b code (a₁ :: depth) operands)
                  (.cons (second_operand_pop a₁ a₀ true b code depth operands)
                    (.cons (second_operand_present a₁ b code depth operands)
                      (.cons (result_set a₁ b code depth operands)
                        (.cons (result_push b code depth operands)
                          (.cons (operation_dispatch b code (true :: depth) operands) (.refl _)))))))))))))

/-- Empty code is a completed instruction stream, not a malformed tag. -/
theorem eof_trace (v p op : Bool) (depth operands : List Bool) :
    Trace program 2 (cfg (some 0) v p op [] depth operands)
      (cfg (some doneExit) false false op [] depth operands) := by
  refine .cons (b := cfg (some 1) false false op [] depth operands) ?_ ?_
  · simp [step, cfg, execInstr, readRegs]
  · refine .cons ?_ (.refl _)
    simp [step, cfg, execInstr]

/-! ## Serialization of the existing postfix instruction type -/

/-! ## Literal-push service with the framed-list operand ABI -/

private theorem cfg_ext {r s l : ℕ} {a b : Cfg r s l}
    (hp : a.pc = b.pc) (hr : a.regs = b.regs) (hs : a.stacks = b.stacks) : a = b := by
  cases a; cases b; simp_all

theorem parserRegister_injective : Function.Injective parserRegister := by
  intro a b h
  exact Fin.ext (congrArg (fun i : Fin 3 => i.val) h)

theorem parserStack_injective : Function.Injective parserStack := by decide

theorem literalService_parser_code :
    ProgramLinking.CodeEmbedding ParserProgram.frameProgram literalService
      parserRegister parserStack parserLabel (some 7) := by
  intro pc
  simp [literalService, parserLabel]

private theorem embed_parser_cfg (pc : Option (Fin 7)) (v p op : Bool)
    (code depth operands scratch : List Bool) :
    ProgramLinking.embedCfg parserRegister parserStack parserLabel (some 7)
      (cfg4 none false false op [] depth operands [])
      (ParserProgram.cfg pc v p code scratch) =
    cfg4 (ProgramLinking.relocatePc parserLabel (some 7) pc) v p op code depth operands scratch := by
  apply cfg_ext
  · rfl
  · funext i
    fin_cases i
    · change Function.extend parserRegister (ParserProgram.pair v p)
        (triple false false op) (parserRegister 0) = v
      rw [parserRegister_injective.extend_apply]
      rfl
    · change Function.extend parserRegister (ParserProgram.pair v p)
        (triple false false op) (parserRegister 1) = p
      rw [parserRegister_injective.extend_apply]
      rfl
    · change Function.extend parserRegister (ParserProgram.pair v p)
        (triple false false op) 2 = op
      rw [Function.extend_apply' _ _ _ (by decide : ¬ ∃ i, parserRegister i = 2)]
      rfl
  · funext i
    fin_cases i
    · change Function.extend parserStack (ParserProgram.pair code scratch)
        (quadruple [] depth operands []) (parserStack 0) = code
      rw [parserStack_injective.extend_apply]
      rfl
    · change Function.extend parserStack (ParserProgram.pair code scratch)
        (quadruple [] depth operands []) 1 = depth
      rw [Function.extend_apply' _ _ _ (by decide : ¬ ∃ i, parserStack i = 1)]
      rfl
    · change Function.extend parserStack (ParserProgram.pair code scratch)
        (quadruple [] depth operands []) 2 = operands
      rw [Function.extend_apply' _ _ _ (by decide : ¬ ∃ i, parserStack i = 2)]
      rfl
    · change Function.extend parserStack (ParserProgram.pair code scratch)
        (quadruple [] depth operands []) (parserStack 1) = scratch
      rw [parserStack_injective.extend_apply]
      rfl

/-- Reuse the measured parser trace through actual instruction-table relocation. -/
theorem literalService_parse_trace (bits rest depth operands scratch : List Bool)
    (v p op : Bool) :
    Trace literalService (6 * bits.length + 4)
      (cfg4 (some 0) v p op (Encoding.frame bits ++ rest) depth operands scratch)
      (cfg4 (some 7) false true op rest depth operands (bits.reverse ++ scratch)) := by
  have h := ProgramLinking.relocate_trace ParserProgram.frameProgram literalService
    parserRegister parserStack parserLabel (some 7)
    (cfg4 none false false op [] depth operands [])
    parserRegister_injective parserStack_injective literalService_parser_code
    (ParserProgram.frame_trace bits rest scratch v p)
  rw [embed_parser_cfg, embed_parser_cfg] at h
  have hz : parserLabel (0 : Fin 7) = (0 : Fin 17) := by
    apply Fin.ext
    rfl
  simpa only [ProgramLinking.relocatePc, hz] using h

/-- Complete literal service: consume one frame and push a framed list item. -/
theorem literalService_trace (bits rest depth operands : List Bool) (v p op : Bool) :
    Trace literalService (11 * bits.length + 11)
      (cfg4 (some 0) v p op (Encoding.frame bits ++ rest) depth operands [])
      (cfg4 none true false op rest depth (true :: (Encoding.frame bits ++ operands)) []) := by
  have parse := literalService_parse_trace bits rest depth operands [] v p op
  have encode := literalService_encode_trace bits rest depth operands false true op
  simp only [List.append_nil] at parse
  have h := parse.trans encode
  have hn : (6 * bits.length + 4) + (5 * bits.length + 7) = 11 * bits.length + 11 := by omega
  simpa only [hn] using h

end SubexponentialSAT.SubexpPostfixControl

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpPostfixInterpreter
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FiniteField.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.StructuredProgram.siteFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# A finite postfix interpreter with linked arithmetic services

The interpreter contains the concrete tag dispatcher and literal loader, two
initialization instructions, and the supplied finite arithmetic instruction
tables. Arithmetic correctness is required as a local Boolean-machine trace
contract; an arithmetic operation is never added to the instruction language.
-/

namespace SubexponentialSAT.SubexpPostfixInterpreter

open BitProgram
open SubexpPostfixControl

variable {r s a b : ℕ}

theorem castAdd_injective (m n : ℕ) : Function.Injective (@Fin.castAdd m n) := by
  intro x y h
  exact Fin.ext (congrArg (fun i : Fin (m + n) => i.val) h)

theorem extend_castAdd {m n : ℕ} {α : Type*} (f : Fin m → α) (z : α) :
    Function.extend (Fin.castAdd n) f (fun _ => z) =
      Fin.addCases f (fun _ : Fin n => z) := by
  funext i
  refine Fin.addCases ?_ ?_ i
  · intro j
    simpa using (castAdd_injective m n).extend_apply f (fun _ => z) j
  · intro j
    rw [Function.extend_apply' _ _ _ ?_]
    · simp
    · rintro ⟨k, hk⟩
      have hv := congrArg Fin.val hk
      change k.val = m + j.val at hv
      omega

private theorem quad_three (code depth operands : List Bool) :
    quadruple code depth operands [] =
      Fin.addCases (motive := fun _ : Fin (3 + 1) => List Bool)
        (triple code depth operands) (fun _ : Fin 1 => []) := by
  first | done | (funext i; fin_cases i <;> rfl)

theorem extend_castAdd_frame {m n : ℕ} {α : Type*} (f f0 : Fin m → α) (g : Fin n → α) :
    Function.extend (Fin.castAdd n) f (Fin.addCases f0 g) = Fin.addCases f g := by
  funext i
  refine Fin.addCases ?_ ?_ i
  · intro j
    simpa using (castAdd_injective m n).extend_apply f (Fin.addCases f0 g) j
  · intro j
    rw [Function.extend_apply' _ _ _ ?_]
    · simp
    · rintro ⟨v, hv⟩
      have h := congrArg Fin.val hv
      change v.val = m + j.val at h
      omega

theorem extend_two_castAdd_frame {m n k : ℕ} {α : Type*}
    (f f0 : Fin m → α) (g : Fin n → α) (h : Fin k → α) :
    Function.extend (fun i => Fin.castAdd k (Fin.castAdd n i)) f
      (Fin.addCases (Fin.addCases f0 g) h) = Fin.addCases (Fin.addCases f g) h := by
  have hi : Function.Injective (fun i => Fin.castAdd k (Fin.castAdd n i)) :=
    (castAdd_injective (m + n) k).comp (castAdd_injective m n)
  funext i
  refine Fin.addCases ?_ ?_ i
  · intro j
    refine Fin.addCases ?_ ?_ j
    · intro v
      simpa only [Function.comp_apply, Fin.addCases_left] using
        hi.extend_apply f (Fin.addCases (Fin.addCases f0 g) h) v
    · intro v
      rw [Function.extend_apply' _ _ _ ?_]
      · simp
      · rintro ⟨w, hw⟩
        have he := congrArg Fin.val hw
        change w.val = m + v.val at he
        omega
  · intro j
    rw [Function.extend_apply' _ _ _ ?_]
    · simp
    · rintro ⟨v, hv⟩
      have he := congrArg Fin.val hv
      change v.val = m + n + j.val at he
      omega

private theorem cfg_ext {R S L : ℕ} {x y : Cfg R S L}
    (hp : x.pc = y.pc) (hr : x.regs = y.regs) (hs : x.stacks = y.stacks) : x = y := by
  cases x; cases y; simp_all

theorem embed_cfg4 {l L : ℕ} (context : Fin s → List Bool)
    (label : Fin l → Fin L) (ret : Option (Fin L))
    (pc : Option (Fin l)) (v p op : Bool) (code depth operands : List Bool) :
    ProgramLinking.embedCfg (@register r) (@stack s) label ret
      (cfg (r := r) (s := s) none false false false [] [] [] context)
      (cfg4 pc v p op code depth operands []) =
    cfg (ProgramLinking.relocatePc label ret pc) v p op code depth operands context := by
  apply cfg_ext
  · rfl
  · change Function.extend (Fin.castAdd r) (triple v p op) _ = _
    have hf : (cfg (r := r) (s := s) (l := L) none false false false [] [] [] context).regs =
        fun _ => false := by
      funext i
      refine Fin.addCases ?_ ?_ i
      · intro j; fin_cases j <;> rfl
      · intro j; simp [cfg]
    rw [hf]
    exact extend_castAdd _ _
  · exact extend_castAdd_frame _ _ _

theorem embed_control_cfg {L : ℕ} (context : Fin s → List Bool)
    (label : Fin 20 → Fin L) (ret : Option (Fin L))
    (pc : Option (Fin 20)) (v p op : Bool) (code depth operands : List Bool) :
    ProgramLinking.embedCfg (@register r) (fun i => stack (Fin.castAdd 1 i)) label ret
      (cfg (r := r) (s := s) none false false false [] [] [] context)
      (SubexpPostfixControl.cfg pc v p op code depth operands) =
    cfg (ProgramLinking.relocatePc label ret pc) v p op code depth operands context := by
  apply cfg_ext
  · rfl
  · change Function.extend (Fin.castAdd r) (triple v p op) _ = _
    have hf : (cfg (r := r) (s := s) (l := L) none false false false [] [] [] context).regs =
        fun _ => false := by
      funext i
      refine Fin.addCases ?_ ?_ i
      · intro j; fin_cases j <;> rfl
      · intro j; simp [cfg]
    rw [hf]
    exact extend_castAdd _ _
  · change Function.extend (fun i => Fin.castAdd s (Fin.castAdd 1 i))
      (triple code depth operands) (Fin.addCases (quadruple [] [] [] []) context) = _
    simp only [cfg, quad_three]
    exact extend_two_castAdd_frame _ _ _ _

variable (add : Program (3 + r) (4 + s) a) (mul : Program (3 + r) (4 + s) b)

theorem bootProgram_trace (code : List Bool) :
    Trace bootProgram 2 (cfg4 (some 0) false false false code [] [] [])
      (cfg4 (some 2) false false false code [] [false] []) := by
  refine .cons (b := cfg4 (some 1) false false false code [] [] []) ?_ ?_
  · simp [step, execInstr, cfg4]
  · refine .cons ?_ (.refl _)
    simp [step, execInstr, cfg4]

end SubexponentialSAT.SubexpPostfixInterpreter

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpPostfixGlobal
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Shared-machine port adapter for the concrete postfix interpreter

The shared machine uses code/depth/operand/scratch stacks 26/28/27/29.
A fixed permutation installs the proved interpreter there while accepting
arithmetic service tables already written for the shared 16-register,
128-stack machine. Port renaming adds no machine transitions.
-/

namespace SubexponentialSAT.SubexpPostfixGlobal

open BitProgram
open SubexpPostfixInterpreter

theorem embedCfg_reindex {r s l : ℕ} (e : Equiv.Perm (Fin s))
    (frame c : Cfg r s l) :
    ProgramLinking.embedCfg id e id none frame c = reindexCfg e c := by
  cases c with
  | mk pc regs stk =>
    have hs : Function.extend e stk frame.stacks = fun i => stk (e.symm i) := by
      funext i
      rw [← e.apply_symm_apply i, e.injective.extend_apply]
      simp
    cases pc <;> simp [ProgramLinking.embedCfg, ProgramLinking.relocatePc, reindexCfg, hs]

theorem reindex_runsIn {r s l n : ℕ} (p : Program r s l) (e : Equiv.Perm (Fin s))
    {c d : Cfg r s l} (h : RunsIn p n c d) :
    RunsIn (ProgramLinking.liftProgram p id e) n (reindexCfg e c) (reindexCfg e d) := by
  have hl := ProgramLinking.liftProgram_runsIn p id e (reindexCfg e c)
    Function.injective_id e.injective h
  simpa only [embedCfg_reindex] using hl

end SubexponentialSAT.SubexpPostfixGlobal

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpProjectedInterpreter
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# A finite postfix interpreter with a real literal-projection call

The literal bytes are parsed and pushed by the concrete loader, then passed to
an actual finite projection service before dispatch resumes. Arithmetic and
projection contracts refer to traces of supplied Boolean instruction tables.
-/

namespace SubexponentialSAT.SubexpProjectedInterpreter

open BitProgram
open SubexpPostfixControl (triple cfg4 controlLabel literalLabel pushLoopProgram
  literalService serializeCode serializeInstr operandDepth)
open SubexpPostfixInterpreter (register stack cfg castAdd_injective embed_cfg4
  embed_control_cfg bootProgram bootProgram_trace )

variable {r s a b c : ℕ}

variable (add : Program (3 + r) (4 + s) a) (mul : Program (3 + r) (4 + s) b)
  (loader : Program (3 + r) (4 + s) c)

theorem program_base_code (pc : Fin 37) (h16 : pc ≠ 16) (h17 : pc ≠ 17) (h36 : pc ≠ 36) :
    (program add mul loader).code (baseLabel pc) =
      ProgramLinking.relocateInstr register stack baseLabel none (pushLoopProgram.code pc) := by
  simp [program, baseLabel, h16, h17, h36]

theorem program_add_code : ProgramLinking.CodeEmbedding add (program add mul loader)
    id id addLabel (some (baseLabel 0)) := by
  intro pc
  simp [program, addLabel]

theorem program_mul_code : ProgramLinking.CodeEmbedding mul (program add mul loader)
    id id mulLabel (some (baseLabel 0)) := by
  intro pc
  simp [program, mulLabel]

theorem program_load_code : ProgramLinking.CodeEmbedding loader (program add mul loader)
    id id loadLabel (some (baseLabel 0)) := by
  intro pc
  simp [program, loadLabel]

theorem program_control_nonhalt (pc : Fin 20)
    (hp : SubexpPostfixControl.program.code pc ≠ .halt) :
    (program add mul loader).code (baseLabel (controlLabel pc)) =
      ProgramLinking.relocateInstr register (fun i => stack (Fin.castAdd 1 i))
        (fun i => baseLabel (controlLabel i)) none (SubexpPostfixControl.program.code pc) := by
  fin_cases pc <;> first | rfl | simp [] at hp

/-- The loader's final halt now jumps into the supplied projection table. -/
theorem program_literal_code : ProgramLinking.CodeEmbedding literalService (program add mul loader)
    register stack (fun i => baseLabel (literalLabel i)) (some (loadLabel loader.entry)) := by
  intro pc
  fin_cases pc <;> rfl

theorem prepare_literal_trace (context : Fin s → List Bool)
    (code depth operands : List Bool) (v p op : Bool) :
    Trace (program add mul loader) 6
      (cfg (some (baseLabel 0)) v p op (false :: code) depth operands context)
      (cfg (some (baseLabel 20)) true true op code (true :: depth) operands context) := by
  have h := ProgramLinking.relocate_trace_before_halt SubexpPostfixControl.program
    (program add mul loader) register (fun i => stack (Fin.castAdd 1 i))
    (fun i => baseLabel (controlLabel i)) none
    (cfg none false false false [] [] [] context)
    (castAdd_injective 3 r) ((castAdd_injective 4 s).comp (castAdd_injective 3 1))
    (program_control_nonhalt add mul loader)
    (SubexpPostfixControl.prepare_push_trace v p op code depth operands)
    (by simp [SubexpPostfixControl.cfg])
  rw [embed_control_cfg, embed_control_cfg] at h
  have hc : Trace (program add mul loader) 1
      (cfg (some (baseLabel 15)) true true op code (true :: depth) operands context)
      (cfg (some (baseLabel 20)) true true op code (true :: depth) operands context) := by
    refine .cons ?_ (.refl _)
    change some (execInstr ((program add mul loader).code (baseLabel 15)) _) = _
    rfl
  exact h.trans hc

/-- Parse all literal bytes and enter projection with its raw payload on top. -/
theorem raw_push_trace (context : Fin s → List Bool)
    (bits rest depth operands : List Bool) (v p op : Bool) :
    Trace (program add mul loader) (11 * bits.length + 17)
      (cfg (some (baseLabel 0)) v p op (false :: (Encoding.frame bits ++ rest)) depth operands context)
      (cfg (some (loadLabel loader.entry)) true false op rest (true :: depth)
        (true :: (Encoding.frame bits ++ operands)) context) := by
  have hl := ProgramLinking.relocate_trace literalService (program add mul loader)
    register stack (fun i => baseLabel (literalLabel i)) (some (loadLabel loader.entry))
    (cfg none false false false [] [] [] context)
    (castAdd_injective 3 r) (castAdd_injective 4 s) (program_literal_code add mul loader)
    (SubexpPostfixControl.literalService_trace bits rest (true :: depth) operands true true op)
  rw [embed_cfg4, embed_cfg4] at hl
  have h := (prepare_literal_trace add mul loader context (Encoding.frame bits ++ rest)
    depth operands v p op).trans hl
  convert h using 1
  · omega
  · simp [ProgramLinking.relocatePc]

theorem binary_prepare_trace (context : Fin s → List Bool)
    (isMul : Bool) (code operands : List Bool)
    (depth : List Bool) (v p op : Bool) :
    Trace (program add mul loader) 13
      (cfg (some (baseLabel 0)) v p op (true :: isMul :: code)
        (true :: true :: depth) operands context)
      (cfg (some (baseLabel (if isMul then 17 else 16))) true true isMul
        code (true :: depth) operands context) := by
  have h := ProgramLinking.relocate_trace_before_halt SubexpPostfixControl.program (program add mul loader)
    register (fun i => stack (Fin.castAdd 1 i)) (fun i => baseLabel (controlLabel i)) none
    (cfg none false false false [] [] [] context)
    (castAdd_injective 3 r) ((castAdd_injective 4 s).comp (castAdd_injective 3 1))
    (program_control_nonhalt add mul loader)
    (SubexpPostfixControl.prepare_binary_trace isMul true true v p op code depth operands) (by simp [SubexpPostfixControl.cfg])
  rw [embed_control_cfg, embed_control_cfg] at h
  cases isMul <;> exact h

theorem add_call_step (context : Fin s → List Bool) (code depth operands : List Bool) :
    step (program add mul loader) (cfg (some (baseLabel 16)) true true false code depth operands context) =
      some (cfg (some (addLabel add.entry)) true true false code depth operands context) := by
  simp [step, cfg, program, baseLabel, execInstr]

theorem mul_call_step (context : Fin s → List Bool) (code depth operands : List Bool) :
    step (program add mul loader) (cfg (some (baseLabel 17)) true true true code depth operands context) =
      some (cfg (some (mulLabel mul.entry)) true true true code depth operands context) := by
  simp [step, cfg, program, baseLabel, execInstr]

theorem boot_nonhalt (pc : Fin 3) (hp : bootProgram.code pc ≠ .halt) :
    (program add mul loader).code (bootMap pc) =
      ProgramLinking.relocateInstr register stack bootMap none (bootProgram.code pc) := by
  fin_cases pc <;> first | rfl | simp [] at hp

theorem boot_trace (context : Fin s → List Bool) (code : List Bool) :
    Trace (program add mul loader) 2
      (cfg (some (program add mul loader).entry) false false false code [] [] context)
      (cfg (some (baseLabel 0)) false false false code [] [false] context) := by
  have h := ProgramLinking.relocate_trace_before_halt bootProgram (program add mul loader)
    register stack bootMap none (cfg none false false false [] [] [] context)
    (castAdd_injective 3 r) (castAdd_injective 4 s)
    (boot_nonhalt add mul loader) (bootProgram_trace code) (by simp [])
  rw [embed_cfg4, embed_cfg4] at h
  exact h

theorem finish_trace (context : Fin s → List Bool) (depth operands : List Bool) (v p op : Bool) :
    Trace (program add mul loader) 3
      (cfg (some (baseLabel 0)) v p op [] depth operands context)
      (cfg none false false op [] depth operands context) := by
  have h := ProgramLinking.relocate_trace_before_halt SubexpPostfixControl.program (program add mul loader)
    register (fun i => stack (Fin.castAdd 1 i)) (fun i => baseLabel (controlLabel i)) none
    (cfg none false false false [] [] [] context)
    (castAdd_injective 3 r) ((castAdd_injective 4 s).comp (castAdd_injective 3 1))
    (program_control_nonhalt add mul loader) (SubexpPostfixControl.eof_trace v p op depth operands)
    (by simp [SubexpPostfixControl.cfg])
  rw [embed_control_cfg, embed_control_cfg] at h
  have hc : (program add mul loader).code (baseLabel 18) = .halt := by
    rw [program_base_code add mul loader 18 (by decide) (by decide) (by decide)]
    rfl
  have hs : Trace (program add mul loader) 1
      (cfg (some (baseLabel 18)) false false op [] depth operands context)
      (cfg none false false op [] depth operands context) := by
    refine .cons ?_ (.refl _)
    change some (execInstr ((program add mul loader).code (baseLabel 18)) _) = _
    rw [hc]
    rfl
  exact h.trans hs


end SubexponentialSAT.SubexpProjectedInterpreter

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpProjectedExecution
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Projected postfix execution

The compiled source contains the original raw literals. Each complete push
calls the finite projection table; the resulting value is therefore
`(e.map project).eval`. The induction tracks the entire remaining source and
operand list, and charges actual service trace bounds at every node.
-/

namespace SubexponentialSAT.SubexpProjectedInterpreter

open BitProgram
open SubexpPostfixControl (serializeCode serializeInstr operandDepth)
open SubexpPostfixInterpreter (cfg )

variable {r s a b c : ℕ}

theorem Validity.eval_valid {R : Type*} [Add R] [Mul R] {valid : R → Prop} {project : R → R}
    (h : Validity valid project) (e : Algorithm.Expr R) : valid (e.map project).eval := by
  induction e with
  | lit x => exact h.load_valid x
  | add e f he hf => exact h.add_valid _ _ he hf
  | mul e f he hf => exact h.mul_valid _ _ he hf

variable (add : Program (3 + r) (4 + s) a) (mul : Program (3 + r) (4 + s) b)
  (loader : Program (3 + r) (4 + s) c)

theorem push_instruction {R : Type*} (encode : R → List Bool) (project : R → R)
    (loadBound : R → ℕ) (context : Fin s → List Bool)
    (hload : LoadImplements encode project loader loadBound context)
    (x : R) (xs : List R) (code depth : List Bool) (v p op : Bool) :
    RunsIn (program add mul loader) (11 * (encode x).length + 17 + loadBound x)
      (cfg (some (baseLabel 0)) v p op (false :: (Encoding.frame (encode x) ++ code)) depth
        (Encoding.encodeList encode xs) context)
      (cfg (some (baseLabel 0)) false false false code (true :: depth)
        (Encoding.encodeList encode (project x :: xs)) context) := by
  obtain ⟨n, hn, ht⟩ := hload x xs code (true :: depth) op
  have hs := ProgramLinking.relocate_trace loader (program add mul loader) id id loadLabel
    (some (baseLabel 0)) (cfg none false false false [] [] [] context)
    Function.injective_id Function.injective_id (program_load_code add mul loader) ht
  simp only [ProgramLinking.embedCfg_id, ProgramLinking.relabelCfg,
    ProgramLinking.relocatePc, cfg] at hs
  have hp := raw_push_trace add mul loader context (encode x) code depth
    (Encoding.encodeList encode xs) v p op
  refine ⟨11 * (encode x).length + 17 + n, by omega, ?_⟩
  exact hp.trans hs

section Execution

variable {R : Type*} [Add R] [Mul R] (encode : R → List Bool)
variable (addBound mulBound : R → R → ℕ) (context : Fin s → List Bool) (valid : R → Prop)
variable (hadd : ImplementsOn valid encode (· + ·) false add addBound context)
variable (hmul : ImplementsOn valid encode (· * ·) true mul mulBound context)

include hadd in
omit [Mul R] in
theorem add_instruction (x y : R) (hx : valid x) (hy : valid y) (xs : List R) (code depth : List Bool) (v p op : Bool) :
    RunsIn (program add mul loader) (14 + addBound x y)
      (cfg (some (baseLabel 0)) v p op (true :: false :: code) (true :: true :: depth)
        (Encoding.encodeList encode (y :: x :: xs)) context)
      (cfg (some (baseLabel 0)) false false false code (true :: depth)
        (Encoding.encodeList encode ((x + y) :: xs)) context) := by
  obtain ⟨n, hn, ht⟩ := hadd x y hx hy xs code (true :: depth)
  have hs := ProgramLinking.relocate_trace add (program add mul loader) id id addLabel
    (some (baseLabel 0)) (cfg none false false false [] [] [] context)
    Function.injective_id Function.injective_id (program_add_code add mul loader) ht
  simp only [ProgramLinking.embedCfg_id, ProgramLinking.relabelCfg,
    ProgramLinking.relocatePc, cfg] at hs
  have hc : Trace (program add mul loader) 1
      (cfg (some (baseLabel 16)) true true false code (true :: depth)
        (Encoding.encodeList encode (y :: x :: xs)) context)
      (cfg (some (addLabel add.entry)) true true false code (true :: depth)
        (Encoding.encodeList encode (y :: x :: xs)) context) :=
    .cons (add_call_step add mul loader context code _ _) (.refl _)
  have hp := binary_prepare_trace add mul loader context false code
    (Encoding.encodeList encode (y :: x :: xs)) depth v p op
  have h := (hp.trans hc).trans hs
  refine ⟨13 + 1 + n, by omega, ?_⟩
  exact h

include hmul in
omit [Add R] in
theorem mul_instruction (x y : R) (hx : valid x) (hy : valid y) (xs : List R) (code depth : List Bool) (v p op : Bool) :
    RunsIn (program add mul loader) (14 + mulBound x y)
      (cfg (some (baseLabel 0)) v p op (true :: true :: code) (true :: true :: depth)
        (Encoding.encodeList encode (y :: x :: xs)) context)
      (cfg (some (baseLabel 0)) false false false code (true :: depth)
        (Encoding.encodeList encode ((x * y) :: xs)) context) := by
  obtain ⟨n, hn, ht⟩ := hmul x y hx hy xs code (true :: depth)
  have hs := ProgramLinking.relocate_trace mul (program add mul loader) id id mulLabel
    (some (baseLabel 0)) (cfg none false false false [] [] [] context)
    Function.injective_id Function.injective_id (program_mul_code add mul loader) ht
  simp only [ProgramLinking.embedCfg_id, ProgramLinking.relabelCfg,
    ProgramLinking.relocatePc, cfg] at hs
  have hc : Trace (program add mul loader) 1
      (cfg (some (baseLabel 17)) true true true code (true :: depth)
        (Encoding.encodeList encode (y :: x :: xs)) context)
      (cfg (some (mulLabel mul.entry)) true true true code (true :: depth)
        (Encoding.encodeList encode (y :: x :: xs)) context) :=
    .cons (mul_call_step add mul loader context code _ _) (.refl _)
  have hp := binary_prepare_trace add mul loader context true code
    (Encoding.encodeList encode (y :: x :: xs)) depth v p op
  have h := (hp.trans hc).trans hs
  refine ⟨13 + 1 + n, by omega, ?_⟩
  exact h

variable (project : R → R) (loadBound : R → ℕ)
variable (hload : LoadImplements encode project loader loadBound context)
variable (hvalid : Validity valid project)

include hadd hmul hload hvalid in
/-- Every source literal is projected, including a single-literal expression.
All source suffix bytes, lower operands, and fixed context are unchanged. -/
theorem compile_runsIn (e : Algorithm.Expr R) (suffix : List (Algorithm.Instr R))
    (xs : List R) (v p op : Bool) :
    RunsIn (program add mul loader) (exprCost encode addBound mulBound project loadBound e)
      (cfg (some (baseLabel 0)) v p op (serializeCode encode (e.compile ++ suffix))
        (operandDepth xs) (Encoding.encodeList encode xs) context)
      (cfg (some (baseLabel 0)) false false false (serializeCode encode suffix)
        (operandDepth ((e.map project).eval :: xs))
        (Encoding.encodeList encode ((e.map project).eval :: xs)) context) := by
  induction e generalizing suffix xs v p op with
  | lit x =>
      simpa [Algorithm.Expr.compile, Algorithm.Expr.map, Algorithm.Expr.eval, exprCost,
        serializeCode, serializeInstr, operandDepth, List.replicate_succ] using
        push_instruction add mul loader encode project loadBound context hload x xs
          (serializeCode encode suffix) (operandDepth xs) v p op
  | add e f he hf =>
      have h₁ := he (f.compile ++ .add :: suffix) xs v p op
      have h₂ := hf (.add :: suffix) ((e.map project).eval :: xs) false false false
      have h₃ := add_instruction add mul loader encode addBound context valid hadd
        (e.map project).eval (f.map project).eval (hvalid.eval_valid e) (hvalid.eval_valid f) xs
        (serializeCode encode suffix) (operandDepth xs) false false false
      simpa [Algorithm.Expr.compile, Algorithm.Expr.map, Algorithm.Expr.eval, exprCost,
        List.append_assoc, serializeCode, serializeInstr, operandDepth, List.replicate_succ] using
        (h₁.trans h₂).trans h₃
  | mul e f he hf =>
      have h₁ := he (f.compile ++ .mul :: suffix) xs v p op
      have h₂ := hf (.mul :: suffix) ((e.map project).eval :: xs) false false false
      have h₃ := mul_instruction add mul loader encode mulBound context valid hmul
        (e.map project).eval (f.map project).eval (hvalid.eval_valid e) (hvalid.eval_valid f) xs
        (serializeCode encode suffix) (operandDepth xs) false false false
      simpa [Algorithm.Expr.compile, Algorithm.Expr.map, Algorithm.Expr.eval, exprCost,
        List.append_assoc, serializeCode, serializeInstr, operandDepth, List.replicate_succ] using
        (h₁.trans h₂).trans h₃

include hadd hmul hload hvalid in
/-- Complete execution initializes the list marker and ends after the real EOF
halt. The final singleton contains the evaluation of projected literals. -/
theorem complete_runsIn (e : Algorithm.Expr R) :
    RunsIn (program add mul loader) (exprCost encode addBound mulBound project loadBound e + 5)
      (cfg (some (program add mul loader).entry) false false false
        (serializeCode encode e.compile) [] [] context)
      (cfg none false false false [] (operandDepth [(e.map project).eval])
        (Encoding.encodeList encode [(e.map project).eval]) context) := by
  have he := compile_runsIn add mul loader encode addBound mulBound context valid hadd hmul
    project loadBound hload hvalid e [] [] false false false
  have he' : RunsIn (program add mul loader) (exprCost encode addBound mulBound project loadBound e)
      (cfg (some (baseLabel 0)) false false false (serializeCode encode e.compile) [] [false] context)
      (cfg (some (baseLabel 0)) false false false [] (operandDepth [(e.map project).eval])
        (Encoding.encodeList encode [(e.map project).eval]) context) := by
    simpa only [List.append_nil, serializeCode, operandDepth, List.length_nil,
      List.replicate_zero, Encoding.encodeList] using he
  have hb : RunsIn (program add mul loader) 2
      (cfg (some (program add mul loader).entry) false false false
        (serializeCode encode e.compile) [] [] context)
      (cfg (some (baseLabel 0)) false false false (serializeCode encode e.compile) [] [false] context) :=
    ⟨2, le_rfl, boot_trace add mul loader context _⟩
  have hf : RunsIn (program add mul loader) 3
      (cfg (some (baseLabel 0)) false false false [] (operandDepth [(e.map project).eval])
        (Encoding.encodeList encode [(e.map project).eval]) context)
      (cfg none false false false [] (operandDepth [(e.map project).eval])
        (Encoding.encodeList encode [(e.map project).eval]) context) :=
    ⟨3, le_rfl, finish_trace add mul loader context _ _ false false false⟩
  convert (hb.trans he').trans hf using 1
  all_goals try with_reducible_and_instances rfl
  omega

end Execution

end SubexponentialSAT.SubexpProjectedInterpreter

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpRowPostfixInterpreter
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The source-row postfix interpreter on the fixed 256-stack workspace.
Only port names change; the checked dispatcher and all service transitions
are retained. Parameters such as R and the field remain encoded data. -/

namespace SubexponentialSAT.SubexpRowPostfixInterpreter

open BitProgram
open SubexpPostfixControl (serializeCode operandDepth)
open SubexpPostfixInterpreter (cfg)
open SubexpPostfixGlobal (reindexCfg reindex_runsIn)
open SubexpProjectedInterpreter (exprCost LoadImplements ImplementsOn Validity)

theorem local_binary_implements {R : Type*} {l : ℕ} (valid : R → Prop)
    (encode : R → List Bool) (operation : R → R → R) (isMul : Bool)
    (service : Program 16 256 l) (bound : R → R → ℕ) (context : Fin 252 → List Bool)
    (h : ImplementsOnGlobal valid encode operation isMul service bound context) :
    ImplementsOn (r := 13) (s := 252) valid encode operation isMul (localService service) bound context := by
  intro x y hx hy xs code depth
  have hs := reindex_runsIn service ports.symm (h x y hx hy xs code depth)
  simpa only [physicalCfg, SubexpPostfixGlobal.reindexCfg_symm, localService,
    ProgramLinking.liftProgram] using hs

theorem local_load_implements {R : Type*} {l : ℕ} (encode : R → List Bool)
    (project : R → R) (service : Program 16 256 l) (bound : R → ℕ)
    (context : Fin 252 → List Bool)
    (h : LoadImplementsGlobal encode project service bound context) :
    LoadImplements (r := 13) (s := 252) encode project (localService service) bound context := by
  intro x xs code depth op
  have hs := reindex_runsIn service ports.symm (h x xs code depth op)
  simpa only [physicalCfg, SubexpPostfixGlobal.reindexCfg_symm, localService,
    ProgramLinking.liftProgram] using hs

/-- Execution of original raw-literal source, with a concrete projection call
at every literal. The three hypotheses concern the supplied finite tables. -/
theorem global_complete_runsIn_oai {R : Type*} [Add R] [Mul R] {a b c : ℕ}
    (add : Program 16 256 a) (mul : Program 16 256 b) (loader : Program 16 256 c)
    (encode : R → List Bool) (project : R → R) (valid : R → Prop)
    (addBound mulBound : R → R → ℕ) (loadBound : R → ℕ) (context : Fin 252 → List Bool)
    (ha : ImplementsOnGlobal valid encode (· + ·) false add addBound context)
    (hm : ImplementsOnGlobal valid encode (· * ·) true mul mulBound context)
    (hl : LoadImplementsGlobal encode project loader loadBound context)
    (hvalid : Validity valid project) (e : Algorithm.Expr R) :
    RunsIn (globalProgram add mul loader) (exprCost encode addBound mulBound project loadBound e + 5)
      (physicalCfg (some (globalProgram add mul loader).entry) false false false
        (serializeCode encode e.compile) [] [] context)
      (physicalCfg none false false false [] (operandDepth [(e.map project).eval])
        (Encoding.encodeList encode [(e.map project).eval]) context) := by
  have hal := local_binary_implements valid encode (· + ·) false add addBound context ha
  have hml := local_binary_implements valid encode (· * ·) true mul mulBound context hm
  have hll := local_load_implements encode project loader loadBound context hl
  have h := SubexpProjectedInterpreter.complete_runsIn (r := 13) (s := 252)
    (localService add) (localService mul) (localService loader) encode addBound mulBound
    context valid hal hml project loadBound hll hvalid e
  exact reindex_runsIn _ ports h


end SubexponentialSAT.SubexpRowPostfixInterpreter

end OAI.Algorithms
end

theorem solution.{u_1} : type_of% @OAI.Algorithms.SubexponentialSAT.SubexpRowPostfixInterpreter.global_complete_runsIn_oai.{u_1} := @OAI.Algorithms.SubexponentialSAT.SubexpRowPostfixInterpreter.global_complete_runsIn_oai.{u_1}
