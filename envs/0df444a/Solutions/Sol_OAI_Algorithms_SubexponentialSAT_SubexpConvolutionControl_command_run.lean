-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SubexpConvolutionControl.command_run
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T04:11:19.781874+00:00
-- url     : https://prove2.me/submissions/fb37ec2a-692a-4661-9dcb-7add19a2bd86

import Mathlib
import Definitions.Def_OAIQ081S067
import Definitions.Def_OAIQ081S068
import Definitions.Def_OAIQ081S081

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpConvolutionControl
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Fixed finite control for triangular, truncated convolution

Polynomial coefficients occupy equal-width flat cells. Both input arrays have
D cells. The left array is consumed; the right array is retained. The output
array is preallocated with D zero cells. Unary loop counters and indices are
runtime stacks, so changing D does not change this control program.

The scalar product-and-accumulate command is inserted as a fixed command. Its
concrete implementation uses the quartic multiplier and the persistent cell
updater; it is never a semantic-function instruction.
-/

namespace SubexponentialSAT.SubexpConvolutionControl

open BitProgram StructuredCalls SubexpScanPrimitives

theorem appendIndex_eval (d : Data) (index : Fin 256) :
    Eval (appendIndex index) 2 d (afterAppendIndex d index) := by
  have h₁ := StructuredProgram.Eval.atom (StructuredProgram.Atom.set 0 false) d
  have h₂ := StructuredProgram.Eval.atom (StructuredProgram.Atom.push index 0)
    ((StructuredProgram.Atom.set 0 false).eval d)
  simpa [appendIndex, seq, afterAppendIndex, StructuredProgram.Atom.eval,
    StructuredProgram.Atom.instr, StructuredProgram.State.ofCfg,
    StructuredProgram.State.withPC, execInstr] using Eval.seq (.base h₁) (.base h₂)

end SubexponentialSAT.SubexpConvolutionControl

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpConvolutionIteration
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Unary runtime-loop execution used by both convolution loops. The body
obligation contains actual executions; the loop invariant concerns physical
stacks and may include decoded coefficient arrays and their lengths. -/

namespace SubexponentialSAT.SubexpConvolutionControl

open BitProgram StructuredCalls

theorem test_eval (counter : Fin 256) (flag : Fin 16) (d : Data) :
    Eval (test counter flag) 1 d (testResult counter flag d) :=
  .base (.atom _ _)

theorem testResult_flag (counter : Fin 256) (flag : Fin 16) (d : Data) :
    (testResult counter flag d).regs flag = decide (0 < (d.stacks counter).length) := by
  cases h : d.stacks counter with
  | nil => simp [testResult, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
      StructuredProgram.State.ofCfg, execInstr,
      readRegs, h]
  | cons b bs => simp [testResult, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
      StructuredProgram.State.ofCfg, execInstr,
      readRegs, h]

theorem unaryLoop_eval (counter : Fin 256) (flag : Fin 16)
    (body : Code) (Inv : ℕ → (Fin 256 → List Bool) → Prop) (cost : ℕ → ℕ)
    (hcount : ∀ fuel stk, Inv fuel stk → (stk counter).length = fuel)
    (hstep : ∀ fuel (d : Data), Inv (fuel + 1) d.stacks →
      ∃ n e, Eval body n d e ∧ n ≤ cost (fuel + 1) ∧ Inv fuel e.stacks)
    (fuel : ℕ) :
    ∀ d : Data, Inv fuel d.stacks → d.regs flag = decide (0 < fuel) →
      ∃ n e, Eval (unaryLoop counter flag body) n d e ∧
        n ≤ unaryBudget cost fuel ∧ Inv 0 e.stacks := by
  induction fuel with
  | zero =>
      intro d hd hg
      exact ⟨1, d, .while_false (by simpa using hg), by rfl, hd⟩
  | succ fuel ih =>
      intro d hd hg
      obtain ⟨nb, e, hb, hnb, he⟩ := hstep fuel d hd
      have htest := test_eval counter flag e
      have he' : Inv fuel (testResult counter flag e).stacks := he
      have hflag' : (testResult counter flag e).regs flag = decide (0 < fuel) := by
        rw [testResult_flag counter flag, hcount fuel e.stacks he]
      obtain ⟨nt, f, ht, hnt, hf⟩ := ih (testResult counter flag e) he' hflag'
      refine ⟨(nb + 1) + nt + 1, f,
        .while_true (by simpa using hg) (.seq hb htest) ht, ?_, hf⟩
      simp only [unaryBudget]
      omega

/-- The initial physical peek is included in the bound. The body may change
all registers because the next peek establishes the loop guard anew. -/
theorem unaryRun_eval (counter : Fin 256) (flag : Fin 16)
    (body : Code) (Inv : ℕ → (Fin 256 → List Bool) → Prop) (cost : ℕ → ℕ)
    (hcount : ∀ fuel stk, Inv fuel stk → (stk counter).length = fuel)
    (hstep : ∀ fuel (d : Data), Inv (fuel + 1) d.stacks →
      ∃ n e, Eval body n d e ∧ n ≤ cost (fuel + 1) ∧ Inv fuel e.stacks)
    (fuel : ℕ) (d : Data) (hd : Inv fuel d.stacks) :
    ∃ n e, Eval (unaryRun counter flag body) n d e ∧
      n ≤ 1 + unaryBudget cost fuel ∧ Inv 0 e.stacks := by
  obtain ⟨n, e, he, hn, hIe⟩ := unaryLoop_eval counter flag body Inv cost hcount hstep fuel
    (testResult counter flag d) hd (by
      rw [testResult_flag counter flag, hcount fuel d.stacks hd])
  exact ⟨1 + n, e, .seq (test_eval counter flag d) he, Nat.add_le_add_left hn 1, hIe⟩

theorem unaryBudget_le (cost : ℕ → ℕ) (C fuel : ℕ)
    (hc : ∀ i, 0 < i → i ≤ fuel → cost i ≤ C) :
    unaryBudget cost fuel ≤ fuel * (C + 2) + 1 := by
  induction fuel with
  | zero => simp [unaryBudget]
  | succ fuel ih =>
      have hprev := ih (fun i hi hif => hc i hi (by omega))
      have hcur := hc (fuel + 1) (by omega) (by omega)
      simp only [unaryBudget, Nat.succ_mul]
      omega

end SubexponentialSAT.SubexpConvolutionControl

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpConvolutionStore
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Stack-only contracts for the concrete copies, fixed-width reads, and unary
counter updates in the convolution controller. Register values are genuine
outputs of the executed commands, but are unrestricted between these blocks. -/

namespace SubexponentialSAT.SubexpConvolutionControl

open BitProgram StructuredCalls SubexpScanPrimitives

theorem takeCell_run (src dst : Fin 256) (s : Store) (bits rest : List Bool)
    (hdist : Function.Injective (![104, 121, 122, src, dst] : Fin 5 → Fin 256))
    (hsrc : s src = bits ++ rest) (hcounter : s 121 = []) (htmp : s 122 = [])
    (hwidth : (s 104).length = bits.length) :
    ExecutesIn (takeCell src dst) (14 * bits.length + 11) s
      (Function.update (Function.update s src rest) dst (bits ++ s dst)) := by
  intro regs
  refine ⟨_, readRegs regs 0 1 none, le_rfl, ?_⟩
  exact SubexpScanPrimitives.takeWord_eval (⟨regs, s⟩ : Data)
    104 121 122 src dst 0 1 hdist (by decide) bits rest hsrc hcounter htmp hwidth

theorem appendIndex_run (index : Fin 256) (s : Store) :
    ExecutesIn (appendIndex index) 2 s (Function.update s index (false :: s index)) := by
  intro regs
  exact ⟨2, Function.update regs 0 false, le_rfl, appendIndex_eval ⟨regs, s⟩ index⟩

theorem popToken_run (counter : Fin 256) (s : Store) (bit : Bool) (rest : List Bool)
    (hcounter : s counter = bit :: rest) :
    ExecutesIn (popToken counter) 1 s (Function.update s counter rest) := by
  intro regs
  refine ⟨1, readRegs regs 0 1 (some bit), le_rfl, ?_⟩
  have h := StructuredProgram.Eval.atom (StructuredProgram.Atom.pop counter 0 1)
    (⟨regs, s⟩ : Data)
  simpa [popToken, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
    StructuredProgram.State.ofCfg, StructuredProgram.State.withPC,
    execInstr, hcounter] using Eval.base h

theorem buffers_frame (base : Store) (w : Buffers) (j : Fin 256)
    (hj : ¬ ∃ i, bufferPorts i = j) : buffers base w j = base j :=
  Function.extend_apply' _ _ _ hj

theorem buffers_update (base : Store) (w : Buffers) (i : Fin 11) (v : List Bool) :
    buffers base (Function.update w i v) = Function.update (buffers base w) (bufferPorts i) v :=
  ProgramLinking.extend_update bufferPorts.injective w base i v

@[simp] theorem buffers_104 (base : Store) (w : Buffers) : buffers base w 104 = base 104 :=
  buffers_frame base w 104 (by decide)
@[simp] theorem buffers_120 (base : Store) (w : Buffers) : buffers base w 120 = base 120 :=
  buffers_frame base w 120 (by decide)
@[simp] theorem buffers_121 (base : Store) (w : Buffers) : buffers base w 121 = base 121 :=
  buffers_frame base w 121 (by decide)
@[simp] theorem buffers_122 (base : Store) (w : Buffers) : buffers base w 122 = base 122 :=
  buffers_frame base w 122 (by decide)

end SubexponentialSAT.SubexpConvolutionControl

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpConvolutionRows
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FiniteField.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The triangular convolution controller charges actual fixed-width reads,
copies, and cell writes. The local pair contract is a contract for a fixed
finite command and is instantiated by the concrete quartic/jet service. -/

namespace SubexponentialSAT.SubexpConvolutionControl

open BitProgram StructuredCalls

variable {C : Type*}

theorem encodeArray_length (encode : C → List Bool) (W : ℕ)
    (hW : ∀ x, (encode x).length = W) (xs : List C) :
    (encodeArray encode xs).length = xs.length * W := by
  induction xs with
  | nil => simp
  | cons a xs ih => simp [ih, hW, Nat.succ_mul, Nat.add_comm]

/-- One iteration of the actual inner command, including every data movement
and the physical increment of the output index. -/
theorem innerStep_run (pair : Code) (base : Store) (encode : C → List Bool)
    (add mul : C → C → C) (D W pairCost : ℕ)
    (hpair : PairSpec pair base encode add mul D pairCost)
    (hwidth : (base 104).length = W)
    (h120 : base 120 = []) (h121 : base 121 = []) (h122 : base 122 = [])
    (w : Buffers) (a b : C) (acc : List C) (rightTail cellsLeft : List Bool) (bit : Bool)
    (ha : (encode a).length = W) (hb : (encode b).length = W)
    (hlen : acc.length = D) (hi : (w 3).length < D)
    (hacc : w 2 = encodeArray encode acc) (hright : w 6 = encode b ++ rightTail)
    (hcount : w 7 = bit :: cellsLeft) (hcoef : w 8 = encode a)
    (hx : w 9 = []) (hy : w 10 = []) :
    ExecutesIn (innerStep pair) (pairCost + 21 * W + 19) (buffers base w)
      (buffers base (innerAfter w
        (encodeArray encode (TruncatedConvolution.addProduct add mul (w 3).length a b acc))
        rightTail cellsLeft)) := by
  let w₁ := Function.update w 7 cellsLeft
  let w₂ := Function.update (Function.update w₁ 6 rightTail) 10 (encode b)
  let w₃ := Function.update w₂ 9 (encode a)
  let acc' := TruncatedConvolution.addProduct add mul (w 3).length a b acc
  let w₄ := Function.update (Function.update (Function.update w₃ 9 []) 10 []) 2
    (encodeArray encode acc')
  let w₅ := Function.update w₄ 3 (false :: w₄ 3)
  have h₁ : ExecutesIn (popToken 109) 1 (buffers base w) (buffers base w₁) := by
    simpa only [w₁, buffers_update, show bufferPorts 7 = (109 : Fin 256) from rfl] using
      popToken_run 109 (buffers base w) bit cellsLeft (by simpa using hcount)
  have h₂ : ExecutesIn (takeCell 108 199) (14 * W + 11)
      (buffers base w₁) (buffers base w₂) := by
    have h := takeCell_run 108 199 (buffers base w₁) (encode b) rightTail
      (by decide) (by simpa [w₁] using hright)
      (by simpa using h121) (by simpa using h122) (by simpa [hb] using hwidth)
    simpa [w₂, buffers_update, bufferPorts, w₁, hy, hb] using h
  have h₃ : ExecutesIn (copy 110 198) (7 * W + 5) (buffers base w₂) (buffers base w₃) := by
    have h := copy_run 110 198 (buffers base w₂)
      (by decide) (by decide) (by decide) (by simpa using h120)
    simpa [w₃, buffers_update, bufferPorts, w₂, w₁, hcoef, hx, ha] using h
  have h₄ : ExecutesIn pair pairCost (buffers base w₃) (buffers base w₄) := by
    have h := hpair w₃ a b acc hlen (by simpa [w₃, w₂, w₁] using hi)
      (by simpa [w₃, w₂, w₁] using hacc) (by simp [w₃]) (by simp [w₃, w₂])
    simpa [w₄, acc', w₃, w₂, w₁] using h
  have h₅ : ExecutesIn (appendIndex 103) 2 (buffers base w₄) (buffers base w₅) := by
    simpa only [w₅, buffers_update, show bufferPorts 3 = (103 : Fin 256) from rfl,
      buffers_103] using appendIndex_run 103 (buffers base w₄)
  have hfinal : w₅ = innerAfter w (encodeArray encode acc') rightTail cellsLeft := by
    funext j
    fin_cases j <;> simp [w₅, w₄, w₃, w₂, w₁, innerAfter]
  have h := h₁.seq (h₂.seq (h₃.seq (h₄.seq h₅)))
  rw [hfinal] at h
  change ExecutesIn (innerStep pair) _ _ _ at h
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  omega

/-- The complete inner loop executes exactly the triangular row, with all
field data, scratch use, and per-pair work accounted for by actual commands. -/
theorem innerLoop_run (pair : Code) (base : Store) (encode : C → List Bool)
    (add mul : C → C → C) (D W pairCost : ℕ)
    (hpair : PairSpec pair base encode add mul D pairCost)
    (hencode : ∀ c, (encode c).length = W) (hwidth : (base 104).length = W)
    (h120 : base 120 = []) (h121 : base 121 = []) (h122 : base 122 = [])
    (w : Buffers) (a : C) (acc pending suffix : List C)
    (hlen : acc.length = D) (hacc : w 2 = encodeArray encode acc)
    (hright : w 6 = encodeArray encode (pending ++ suffix))
    (hcount : (w 7).length = pending.length) (hcoef : w 8 = encode a)
    (hx : w 9 = []) (hy : w 10 = [])
    (hi : (w 3).length + pending.length ≤ D) :
    ExecutesIn (innerLoop pair) (pending.length * (pairCost + 21 * W + 21) + 2)
      (buffers base w) (buffers base (innerDone w
        (encodeArray encode (TruncatedConvolution.row add mul a (w 3).length pending acc))
        (encodeArray encode suffix) pending.length)) := by
  let target := TruncatedConvolution.row add mul a (w 3).length pending acc
  let Good := InnerGood base encode add mul a D w target suffix pending.length
  let Inv : ℕ → Store → Prop := fun fuel stk => ∃ r, Good r fuel stk
  have hInvCount : ∀ fuel stk, Inv fuel stk → (stk 109).length = fuel := by
    intro fuel stk h
    obtain ⟨r, hr⟩ := h
    rw [hr.store_eq, buffers_109]
    exact hr.count_length
  have hStep : ∀ fuel (d : Data), Inv (fuel + 1) d.stacks →
      ∃ n e, Eval (innerStep pair) n d e ∧ n ≤ pairCost + 21 * W + 19 ∧
        Inv fuel e.stacks := by
    intro fuel d hd
    obtain ⟨r, hr⟩ := hd
    have hbs := hr.pending_length
    cases hlist : r.pending with
    | nil => simp [hlist] at hbs
    | cons b bs =>
      have hbsLen : bs.length = fuel := by simpa [hlist] using hbs
      have hcnt := hr.count_length
      cases htokens : r.work 7 with
      | nil => simp [htokens] at hcnt
      | cons bit tokens =>
        have htlen : tokens.length = fuel := by simpa [htokens] using hcnt
        let values' := TruncatedConvolution.addProduct add mul (r.work 3).length a b r.values
        let work' := innerAfter r.work (encodeArray encode values')
          (encodeArray encode (bs ++ suffix)) tokens
        let r' : RowData C := ⟨work', values', bs⟩
        have hrun := innerStep_run pair base encode add mul D W pairCost hpair hwidth h120 h121 h122
          r.work a b r.values (encodeArray encode (bs ++ suffix)) tokens bit
          (hencode a) (hencode b) hr.values_length (by have := hr.index_bound; omega)
          hr.accumulator (by simpa [hlist] using hr.right_tail) htokens hr.coefficient
          hr.operand_left hr.operand_right
        obtain ⟨n, regs', hn, he⟩ := hrun d.regs
        have hdEq : d = ⟨d.regs, buffers base r.work⟩ := by
          exact SubexpScanPrimitives.state_ext rfl hr.store_eq
        refine ⟨n, ⟨regs', buffers base work'⟩, ?_, hn, r', ?_⟩
        · rw [← hdEq] at he
          exact he
        · refine {
            store_eq := rfl
            pending_length := hbsLen
            values_length := ?_
            accumulator := ?_
            right_tail := ?_
            count_length := ?_
            coefficient := ?_
            operand_left := ?_
            operand_right := ?_
            index_bound := ?_
            index_tokens := ?_
            target_eq := ?_
            frame_left := ?_
            frame_right := ?_
            frame_row_index := ?_
            frame_row_count := ?_ }
          · simpa [r', values'] using hr.values_length
          · simp [r', work', innerAfter]
          · simp [r', work', innerAfter]
          · simpa [r', work', innerAfter] using htlen
          · simpa [r', work', innerAfter] using hr.coefficient
          · simp [r', work', innerAfter]
          · simp [r', work', innerAfter]
          · have hbound := hr.index_bound
            simp only [r', work', innerAfter, Function.update_self,
              List.length_cons]
            omega
          · have hsame : List.replicate fuel false ++ (false :: r.work 3) =
                List.replicate (fuel + 1) false ++ r.work 3 := by
              simp [List.replicate_add, List.append_assoc]
            simpa [r', work', innerAfter, hsame] using hr.index_tokens
          · simpa [r', work', innerAfter, values', hlist, TruncatedConvolution.row] using hr.target_eq
          · simpa [r', work', innerAfter] using hr.frame_left
          · simpa [r', work', innerAfter] using hr.frame_right
          · simpa [r', work', innerAfter] using hr.frame_row_index
          · simpa [r', work', innerAfter] using hr.frame_row_count
  intro regs
  have hInitial : Inv pending.length (buffers base w) := by
    refine ⟨⟨w, acc, pending⟩, ?_⟩
    exact {
      store_eq := rfl, pending_length := rfl, values_length := hlen,
      accumulator := hacc, right_tail := hright, count_length := hcount,
      coefficient := hcoef, operand_left := hx, operand_right := hy,
      index_bound := hi, index_tokens := rfl, target_eq := rfl,
      frame_left := rfl, frame_right := rfl, frame_row_index := rfl, frame_row_count := rfl }
  obtain ⟨n, e, he, hn, r, hr⟩ := unaryRun_eval 109 15 (innerStep pair) Inv
    (fun _ => pairCost + 21 * W + 19) hInvCount hStep pending.length
    ⟨regs, buffers base w⟩ hInitial
  have hnil : r.pending = [] := List.length_eq_zero_iff.mp hr.pending_length
  have hvalues : r.values = target := by simpa [hnil, TruncatedConvolution.row] using hr.target_eq
  have htokens : r.work 7 = [] := List.length_eq_zero_iff.mp hr.count_length
  have hwork : r.work = innerDone w (encodeArray encode target) (encodeArray encode suffix) pending.length := by
    funext j
    fin_cases j
    · simpa [innerDone] using hr.frame_left
    · simpa [innerDone] using hr.frame_right
    · simpa [innerDone, hvalues] using hr.accumulator
    · simpa [innerDone] using hr.index_tokens
    · simpa [innerDone] using hr.frame_row_index
    · simpa [innerDone] using hr.frame_row_count
    · simpa [innerDone, hnil] using hr.right_tail
    · simpa [innerDone] using htokens
    · simpa [innerDone, hcoef] using hr.coefficient
    · simpa [innerDone, hx] using hr.operand_left
    · simpa [innerDone, hy] using hr.operand_right
  have hstack : e.stacks = buffers base
      (innerDone w (encodeArray encode target) (encodeArray encode suffix) pending.length) := by
    rw [hr.store_eq, hwork]
  have heEq : e = ⟨e.regs, buffers base
      (innerDone w (encodeArray encode target) (encodeArray encode suffix) pending.length)⟩ := by
    exact SubexpScanPrimitives.state_ext rfl hstack
  have hbudget := unaryBudget_le (fun _ => pairCost + 21 * W + 19)
    (pairCost + 21 * W + 19) pending.length (by intros; rfl)
  have hcost : pairCost + 21 * W + 19 + 2 = pairCost + 21 * W + 21 := by omega
  rw [hcost] at hbudget
  refine ⟨n, e.regs, ?_, ?_⟩
  · omega
  · change Eval (innerLoop pair) n ⟨regs, buffers base w⟩ e at he
    rw [heEq] at he
    exact he

end SubexponentialSAT.SubexpConvolutionControl

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpConvolutionOuter
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FiniteField.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The outer triangular loop of the fixed convolution controller. Each row
copies the preserved right-hand array, consumes one left coefficient, and
executes only the still-relevant output positions. -/

namespace SubexponentialSAT.SubexpConvolutionControl

open BitProgram StructuredCalls

variable {C : Type*}

/-- One actual row of the convolution, including preparation and cleanup. -/
theorem outerStep_run (pair : Code) (base : Store) (encode : C → List Bool)
    (add mul : C → C → C) (D W pairCost : ℕ)
    (hpair : PairSpec pair base encode add mul D pairCost)
    (hencode : ∀ c, (encode c).length = W) (hwidth : (base 104).length = W)
    (h120 : base 120 = []) (h121 : base 121 = []) (h122 : base 122 = [])
    (w : Buffers) (a : C) (rest Q acc : List C) (bit : Bool) (tokens : List Bool)
    (hQ : Q.length = D) (hlen : acc.length = D)
    (hleft : w 0 = encodeArray encode (a :: rest))
    (hright : w 1 = encodeArray encode Q) (hacc : w 2 = encodeArray encode acc)
    (hcount : w 5 = bit :: tokens)
    (hindex : (w 4).length + (w 5).length ≤ D)
    (h3 : w 3 = []) (h6 : w 6 = []) (h7 : w 7 = []) (h8 : w 8 = [])
    (h9 : w 9 = []) (h10 : w 10 = []) :
    ExecutesIn (outerStep pair) (outerCost D W pairCost) (buffers base w)
      (buffers base (outerAfter w (encodeArray encode rest)
        (encodeArray encode (TruncatedConvolution.row add mul a (w 4).length
          (Q.take (w 5).length) acc)) tokens)) := by
  let r := (w 5).length
  let i := (w 4).length
  let w₁ := Function.update w 7 (w 5)
  let w₂ := Function.update w₁ 5 tokens
  let w₃ := Function.update (Function.update w₂ 0 (encodeArray encode rest)) 8 (encode a)
  let w₄ := Function.update w₃ 6 (encodeArray encode Q)
  let w₅ := Function.update w₄ 3 (w 4)
  let values := TruncatedConvolution.row add mul a i (Q.take r) acc
  let w₆ := innerDone w₅ (encodeArray encode values) (encodeArray encode (Q.drop r)) r
  let w₇ := Function.update w₆ 6 []
  let w₈ := Function.update w₇ 7 []
  let w₉ := Function.update w₈ 3 []
  let w₁₀ := Function.update w₉ 8 []
  let w₁₁ := Function.update w₁₀ 4 (false :: w₁₀ 4)
  have hrD : r ≤ D := by dsimp [r]; omega
  have hiD : i ≤ D := by dsimp [i]; omega
  have hQr : (Q.take r).length = r := by simp [List.length_take, hQ, Nat.min_eq_left hrD]
  have h₁ : ExecutesIn (copy 106 109) (7 * r + 5) (buffers base w) (buffers base w₁) := by
    simpa [w₁, r, buffers_update, bufferPorts, h7] using
      copy_run 106 109 (buffers base w) (by decide) (by decide) (by decide)
        (by simpa using h120)
  have h₂ : ExecutesIn (popToken 106) 1 (buffers base w₁) (buffers base w₂) := by
    simpa [w₂, buffers_update, bufferPorts] using
      popToken_run 106 (buffers base w₁) bit tokens (by simpa [w₁] using hcount)
  have h₃ : ExecutesIn (takeCell 100 110) (14 * W + 11)
      (buffers base w₂) (buffers base w₃) := by
    have ht := takeCell_run 100 110 (buffers base w₂) (encode a) (encodeArray encode rest)
      (by decide) (by simpa [w₂, w₁] using hleft)
      (by simpa using h121) (by simpa using h122) (by simpa [hencode] using hwidth)
    simpa [w₃, buffers_update, bufferPorts, w₂, w₁, h8, hencode] using ht
  have h₄ : ExecutesIn (copy 101 108) (7 * (D * W) + 5)
      (buffers base w₃) (buffers base w₄) := by
    have ht := copy_run 101 108 (buffers base w₃)
      (by decide) (by decide) (by decide) (by simpa using h120)
    simpa [w₄, buffers_update, bufferPorts, w₃, w₂, w₁, hright, h6,
      encodeArray_length encode W hencode, hQ] using ht
  have h₅ : ExecutesIn (copy 105 103) (7 * i + 5)
      (buffers base w₄) (buffers base w₅) := by
    have ht := copy_run 105 103 (buffers base w₄)
      (by decide) (by decide) (by decide) (by simpa using h120)
    simpa [w₅, i, buffers_update, bufferPorts, w₄, w₃, w₂, w₁, h3] using ht
  have h₆ : ExecutesIn (innerLoop pair) (r * (pairCost + 21 * W + 21) + 2)
      (buffers base w₅) (buffers base w₆) := by
    have ht := innerLoop_run pair base encode add mul D W pairCost hpair hencode hwidth
      h120 h121 h122 w₅ a acc (Q.take r) (Q.drop r) hlen
      (by simpa [w₅, w₄, w₃, w₂, w₁] using hacc)
      (by simp [w₅, w₄, List.take_append_drop])
      (by simp [w₅, w₄, w₃, w₂, w₁, hQr, r])
      (by simp [w₅, w₄, w₃])
      (by simpa [w₅, w₄, w₃, w₂, w₁] using h9)
      (by simpa [w₅, w₄, w₃, w₂, w₁] using h10)
      (by simpa [w₅, hQr, r] using hindex)
    have hi : (w₅ 3).length = (w 4).length := by
      simp [w₅, w₄]
    simpa [w₆, values, i, hQr, hi] using ht
  have h₇ : ExecutesIn (clear 108) (2 * (D * W) + 3)
      (buffers base w₆) (buffers base w₇) := by
    have ht := clear_run 108 (buffers base w₆)
    have he : (buffers base w₆ 108).length ≤ D * W := by
      have heq : buffers base w₆ 108 = encodeArray encode (Q.drop r) := by
        simp [w₆, innerDone]
      rw [heq, encodeArray_length encode W hencode, List.length_drop, hQ]
      exact Nat.mul_le_mul_right W (Nat.sub_le D r)
    have := ht.mono (Nat.add_le_add_right (Nat.mul_le_mul_left 2 he) 3)
    simpa [w₇, buffers_update, bufferPorts] using this
  have h₈ : ExecutesIn (clear 109) 3 (buffers base w₇) (buffers base w₈) := by
    simpa [w₈, buffers_update, bufferPorts, w₇, w₆, innerDone] using clear_run 109 (buffers base w₇)
  have h₉ : ExecutesIn (clear 103) (2 * D + 3) (buffers base w₈) (buffers base w₉) := by
    have ht := clear_run 103 (buffers base w₈)
    have he : (buffers base w₈ 103).length ≤ D := by
      simpa [w₈, w₇, w₆, innerDone, w₅, r, Nat.add_comm] using hindex
    have := ht.mono (Nat.add_le_add_right (Nat.mul_le_mul_left 2 he) 3)
    simpa [w₉, buffers_update, bufferPorts] using this
  have h₁₀ : ExecutesIn (clear 110) (2 * W + 3) (buffers base w₉) (buffers base w₁₀) := by
    simpa [w₁₀, buffers_update, bufferPorts, w₉, w₈, w₇, w₆, innerDone,
      w₅, w₄, w₃, hencode] using clear_run 110 (buffers base w₉)
  have h₁₁ : ExecutesIn (appendIndex 105) 2 (buffers base w₁₀) (buffers base w₁₁) := by
    simpa only [w₁₁, buffers_update, show bufferPorts 4 = (105 : Fin 256) from rfl,
      buffers_105] using appendIndex_run 105 (buffers base w₁₀)
  have hfinal : w₁₁ = outerAfter w (encodeArray encode rest) (encodeArray encode values) tokens := by
    funext j
    fin_cases j <;> simp [w₁₁, w₁₀, w₉, w₈, w₇, w₆, innerDone, w₅, w₄, w₃,
      w₂, w₁, outerAfter, h3, h6, h7, h8]
  have ht := h₁.seq (h₂.seq (h₃.seq (h₄.seq (h₅.seq (h₆.seq
    (h₇.seq (h₈.seq (h₉.seq (h₁₀.seq h₁₁)))))))))
  rw [hfinal] at ht
  change ExecutesIn (outerStep pair) _ _ _ at ht
  apply ht.mono
  have hrow := Nat.mul_le_mul_right (pairCost + 21 * W + 21) hrD
  dsimp [outerCost]
  nlinarith


/-- Actual execution of all remaining triangular rows. The proof invariant
tracks the remaining value computation and the physical unary counters. -/
theorem outerLoop_run (pair : Code) (base : Store) (encode : C → List Bool)
    (add mul : C → C → C) (D W pairCost : ℕ)
    (hpair : PairSpec pair base encode add mul D pairCost)
    (hencode : ∀ c, (encode c).length = W) (hwidth : (base 104).length = W)
    (h120 : base 120 = []) (h121 : base 121 = []) (h122 : base 122 = [])
    (w : Buffers) (P Q acc : List C) (hQ : Q.length = D) (hlen : acc.length = D)
    (hleft : w 0 = encodeArray encode P) (hright : w 1 = encodeArray encode Q)
    (hacc : w 2 = encodeArray encode acc) (hcount : (w 5).length = P.length)
    (hindex : (w 4).length + P.length ≤ D)
    (h3 : w 3 = []) (h6 : w 6 = []) (h7 : w 7 = []) (h8 : w 8 = [])
    (h9 : w 9 = []) (h10 : w 10 = []) :
    ExecutesIn (outerLoop pair) (P.length * (outerCost D W pairCost + 2) + 2)
      (buffers base w) (buffers base (outerDone w
        (encodeArray encode (TruncatedConvolution.rows add mul Q (w 4).length P.length P acc))
        P.length)) := by
  let target := TruncatedConvolution.rows add mul Q (w 4).length P.length P acc
  let Good := OuterGood base encode add mul Q D w target P.length
  let Inv : ℕ → Store → Prop := fun fuel stk => ∃ r, Good r fuel stk
  have hInvCount : ∀ fuel stk, Inv fuel stk → (stk 106).length = fuel := by
    intro fuel stk h
    obtain ⟨r, hr⟩ := h
    rw [hr.store_eq, buffers_106]
    exact hr.row_count
  have hStep : ∀ fuel (d : Data), Inv (fuel + 1) d.stacks →
      ∃ n e, Eval (outerStep pair) n d e ∧ n ≤ outerCost D W pairCost ∧
        Inv fuel e.stacks := by
    intro fuel d hd
    obtain ⟨r, hr⟩ := hd
    have hpending := hr.pending_length
    cases hlist : r.pending with
    | nil => simp [hlist] at hpending
    | cons a rest =>
      have hrest : rest.length = fuel := by simpa [hlist] using hpending
      have hcnt := hr.row_count
      cases htokens : r.work 5 with
      | nil => simp [htokens] at hcnt
      | cons bit tokens =>
        have htlen : tokens.length = fuel := by simpa [htokens] using hcnt
        let values' := TruncatedConvolution.row add mul a (r.work 4).length (Q.take (fuel + 1)) r.values
        let work' := outerAfter r.work (encodeArray encode rest) (encodeArray encode values') tokens
        let r' : RowData C := ⟨work', values', rest⟩
        have hrun := outerStep_run pair base encode add mul D W pairCost hpair hencode
          hwidth h120 h121 h122 r.work a rest Q r.values bit tokens hQ hr.values_length
          (by simpa [hlist] using hr.left) hr.right hr.accumulator htokens
          (by simpa [hr.row_count] using hr.index_bound)
          hr.index_empty hr.right_empty hr.count_empty hr.coefficient_empty
          hr.operand_left hr.operand_right
        obtain ⟨n, regs', hn, he⟩ := hrun d.regs
        have hdEq : d = ⟨d.regs, buffers base r.work⟩ :=
          SubexpScanPrimitives.state_ext rfl hr.store_eq
        refine ⟨n, ⟨regs', buffers base work'⟩, ?_, hn, r', ?_⟩
        · rw [← hdEq] at he
          simpa only [hr.row_count] using he
        · refine {
            store_eq := rfl
            pending_length := hrest
            values_length := ?_
            left := ?_
            right := ?_
            accumulator := ?_
            row_count := ?_
            index_empty := ?_
            right_empty := ?_
            count_empty := ?_
            coefficient_empty := ?_
            operand_left := ?_
            operand_right := ?_
            index_bound := ?_
            index_tokens := ?_
            target_eq := ?_ }
          · simpa [r', values'] using hr.values_length
          · simp [r', work', outerAfter]
          · simpa [r', work', outerAfter] using hr.right
          · simp [r', work', outerAfter]
          · simpa [r', work', outerAfter] using htlen
          · simpa [r', work', outerAfter] using hr.index_empty
          · simpa [r', work', outerAfter] using hr.right_empty
          · simpa [r', work', outerAfter] using hr.count_empty
          · simpa [r', work', outerAfter] using hr.coefficient_empty
          · simpa [r', work', outerAfter] using hr.operand_left
          · simpa [r', work', outerAfter] using hr.operand_right
          · have hbound := hr.index_bound
            simp only [r', work', outerAfter, Function.update_of_ne (by decide : (4 : Fin 11) ≠ 5),
              Function.update_self, List.length_cons]
            omega
          · have hsame : List.replicate fuel false ++ (false :: r.work 4) =
                List.replicate (fuel + 1) false ++ r.work 4 := by
              simp [List.replicate_add, List.append_assoc]
            simpa [r', work', outerAfter, hsame] using hr.index_tokens
          · simpa [r', work', outerAfter, values', hlist, TruncatedConvolution.rows] using hr.target_eq
  intro regs
  have hInitial : Inv P.length (buffers base w) := by
    refine ⟨⟨w, acc, P⟩, ?_⟩
    exact {
      store_eq := rfl, pending_length := rfl, values_length := hlen,
      left := hleft, right := hright, accumulator := hacc, row_count := hcount,
      index_empty := h3, right_empty := h6, count_empty := h7, coefficient_empty := h8,
      operand_left := h9, operand_right := h10, index_bound := hindex,
      index_tokens := rfl, target_eq := rfl }
  obtain ⟨n, e, he, hn, r, hr⟩ := unaryRun_eval 106 14 (outerStep pair) Inv
    (fun _ => outerCost D W pairCost) hInvCount hStep P.length
    ⟨regs, buffers base w⟩ hInitial
  have hnil : r.pending = [] := List.length_eq_zero_iff.mp hr.pending_length
  have hvalues : r.values = target := by simpa [TruncatedConvolution.rows] using hr.target_eq
  have htokens : r.work 5 = [] := List.length_eq_zero_iff.mp hr.row_count
  have hwork : r.work = outerDone w (encodeArray encode target) P.length := by
    funext j
    fin_cases j
    · simpa [outerDone, hnil] using hr.left
    · simpa [outerDone, hright] using hr.right
    · simpa [outerDone, hvalues] using hr.accumulator
    · simpa [outerDone, h3] using hr.index_empty
    · simpa [outerDone] using hr.index_tokens
    · simpa [outerDone] using htokens
    · simpa [outerDone, h6] using hr.right_empty
    · simpa [outerDone, h7] using hr.count_empty
    · simpa [outerDone, h8] using hr.coefficient_empty
    · simpa [outerDone, h9] using hr.operand_left
    · simpa [outerDone, h10] using hr.operand_right
  have hstack : e.stacks = buffers base (outerDone w (encodeArray encode target) P.length) := by
    rw [hr.store_eq, hwork]
  have heEq : e = ⟨e.regs, buffers base (outerDone w (encodeArray encode target) P.length)⟩ :=
    SubexpScanPrimitives.state_ext rfl hstack
  have hbudget := unaryBudget_le (fun _ => outerCost D W pairCost)
    (outerCost D W pairCost) P.length (by intros; rfl)
  refine ⟨n, e.regs, ?_, ?_⟩
  · omega
  · change Eval (outerLoop pair) n ⟨regs, buffers base w⟩ e at he
    rw [heEq] at he
    exact he

end SubexponentialSAT.SubexpConvolutionControl

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpConvolutionExecution
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Actual finite-program execution of the padded triangular convolution.
The generic local pair contract is instantiated separately by the concrete
quartic multiplier and persistent-cell update service. -/

namespace SubexponentialSAT.SubexpConvolutionControl

open BitProgram StructuredCalls

variable {C : Type*}

/-- The whole nested-loop command consumes the left input and row counter,
retains the right input and scalar frame, and writes the computed output. -/
theorem command_run_oai (pair : Code) (base : Store) (encode : C → List Bool)
    (add mul : C → C → C) (D W pairCost : ℕ)
    (hpair : PairSpec pair base encode add mul D pairCost)
    (hencode : ∀ c, (encode c).length = W) (hwidth : (base 104).length = W)
    (h120 : base 120 = []) (h121 : base 121 = []) (h122 : base 122 = [])
    (w : Buffers) (P Q acc : List C) (hP : P.length = D) (hQ : Q.length = D)
    (hlen : acc.length = D) (hleft : w 0 = encodeArray encode P)
    (hright : w 1 = encodeArray encode Q) (hacc : w 2 = encodeArray encode acc)
    (hcount : (w 5).length = D) (h4 : w 4 = [])
    (h3 : w 3 = []) (h6 : w 6 = []) (h7 : w 7 = []) (h8 : w 8 = [])
    (h9 : w 9 = []) (h10 : w 10 = []) :
    ExecutesIn (command pair) (convolutionBudget D W pairCost) (buffers base w)
      (buffers base (finishedBuffers w
        (encodeArray encode (TruncatedConvolution.rows add mul Q 0 D P acc)))) := by
  let result := encodeArray encode (TruncatedConvolution.rows add mul Q 0 D P acc)
  let w' := outerDone w result D
  have hloop : ExecutesIn (outerLoop pair) (D * (outerCost D W pairCost + 2) + 2)
      (buffers base w) (buffers base w') := by
    have h := outerLoop_run pair base encode add mul D W pairCost hpair hencode hwidth
      h120 h121 h122 w P Q acc hQ hlen hleft hright hacc
      (hcount.trans hP.symm) (by simp [h4, hP]) h3 h6 h7 h8 h9 h10
    simpa [w', result, h4, hP] using h
  have hclear : ExecutesIn (clear 105) (2 * D + 3) (buffers base w')
      (buffers base (Function.update w' 4 [])) := by
    simpa [buffers_update, bufferPorts, w', outerDone, h4] using clear_run 105 (buffers base w')
  have hfinal : Function.update w' 4 [] = finishedBuffers w result := by
    funext j
    fin_cases j <;> simp [w', outerDone, finishedBuffers]
  have h := hloop.seq hclear
  rw [hfinal] at h
  change ExecutesIn (command pair) _ _ _ at h
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  simp only [convolutionBudget]
  ring

end SubexponentialSAT.SubexpConvolutionControl

end OAI.Algorithms
end

theorem solution.{u_1} : type_of% @OAI.Algorithms.SubexponentialSAT.SubexpConvolutionControl.command_run_oai.{u_1} := @OAI.Algorithms.SubexponentialSAT.SubexpConvolutionControl.command_run_oai.{u_1}
