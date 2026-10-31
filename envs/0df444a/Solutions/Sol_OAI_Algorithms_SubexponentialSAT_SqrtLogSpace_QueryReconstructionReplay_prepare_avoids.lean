-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryReconstructionReplay.prepare_avoids
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T09:53:55.547801+00:00
-- url     : https://prove2.me/submissions/7f9fb673-f0ae-4355-9897-96f4123ebfd8

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S166
import Definitions.Def_OAIQ081S179
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_ReconstructionNative_run_space

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_StackRoutines
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Fixed-alphabet stack routines

This module records stack-state transformations and proves instruction traces
for concrete programs over Boolean stacks. The number of symbols in a stack is
runtime data; no growing alphabet is used.
-/

namespace SubexponentialSAT.StackRoutines

universe u

theorem clearStacks_frame {S : Type u} [DecidableEq S] (src j : S) (stk : Stacks S)
    (hj : j ≠ src) : clearStacks src stk j = stk j := by
  simp [clearStacks, hj]

open BitProgram

theorem readRegs_frame {r : ℕ} (regs : Fin r → Bool) (value present j : Fin r)
    (top : Option Bool) (hv : j ≠ value) (hp : j ≠ present) :
    readRegs regs value present top j = regs j := by
  simp [readRegs, hv, hp]

end SubexponentialSAT.StackRoutines

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_BankRoutines
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Fixed finite banks of stack-copy and stack-clear routines

The port lists below are part of the finite program syntax.  Word contents and
word lengths remain runtime inputs.  Each call is justified by an actual trace
of the existing stack routine, including its return instruction.  A final clear
of an already empty temporary gives a uniform reset of the two read registers,
including when the port list is empty.
-/

namespace SubexponentialSAT.BankRoutines

open BitProgram StackRoutines StructuredCalls

universe u

theorem clearStacks_eq_self_of_empty {S : Type u} [DecidableEq S]
    (tmp : S) (stk : Stacks S) (htmp : stk tmp = []) :
    clearStacks tmp stk = stk := by
  funext j
  by_cases hj : j = tmp
  · subst j
    simp [htmp]
  · exact clearStacks_frame _ _ _ hj

theorem clearBankStacks_cons {S : Type u} [DecidableEq S]
    (dst : S) (ports : List S) (stk : Stacks S) :
    clearBankStacks ports (clearStacks dst stk) =
      clearBankStacks (dst :: ports) stk := by
  funext j
  by_cases hj : j = dst
  · subst j
    simp [clearBankStacks]
  · simp [clearBankStacks, clearStacks, hj]

theorem clear_call_eval {r s : ℕ} (src : Fin s) (value present : Fin r)
    (regs : Fin r → Bool) (stk : Stacks (Fin s)) :
    Eval (.call (clearProgram src value present)) (2 * (stk src).length + 3)
      ⟨regs, stk⟩ ⟨readRegs regs value present none, clearStacks src stk⟩ := by
  apply Eval.call
  exact ListRegisterProgram.clear_run src value present regs stk

/-- Exact clearing cost in terms of the original word lengths.  The temporary
may also occur in the bank: its initial emptiness makes the final clear cost
exactly three instructions in either case. -/
theorem clear_eval {r s : ℕ} (tmp : Fin s) (value present : Fin r)
    (ports : List (Fin s)) (hports : ports.Nodup)
    (regs : Fin r → Bool) (stk : Stacks (Fin s)) (htmpEmpty : stk tmp = []) :
    Eval (clearCmd tmp value present ports)
      (2 * (ports.map (fun j => (stk j).length)).sum + 3 * ports.length + 3)
      ⟨regs, stk⟩ ⟨readRegs regs value present none, clearBankStacks ports stk⟩ := by
  induction ports generalizing regs stk with
  | nil =>
      have run := clear_call_eval tmp value present regs stk
      simpa [clearCmd, htmpEmpty, clearStacks_eq_self_of_empty tmp stk htmpEmpty] using run
  | cons dst ports ih =>
      have hn := List.nodup_cons.mp hports
      have htemp : clearStacks dst stk tmp = [] := by
        by_cases h : tmp = dst
        · subst tmp
          simp
        · rw [clearStacks_frame dst tmp stk h, htmpEmpty]
      have hmap : ports.map (fun j => (clearStacks dst stk j).length) =
          ports.map (fun j => (stk j).length) := by
        apply List.map_congr_left
        intro j hj
        have hjd : j ≠ dst := by
          intro h
          subst j
          exact hn.1 hj
        rw [clearStacks_frame dst j stk hjd]
      have first := clear_call_eval dst value present regs stk
      have rest := ih hn.2 (readRegs regs value present none)
        (clearStacks dst stk) htemp
      have run := Eval.seq first rest
      simpa only [clearCmd, List.map_cons, List.sum_cons, List.length_cons,
        hmap, readRegs_reset, clearBankStacks_cons, Nat.mul_add,
        Nat.mul_one, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using run

end SubexponentialSAT.BankRoutines

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramCountCorrect
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Closed count recovery: the native Hermite program, the native first-word
reader, and physical reclamation of the CRT caches. The hypotheses describe
stored data and the polynomial, never an assumed arithmetic execution. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.Count

open SubexponentialSAT BitProgram StructuredCalls SubexpLiftRing SubexpQuarticRing
open DensePolynomialProgram


theorem crtRegisters_injective : Function.Injective crtRegisters :=
  Fin.castAdd_injective 16 24

theorem crtStacks_injective : Function.Injective crtStacks :=
  Fin.castAdd_injective 320 448

theorem install_project (a : Data) : install a (project a) = a :=
  embedState_project crtRegisters crtStacks a crtRegisters_injective crtStacks_injective

end SubexponentialSAT.SqrtLog.LeafProgram.Count

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_ReconstructionProgramReady
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.decidableMemJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.decidableMemSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Static readiness obtained from the physically prepared input tapes.
No arithmetic, program trace, or canonicality hypothesis is hidden here. -/
namespace SubexponentialSAT.SqrtLog.ReconstructionProgram.InputReady

open SubexponentialSAT BitProgram StructuredCalls SubexpCRTOuterProgram
open SubexpLiftRing SubexpQuarticRing

theorem nativeReady (p t : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p t) (cache : RingProgram.ScalarCache p t)
    {d : ℕ} (table : Fin d → Fin d → Fin d → Word (baseWidth p t))
    (input : Data) (hc : ∀ i ∈ emptyPorts, input.stacks i = [])
    (hm : input.stacks 194 = M.bits)
    (hw : (input.stacks 202).length = baseWidth p t)
    (hz : input.stacks 203 = cache.zero.val)
    (htable : input.stacks 201 = RingTriple.tableEncoding table)
    (hd : (input.stacks 204).length = d) :
    HornerProgram.Services.NativeReady p t M cache table (base input) := by
  constructor
  · constructor
    · simpa [base, Entry.prepared, localPorts] using hc 120 (by decide)
    · intro i
      fin_cases i <;>
        simp [RingAdapter.ports, RingAdapter.finalNative, RingAdapter.nativeStacks,
          base, Entry.prepared, localPorts]
      all_goals exact hc _ (by decide)
  · simpa [base, Entry.prepared, localPorts] using hm
  · simpa [base, Entry.prepared, localPorts] using hw
  · simpa [base, Entry.prepared, localPorts] using hz
  · simpa [base, Entry.prepared, localPorts] using htable
  · simpa [base, Entry.prepared, localPorts] using hd

theorem polynomialReady (p t : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p t) (cache : RingProgram.ScalarCache p t)
    {d : ℕ} (table : Fin d → Fin d → Fin d → Word (baseWidth p t))
    (input : Data) (hc : ∀ i ∈ emptyPorts, input.stacks i = [])
    (hm : input.stacks 194 = M.bits)
    (hw : (input.stacks 202).length = baseWidth p t)
    (hz : input.stacks 203 = cache.zero.val)
    (htable : input.stacks 201 = RingTriple.tableEncoding table)
    (hd : (input.stacks 204).length = d)
    (hW : (input.stacks 280).length = d*baseWidth p t) :
    DensePolynomialProgram.PairSpec.BaseReady p t M cache table (base input)
      (input.stacks 202) (lowFrame input) := by
  constructor
  · intro i h8 h9
    fin_cases i <;> try contradiction
    all_goals simp [DensePolynomialProgram.RingCall.ports, DensePolynomialProgram.RingCall.port,
      RingScan.serviceState, RingScan.serviceWorkState, RingScan.serviceTapes,
      base, Entry.prepared, localPorts, hm, hz, htable]
    all_goals exact hc _ (by decide)
  · intro i
    fin_cases i <;>
      simp [SubexpConvolutionPair.lowPort, SubexpJetCellProgram.scalarPorts,
        DensePolynomialLoop.ready, DensePolynomialLoop.state, DensePolynomialLoop.stackArray,
        Fin.addCases, Fin.coe_ofNat_eq_mod, base, Entry.prepared, localPorts, lowFrame, hm]
    all_goals exact hc _ (by decide)
  · simpa [base, Entry.prepared, localPorts] using hW
  · exact hw
  · simpa [base, Entry.prepared, localPorts] using hd
  · simpa [base, Entry.prepared, localPorts] using hc 120 (by decide)
  · intro i hlo hhi
    have hi : i = 112 ∨ i = 113 ∨ i = 114 ∨ i = 115 ∨ i = 116 ∨ i = 117 ∨ i = 118 ∨ i = 119 := by
      omega
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [base, Entry.prepared, localPorts]
    all_goals exact hc _ (by decide)

end SubexponentialSAT.SqrtLog.ReconstructionProgram.InputReady

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramCountPrepare
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Actual reclamation of node-work scratch before Hermite reconstruction.
The static port set includes both the native CRT work ports and the scalar/
polynomial arithmetic readiness ports, together with the reader temporaries. Runtime data are cleared by real
stack loops; persistent node and jet inputs remain outside this set. -/

namespace SubexponentialSAT.SqrtLog.LeafProgram.Count.Prepare

open SubexponentialSAT BitProgram StructuredCalls

private theorem ports_lt_aux (i : Fin 768) (hi : i ∈ ports) : i.val < 330 := by
  simp only [ports,List.mem_dedup,List.mem_append] at hi
  rcases hi with hi | hi
  · obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hi
    change j.val < 330
    omega
  · simp only [List.mem_cons,List.mem_nil_iff,or_false] at hi
    rcases hi with h|h|h|h|h|h|h <;> subst i <;> norm_num

theorem scratch_outside : (699 : Fin 768) ∉ ports := by
  intro h
  have := ports_lt_aux 699 h
  norm_num at this

theorem ports_nodup : ports.Nodup := List.nodup_dedup _

theorem command_eval (a : Data) : Eval command (budget a) a (output a) := by
  let mid : Data := ⟨readRegs a.regs 0 1 none,Function.update a.stacks 699 []⟩
  have h1 : Eval (.call (StackRoutines.clearProgram 699 0 1)) (2*(a.stacks 699).length+3) a mid :=
    Eval.call _ (ListRegisterProgram.clear_run (699 : Fin 768) (0 : Fin 40) 1 a.regs a.stacks)
  have h2 := BankRoutines.clear_eval (699 : Fin 768) (0 : Fin 40) 1 ports
    ports_nodup mid.regs mid.stacks (by simp [mid])
  have hm : ports.map (fun i => (mid.stacks i).length) = ports.map (fun i => (a.stacks i).length) := by
    apply List.map_congr_left
    intro i hi
    have hn : i ≠ 699 := by intro h; subst i; exact scratch_outside hi
    simp [mid,hn]
  rw [hm] at h2
  have hfinal : (⟨readRegs mid.regs 0 1 none,
      BankRoutines.clearBankStacks ports mid.stacks⟩ : Data) = output a := by
    simp only [output,mid,StackRoutines.readRegs_reset]
  rw [hfinal] at h2
  have he := h1.seq h2
  have hcost : (2*(a.stacks 699).length+3) +
      (2*(ports.map (fun i => (a.stacks i).length)).sum+3*ports.length+3) = budget a := by
    unfold budget
    omega
  rw [hcost] at he
  exact he

theorem output_clean (a : Data) (i : Fin 320)
    (hi : i ∈ ReconstructionProgram.NativeState.cleanPorts) :
    (output a).stacks (crtStacks i) = [] := by
  have hm : crtStacks i ∈ ports := by
    apply List.mem_dedup.mpr
    exact List.mem_append.mpr (Or.inl
      (List.mem_map.mpr ⟨i,List.mem_append.mpr (Or.inl hi),rfl⟩))
  simpa only [output] using
    (BankRoutines.clearBankStacks_mem (crtStacks i) ports
      (Function.update a.stacks 699 []) hm)

theorem output_arithmetic_clean (a : Data) (i : Fin 320)
    (hi : i ∈ ReconstructionProgram.InputReady.emptyPorts) :
    (output a).stacks (crtStacks i) = [] := by
  have hm : crtStacks i ∈ ports := by
    apply List.mem_dedup.mpr
    exact List.mem_append.mpr (Or.inl
      (List.mem_map.mpr ⟨i,List.mem_append.mpr (Or.inr hi),rfl⟩))
  simpa only [output] using
    (BankRoutines.clearBankStacks_mem (crtStacks i) ports
      (Function.update a.stacks 699 []) hm)

theorem output_reader (a : Data) (i : Fin 768)
    (hi : i ∈ ([323,324,325,326,327,328,329] : List (Fin 768))) :
    (output a).stacks i = [] := by
  have hm : i ∈ ports := by
    apply List.mem_dedup.mpr
    exact List.mem_append.mpr (Or.inr hi)
  simpa only [output] using
    (BankRoutines.clearBankStacks_mem i ports (Function.update a.stacks 699 []) hm)

theorem output_frame (a : Data) (i : Fin 768) (hi : i ∉ ports) (ht : i ≠ 699) :
    (output a).stacks i = a.stacks i := by
  simp [output,BankRoutines.clearBankStacks,hi,ht]

private theorem native_inputs_disjoint : List.Disjoint
    (ReconstructionProgram.NativeState.cleanPorts.map crtStacks) protectedInputs := by
  simp [List.Disjoint, protectedInputs, ReconstructionProgram.NativeState.cleanPorts,
    ReconstructionProgram.NativeState.workingClean,
    ReconstructionProgram.Middle.cleanPorts,
    ReconstructionProgram.CofactorOuter.cleanPorts,
    ReconstructionProgram.Scalar.cleanPorts,
    ReconstructionProgram.Horner.cleanPorts,
    SubexpCRTOuterProgram.initialCleanPorts, CRTLocalProgram.localWork,
    SubexponentialSAT.SubexpConvolutionControl.bufferPorts,
    SubexpCRTOuterProgram.localPorts, crtStacks]

private theorem arithmetic_inputs_disjoint : List.Disjoint
    (ReconstructionProgram.InputReady.emptyPorts.map crtStacks) protectedInputs := by
  simp [List.Disjoint, protectedInputs, ReconstructionProgram.InputReady.emptyPorts, crtStacks]

private theorem reader_inputs_disjoint : List.Disjoint
    ([323,324,325,326,327,328,329] : List (Fin 768)) protectedInputs := by
  simp [List.Disjoint, protectedInputs]

theorem inputs_disjoint : List.Disjoint ports protectedInputs := by
  apply List.disjoint_left.mpr
  intro i hi hp
  simp only [ports,List.mem_dedup,List.map_append,List.mem_append] at hi
  rcases hi with hleft | hr
  · rcases hleft with hn | ha
    · exact (List.disjoint_left.mp native_inputs_disjoint) hn hp
    · exact (List.disjoint_left.mp arithmetic_inputs_disjoint) ha hp
  · exact (List.disjoint_left.mp reader_inputs_disjoint) hr hp

theorem output_input (a : Data) (i : Fin 768)
    (hi : i ∈ ([194,201,202,203,204,207,209,211,212,243,256,265,280] : List (Fin 768))) :
    (output a).stacks i = a.stacks i := by
  apply output_frame
  · intro h
    apply (List.disjoint_left.mp inputs_disjoint) h
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hi
    rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
      simp [protectedInputs]
  · intro h; subst i; simp at hi

theorem output_register_frame (a : Data) (i : Fin 40) (hi : 2 ≤ i.val) :
    (output a).regs i = a.regs i := by
  apply StackRoutines.readRegs_frame
  · intro h; subst i; simp at hi
  · intro h; subst i; simp at hi

end SubexponentialSAT.SqrtLog.LeafProgram.Count.Prepare

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_RingNodeProgramModel
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The physical radix generator emits precisely the coefficient encoding of
nodes in the actual supplied-polynomial unramified ring. -/
namespace SubexponentialSAT.SqrtLog.RingNodeProgram

open SubexponentialSAT BinaryArithmetic SubexpLiftRing SubexpQuarticRing
open RingProgram

theorem nodeCode_value (t d n : ℕ) (ht : 0 < t) (j : Fin d) :
    BinaryArithmetic.toNat (nodeCode t d n j).val = n / 3^j.val % 3 := by
  apply toNat_fixedBits_of_lt
  have hc : 2^2 ≤ 2^(2*t) := Nat.pow_le_pow_right (by decide) (by omega)
  rw [ternary_baseWidth]
  have hm := Nat.mod_lt (n / 3^j.val) (by decide : 0 < 3)
  norm_num at hc
  omega

theorem residueNode_coordinate {d : ℕ} (a : RingModel.Data d) (Q : ℕ)
    (hQ : Q < 3^d) (i : Fin Q) (j : Fin d) :
    (a.fieldCoordinates (a.residueNode Q hQ i) j).val = (i.val+1) / 3^j.val % 3 := by
  let index : Fin (3^d) := ⟨i.val+1, by omega⟩
  let v : Fin d → ZMod 3 := fun j =>
    ZMod.finEquiv 3 ((finFunctionFinEquiv.symm index) j)
  change (a.fieldCoordinates (a.fieldCoordinates.symm v) j).val = _
  rw [LinearEquiv.apply_symm_apply]
  rfl

/-- The physical words decode to the same nodes used by interpolation. -/
theorem nodeCode_decode (t : ℕ) (ht : 0 < t) {d : ℕ} (hd : 0 < d)
    (a : RingModel.Data d) (M : SubexpPreparedQuartic.Modulus 3 t)
    (cache : ScalarCache 3 t) (Q : ℕ) (hQ : Q < 3^d) (i : Fin Q) :
    (modelRing t ht hd a M cache).decode (nodeCode t d (i.val+1)) =
      a.node t Q ht hQ i := by
  rw [modelRing_decode]
  unfold RingModel.Data.node RingModel.Data.sectionValue
  congr 1
  funext j
  unfold wordValue
  rw [nodeCode_value t d (i.val+1) ht j, residueNode_coordinate]

/-- The generated nodes have pairwise distinct, nonzero residues. -/
theorem generated_residue_injective (t : ℕ) (ht : 0 < t) {d : ℕ} (hd : 0 < d)
    (a : RingModel.Data d) (M : SubexpPreparedQuartic.Modulus 3 t)
    (cache : ScalarCache 3 t) (Q : ℕ) (hQ : Q < 3^d) :
    Function.Injective (fun i : Fin Q => a.rho t ht
      ((modelRing t ht hd a M cache).decode (nodeCode t d (i.val+1)))) := by
  simp_rw [nodeCode_decode t ht hd a M cache Q hQ, RingModel.Data.rho_node]
  exact a.residueNode_injective Q hQ

end SubexponentialSAT.SqrtLog.RingNodeProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafRingSetupProgramNative
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms


/-! The fixed executable preparation pipeline.  Its input is the actual
numerical bank emitted by `LeafParametersProgram`; no field polynomial,
modulus, multiplication table, nodes, or idempotent coefficients are inputs.
The stage-by-stage execution theorem is separate from this code definition.
-/


/-! Arithmetic consumers use the same bytes generated by the preceding
stages.  These are structural handoff lemmas; the complete production
trace must establish `NativeBytes` before invoking them. -/

namespace SubexponentialSAT.SqrtLog.LeafRingSetupProgram
open BitProgram StructuredCalls SubexpQuarticRing SubexpLiftRing

/-- The generated canonical scalar zero has the literal bytes required by
the native CRT/readback interface. No additional cache premise is needed. -/
theorem RingCaches.zero_bytes {t d : ℕ} {model : RingModel.Data d}
    {M : SubexpPreparedQuartic.Modulus 3 t} {cache : RingProgram.ScalarCache 3 t}
    {u : RingProgram.ScalarCode 3 t} {a : Data}
    (h : RingCaches t d model M cache u a) :
    cache.zero.val=List.replicate (baseWidth 3 t) false :=
  IdempotentPreparationProgram.Scalar.canonical_zero_bytes t cache h.canonical

end SubexponentialSAT.SqrtLog.LeafRingSetupProgram

namespace SubexponentialSAT.SqrtLog.LeafRingSetupProgram
open BitProgram StructuredCalls LeafParametersProgram SubexpQuarticRing SubexpLiftRing

theorem Produced.zero_bytes {m : Circuit.Model} {hd : 0 < m.val 34}
    {M : SubexpPreparedQuartic.Modulus 3 (m.val 33)}
    {cache : RingProgram.ScalarCache 3 (m.val 33)}
    {u : RingProgram.ScalarCode 3 (m.val 33)} {a : Data}
    (h : Produced m hd M cache u a) :
    cache.zero.val=List.replicate (baseWidth 3 (m.val 33)) false :=
  h.caches.zero_bytes

end SubexponentialSAT.SqrtLog.LeafRingSetupProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_QueryReconstruction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! The actual streamed-jet handoff, scratch preparation, and canonical count
reconstruction. Readiness is derived from the produced ring masters. The target
and jets are mathematical properties of the actual query output; no evaluator
or readiness service is accepted by the produced-input theorem. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryReconstruction

open OAI BitProgram StructuredCalls SubexpLiftRing SubexpQuarticRing OAI.Algorithms.SubexponentialSAT.SqrtLog
open DensePolynomialProgram LeafProgram
open LeafParametersProgram
attribute [local simp] Fin.coe_ofNat_eq_mod

/-- Preparation only clears words, including all of its arithmetic temporaries. -/
theorem prepare_bound (a : CoreData) (B : ℕ)
    (ha : ∀ i, (a.stacks i).length ≤ B) :
    ∀ i, ((Count.Prepare.output a).stacks i).length ≤ B := by
  intro i
  by_cases hi : i ∈ Count.Prepare.ports
  · simp [Count.Prepare.output, BankRoutines.clearBankStacks, hi]
  by_cases hs : i = 699
  · subst i
    simp [Count.Prepare.output, BankRoutines.clearBankStacks, hi]
  simpa [Count.Prepare.output, BankRoutines.clearBankStacks, hi, hs] using ha i

theorem prepare_budget (a : CoreData) (B : ℕ)
    (ha : ∀ i, (a.stacks i).length ≤ B) : Count.Prepare.budget a ≤ prepareBudget B := by
  have hsum : (Count.Prepare.ports.map (fun i => (a.stacks i).length)).sum ≤
      Count.Prepare.ports.length * B := by
    have h := List.sum_le_card_nsmul
      (Count.Prepare.ports.map (fun i => (a.stacks i).length)) B (by
        intro x hx
        obtain ⟨i, _, rfl⟩ := List.mem_map.mp hx
        exact ha i)
    simpa only [List.length_map, smul_eq_mul] using h
  have hscratch := ha 699
  unfold Count.Prepare.budget prepareBudget
  simp only [Nat.mul_assoc]
  omega

/-- Readiness is proved from producer bytes after the actual scratch cleanup.
This is the proof underlying `PreparedRecovery.ofProduced`, applied directly so
that the old materialized query program is not an executable dependency. -/
private theorem core_execution (m : Circuit.Model) (ht : 0 < m.val 33) (hd : 0 < m.val 34)
    (M : SubexpPreparedQuartic.Modulus 3 (m.val 33))
    (cache : RingProgram.ScalarCache 3 (m.val 33))
    (half : RingProgram.ScalarCode 3 (m.val 33)) (e : LeafRingSetupProgram.Data)
    (hp : LeafRingSetupProgram.Produced m hd M cache half e)
    (a : CoreData)
    (hframe : ∀ i ∈ ringPorts, a.stacks (Count.crtStacks i) = e.stacks (i.castAdd 320))
    (hQ : 0 < m.val 21) (hJ : 0 < m.val 42)
    (hfield : m.val 21 < 3^(m.val 34))
    (hexponent : (Circuit.result Serialization.code m).val 44 = 3^(m.val 34)-2)
    (jets : Fin (m.val 21) → CRTLocalProgram.Model.Poly
      (baseWidth 3 (m.val 33)) (m.val 34) (m.val 42))
    (hnodes : a.stacks 256 = (List.finRange (m.val 21)).flatMap
      (fun i => RingProgram.flat (RingNodeProgram.nodeCode (m.val 33) (m.val 34) (i.val+1))))
    (hjets : a.stacks 265 = (List.finRange (m.val 21)).flatMap (fun i => Fixed.encode (jets i)))
    (target : Polynomial ((IrreducibleSearch.data hd).O (m.val 33)))
    (hdegree : target.natDegree < m.val 21 * m.val 42)
    (hhas : Reconstruction.HasJets
      (RingProgram.modelRing (m.val 33) ht hd (IrreducibleSearch.data hd) M cache)
      (fun i : Fin (m.val 21) => RingNodeProgram.nodeCode (m.val 33) (m.val 34) (i.val+1))
      (m.val 42) (fun i => (jets i).1) target)
    (count multiplicity ambient : ℕ) (hcount : count ≤ multiplicity*2^ambient)
    (hlarge : multiplicity*2^ambient < 3^(m.val 33))
    (hconstant : target.eval 0 = (count : (IrreducibleSearch.data hd).O (m.val 33)))
    (B S : ℕ) (ha : ∀ i, (a.stacks i).length ≤ B)
    (hQsize : m.val 21 ≤ S) (hJsize : m.val 42 ≤ S) (htsize : m.val 33 ≤ S)
    (hdsize : m.val 34 ≤ S) (hqsize : 3^(m.val 34) ≤ S)
    (hmodsize : (a.stacks 194).length ≤ S) (hwidthsize : (a.stacks 202).length ≤ S)
    (hcountsize : (DisjointReuse.binaryNat count).length ≤ B) :
    ∃ steps out, steps+1 ≤ coreBudget B S ∧ Eval coreCommand steps a out ∧
      out.stacks = Function.update (Count.Prepare.output a).stacks 323
        (DisjointReuse.binaryNat count) ∧
      (∀ i, (out.stacks i).length ≤ B) ∧
      (∀ i : Fin 40, 16 ≤ i.val → out.regs i = a.regs i) := by
  let : NeZero (m.val 21) := ⟨Nat.ne_of_gt hQ⟩
  generalize hprepared : Count.Prepare.output a = prepared
  let input := Count.project prepared
  have preserved (i : Fin 768)
      (hi : i ∈ ([194,201,202,203,204,207,209,211,212,243,256,265,280] : List (Fin 768))) :
      prepared.stacks i = a.stacks i := by
    have h := Count.Prepare.output_input a i hi
    rw [hprepared] at h
    exact h
  have cleaned (i : Fin 320) (hi : i ∈ ReconstructionProgram.NativeState.cleanPorts) :
      input.stacks i = [] := by
    have h := Count.Prepare.output_clean a i hi
    rw [hprepared] at h
    exact h
  have readers (i : Fin 768)
      (hi : i ∈ ([323,324,325,326,327,328,329] : List (Fin 768))) :
      prepared.stacks i = [] := by
    have h := Count.Prepare.output_reader a i hi
    rw [hprepared] at h
    exact h
  have fw (i : Fin 320) (hi : i ∈ ringPorts) : input.stacks i = e.stacks (i.castAdd 320) := by
    change prepared.stacks (Count.crtStacks i) = _
    rw [preserved]
    · exact hframe i hi
    · simp only [ringPorts, List.mem_cons, List.mem_nil_iff, or_false] at hi
      rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide
  have hm := (fw 194 (by simp [ringPorts])).trans hp.caches.modulus
  have hw := congrArg List.length (fw 202 (by simp [ringPorts])) |>.trans hp.caches.width
  have hz := (fw 203 (by simp [ringPorts])).trans hp.caches.scalarZero
  have htable := (fw 201 (by simp [ringPorts])).trans hp.native.table
  have hdw := congrArg List.length (fw 204 (by simp [ringPorts])) |>.trans hp.caches.degree
  have hzero := (fw 280 (by simp [ringPorts])).trans hp.caches.fullZero_model
  have hlen := congrArg List.length (fw 280 (by simp [ringPorts])) |>.trans hp.native.fullZeroLength
  have hclean (i : Fin 320) (hi : i ∈ ReconstructionProgram.InputReady.emptyPorts) :
      input.stacks i = [] := by
    have h := Count.Prepare.output_arithmetic_clean a i hi
    rw [hprepared] at h
    exact h
  have hscalar := ReconstructionProgram.InputReady.nativeReady 3 _ M cache _ input
    hclean hm hw hz htable hdw
  have hpoly := ReconstructionProgram.InputReady.polynomialReady 3 _ M cache _ input
    hclean hm hw hz htable hdw hlen
  have hmod : (input.stacks 194).length ≤ S := by
    change (prepared.stacks 194).length ≤ S
    rw [preserved 194 (by decide)]
    exact hmodsize
  have hwidth : (input.stacks 202).length ≤ S := by
    change (prepared.stacks 202).length ≤ S
    rw [preserved 202 (by decide)]
    exact hwidthsize
  obtain ⟨steps, out, hsteps, he, _, hs, hr, _⟩ :=
    ReconstructionNative.run_space (m.val 33) ht hd (IrreducibleSearch.data hd) M cache
      hp.caches.canonical hp.zero_bytes (m.val 42) hJ (Nat.mul_pos ht (by omega))
      (fun i : Fin (m.val 21) => RingNodeProgram.nodeCode (m.val 33) (m.val 34) (i.val+1))
      jets (Constants.constantCode (m.val 34) cache.minusOne cache.zero)
      (Constants.minusOne_decode _ ht hd _ M cache) input hscalar (input.stacks 202)
      (ReconstructionProgram.InputReady.lowFrame input) hpoly cleaned
      hzero ((fw 207 (by simp [ringPorts])).trans hp.caches.fullOne_model)
      ((fw 211 (by simp [ringPorts])).trans
        (hp.caches.fullMinusOne.trans (Constants.constantCode_flat _ _ _).symm))
      ((fw 243 (by simp [ringPorts])).trans hp.jetOrder)
      ((preserved 256 (by decide)).trans hnodes)
      ((preserved 265 (by decide)).trans hjets)
      ((congrArg List.length ((fw 209 (by simp [ringPorts])).trans hp.exponent)).trans
        (by simp only [List.length_replicate, hexponent]))
      ((congrArg List.length ((fw 212 (by simp [ringPorts])).trans hp.caches.precision)).trans
        (by simp only [List.length_replicate]))
      (RingNodeProgram.generated_residue_injective _ ht hd _ M cache _ hfield)
      target hdegree hhas count multiplicity ambient hcount hlarge hconstant
      S hQsize hJsize htsize hdsize hqsize hmod hwidth prepared
      (hm ▸ M.value) hw readers
  have hstart : Count.install prepared input = prepared := Count.install_project _
  rw [hstart] at he hs hr
  have hprepare := Count.Prepare.command_eval a
  rw [hprepared] at hprepare
  have hbound := prepare_bound a B ha
  rw [hprepared] at hbound
  refine ⟨Count.Prepare.budget a+steps, out, ?_, hprepare.seq he, hs, ?_, ?_⟩
  · have hp := prepare_budget a B ha
    unfold coreBudget
    omega
  · intro i
    rw [hs]
    by_cases hi : i = 323
    · subst i
      simpa using hcountsize
    simpa only [Function.update_of_ne hi] using hbound i
  · intro i hi
    have hf := Count.Prepare.output_register_frame a i (by omega)
    rw [hprepared] at hf
    exact (hr i hi).trans hf

/-- The two accumulated counts lie above the native arithmetic bank and
below the canonical reader temporaries. Membership is proved structurally. -/
theorem collector_outside (i : Fin 768) (hlo : 320 ≤ i.val) (hhi : i.val < 323) :
    i ∉ Count.Prepare.ports := by
  intro hi
  simp only [Count.Prepare.ports, List.mem_dedup, List.mem_append] at hi
  rcases hi with hi | hi
  · obtain ⟨j, _, hj⟩ := List.mem_map.mp hi
    have hv := congrArg Fin.val hj
    change j.val = i.val at hv
    omega
  · simp only [List.mem_cons, List.mem_nil_iff, or_false] at hi
    rcases hi with h|h|h|h|h|h|h <;> subst i <;> simp at hhi

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryReconstruction
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_QueryReconstructionReplay
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! The complete streamed recovery command does not inspect or modify the
marked-record cursor320 or accumulated mass322. This includes the paid jet
handoff, actual scratch preparation, the CRT, canonical reader and cleanup. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryReconstructionReplay

open BitProgram StructuredCalls SqrtLog.ProgramTapeReplay

private theorem bankClear_avoids {r s : ℕ} (H : Fin s → Prop)
    (temporary : Fin s) (value present : Fin r) (ports : List (Fin s))
    (ht : ¬ H temporary) (hp : ∀ i ∈ ports, ¬ H i) :
    AvoidsCmd H (BankRoutines.clearCmd temporary value present ports) := by
  induction ports with
  | nil => exact avoids_clearProgram H temporary value present ht
  | cons i ports ih =>
      exact ⟨avoids_clearProgram H i value present (hp i (by simp)),
        ih (fun j hj => hp j (by simp [hj]))⟩

theorem prepare_avoids_oai :
    AvoidsCmd (fun i : Fin 768 => i.val = 320 ∨ i.val = 322)
      SqrtLog.LeafProgram.Count.Prepare.command := by
  unfold SqrtLog.LeafProgram.Count.Prepare.command
  generalize hports : SqrtLog.LeafProgram.Count.Prepare.ports = ports
  refine ⟨avoids_clearProgram _ 699 0 1 (by decide),
    bankClear_avoids _ 699 0 1 ports (by decide) ?_⟩
  intro i hi hidden
  rw [← hports] at hi
  exact (QueryReconstruction.collector_outside i (by omega) (by omega)) hi

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryReconstructionReplay
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryReconstructionReplay.prepare_avoids_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryReconstructionReplay.prepare_avoids_oai
