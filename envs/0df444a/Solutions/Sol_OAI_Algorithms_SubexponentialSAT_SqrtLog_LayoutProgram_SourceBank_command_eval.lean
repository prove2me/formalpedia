-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank.command_eval
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T10:36:53.417048+00:00
-- url     : https://prove2.me/submissions/668e54da-e8ec-48b7-8273-dd4d547161f7

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S186
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_LayoutProgram_EntryBankFrame_lookup_lifted
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_LayoutProgram_SourceBank_Ready_metadata
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_LayoutProgram_SourceBank_compareBlocks_eval
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_LayoutProgram_SourceBank_covered_uncovered_cleanup
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_LayoutProgram_SourceBank_literal_cleanup_eval
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_LayoutProgram_SourceBank_nativeBudget_le
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_LayoutProgram_SourceBank_uncovered_cleanup
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_LayoutProgram_SourceBank_universalBudget_le
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_LayoutProgram_SourceBank_universal_generated
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_LayoutSourceExpression_literal_length_le_sourceLengthBound

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_PackingMetadata
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Exact lookup semantics for the storage-ordered packing metadata table.
The physical extraction proof identifies its emitted records with this table. -/

namespace SubexponentialSAT.Subexp.PackingMetadata

open ConstructivePacking
open GlobalBasisMetadata (Metadata)

variable {V U : Type*} [DecidableEq V] [DecidableEq U]

theorem lookup_eq (P : PackingData V U) (encodeVertex : V → List Bool)
    (encodeType : U → List Bool) (hvertex : Function.Injective encodeVertex) (v : V) :
    (records P encodeVertex encodeType).lookup (encodeVertex v) =
      some (value P encodeType v).encode :=
  lookup_graph_encoded _ _ _ hvertex v
    (by simpa using PackingReorder.mem_storageVertices P v)

end SubexponentialSAT.Subexp.PackingMetadata

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutProgramSourceBankFrameCalls
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank
attribute [local simp] Fin.coe_ofNat_eq_mod
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp

theorem lookupRegs_inj : Function.Injective lookupRegs := Fin.castAdd_injective _ _
theorem lookupPorts_inj : Function.Injective lookupPorts := by decide

theorem lookup_eval (a : Data) (records : List (List Bool × List Bool))
    (row col : List Bool) (mr mc : GlobalBasisMetadata.Metadata)
    (hr : records.lookup row=some mr.encode) (hc : records.lookup col=some mc.encode)
    (hm : a.stacks 306=SelectorProgram.rawRecords records)
    (hrow : a.stacks 304=row) (hcol : a.stacks 305=col)
    (hready : ∀ j : Fin 320, 288 ≤ j.val → j.val ≤ 300 → a.stacks j=[]) :
    ∃ n ≤ 400*(GlobalBasisMetadata.volume records row)^2+
        400*(GlobalBasisMetadata.volume records col)^2+1,
      ∃ e : Data, Eval lookup n a e ∧ e.stacks=metadataStacks a mr mc ∧
        e.regs 4=mr.coveredFlag ∧ e.regs 5=mc.coveredFlag := by
  have ha : projectState lookupRegs lookupPorts a=
      LookupPair.state (a.regs ∘ lookupRegs) (SelectorProgram.rawRecords records)
        row col [] [] [] [] [] [] := by
    apply congrArg₂ StructuredProgram.State.mk rfl
    funext j
    fin_cases j <;> simp [lookupPorts,hm,hrow,hcol,hready]
  obtain ⟨n,hn,e,he,hp,hf,_⟩ := EntryBankFrame.lookup_lifted lookupRegs lookupPorts
    lookupRegs_inj lookupPorts_inj a records row col mr mc hr hc ha
  refine ⟨n,hn,e,he,?_,?_,?_⟩
  · funext j
    by_cases hj : ∃ i, lookupPorts i=j
    · obtain ⟨i,rfl⟩ := hj
      have h := congrArg (fun d : LookupPair.Data => d.stacks i) hp
      fin_cases i <;>
        simpa [projectState,lookupPorts,LookupPair.state,metadataStacks,hm,hrow,hcol,hready] using h
    · rw [hf j hj]
      have h288 : j≠288 := by intro h; apply hj; exact ⟨3,h.symm⟩
      have h289 : j≠289 := by intro h; apply hj; exact ⟨4,h.symm⟩
      have h290 : j≠290 := by intro h; apply hj; exact ⟨5,h.symm⟩
      have h291 : j≠291 := by intro h; apply hj; exact ⟨6,h.symm⟩
      have h292 : j≠292 := by intro h; apply hj; exact ⟨7,h.symm⟩
      have h293 : j≠293 := by intro h; apply hj; exact ⟨8,h.symm⟩
      simp [metadataStacks,h288,h289,h290,h291,h292,h293]
  · exact congrArg (fun d : LookupPair.Data => d.regs 4) hp
  · exact congrArg (fun d : LookupPair.Data => d.regs 5) hp

end SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutProgramSourceBankFrameReady
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.Packing.nonemptyUniversal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Concrete pre-state invariants for source dispatch. Metadata lookup and
whole-store comparisons preserve these low-bank arithmetic inputs. -/
namespace SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank
attribute [local simp] Fin.coe_ofNat_eq_mod
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp SubexponentialSAT.MulticolorTypes
open IntegerRingLiftProgram

theorem inputFields_frame {r Q : ℕ} (a b : Data) (c : Numerator.Saved) (start : Fin Q)
    (u y : UniversalType r Q 1) (h : InputFields a c start u y)
    (hf : lowStore b=lowStore a) : InputFields b c start u y := by
  intro i hi hj
  rw [hf]
  exact h i hi hj

theorem inputFields_store_frame {r Q : ℕ} (a b : Data) (c : Numerator.Saved) (start : Fin Q)
    (u y : UniversalType r Q 1) (h : InputFields a c start u y)
    (hf : b.stacks=a.stacks) : InputFields b c start u y :=
  inputFields_frame a b c start u y h (by simp [lowStore,projectState,hf])

theorem cachedReady_store_frame (t : ℕ) {d : ℕ} (model : RingModel.Data d)
    (M : SubexpPreparedQuartic.Modulus 3 t) (cache : RingProgram.ScalarCache 3 t)
    (zero one minusOne : ModelCode t d) (a b : Data)
    (h : CachedReady t model M cache zero one minusOne (lowStore a))
    (hf : b.stacks=a.stacks) : CachedReady t model M cache zero one minusOne (lowStore b) := by
  simpa [lowStore,projectState,hf] using h

end SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutProgramSourceBankState
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Cache and workspace invariants for the actual metadata dispatch. -/
namespace SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp SubexponentialSAT.MulticolorTypes
attribute [local simp] Fin.coe_ofNat_eq_mod

theorem metadata_frame (a : Data) (mr mc : GlobalBasisMetadata.Metadata)
    (j : Fin 320) (hj : j.val < 288 ∨ 293 < j.val) :
    metadataStacks a mr mc j=a.stacks j := by
  have h288 : j≠288 := by intro h; subst j; norm_num at hj
  have h289 : j≠289 := by intro h; subst j; norm_num at hj
  have h290 : j≠290 := by intro h; subst j; norm_num at hj
  have h291 : j≠291 := by intro h; subst j; norm_num at hj
  have h292 : j≠292 := by intro h; subst j; norm_num at hj
  have h293 : j≠293 := by intro h; subst j; norm_num at hj
  simp [metadataStacks,h288,h289,h290,h291,h292,h293]

theorem WorkReady.frame {a b : Data} (h : WorkReady a) (hb : b.stacks=a.stacks) : WorkReady b := by
  constructor
  · intro j hj hk; rw [hb]; exact h.work j hj hk
  · rw [hb]; exact h.temp
  · rw [hb]; exact h.output
  · rw [hb]; exact h.count
  · rw [hb]; exact h.tableCount
  · rw [hb]; exact h.tableAccum
  · intro j hj; rw [hb]; exact h.low j hj

theorem WorkReady.literal {a : Data} (h : WorkReady a) :
    a.stacks 319=[] ∧ a.stacks 315=[] ∧ a.stacks 316=[] ∧ a.stacks 287=[] := by
  exact ⟨h.temp,h.work 315 (by decide) (Or.inr (by decide)),
    h.work 316 (by decide) (Or.inr (by decide)),h.output⟩

theorem WorkReady.compare {a : Data} (h : WorkReady a) :
    a.stacks 301=[] ∧ a.stacks 302=[] ∧ a.stacks 303=[] ∧ a.stacks 307=[] := by
  exact ⟨h.work 301 (by decide) (Or.inr (by decide)),
    h.work 302 (by decide) (Or.inr (by decide)),
    h.work 303 (by decide) (Or.inr (by decide)),
    h.work 307 (by decide) (Or.inr (by decide))⟩

theorem cleared_metadata (a : Data) (mr mc : GlobalBasisMetadata.Metadata)
    (rf : Fin 16 → Bool) :
    clearedStacks (⟨rf,metadataStacks a mr mc⟩ : Data)=clearedStacks a := by
  funext j
  simp only [clearedStacks]
  by_cases hj : j∈cleanupPorts
  · simp [hj]
  · simp only [ite_eq_right hj]
    apply metadata_frame
    by_contra hn
    have hr : 288 ≤ j.val ∧ j.val ≤ 293 := by omega
    have hm : j∈List.ofFn (fun i : Fin 16 => (⟨288+i.val,by omega⟩ : Fin 320)) := by
      apply List.mem_ofFn.mpr
      refine ⟨⟨j.val-288,by omega⟩,?_⟩
      apply Fin.ext; simp; omega
    apply hj
    simp only [cleanupPorts,List.mem_append]
    exact Or.inl (Or.inr hm)

theorem cleared_eq {a : Data} (h : ∀ j∈cleanupPorts,a.stacks j=[]) : clearedStacks a=a.stacks := by
  funext j
  simp only [clearedStacks]
  split_ifs with hj
  · exact (h j hj).symm
  · rfl

theorem metadata_length {a b : Data} (mr mc : GlobalBasisMetadata.Metadata) (S : ℕ)
    (hb : b.stacks=metadataStacks a mr mc) (ha : ∀ j,(a.stacks j).length ≤ S)
    (hr : MetadataBound mr S) (hc : MetadataBound mc S) :
    ∀ j,(b.stacks j).length ≤ S := by
  intro j
  rw [hb]
  simp only [metadataStacks,Function.update_apply]
  split_ifs <;> first
    | exact hr.1
    | exact hr.2.1
    | exact hr.2.2
    | exact hc.1
    | exact hc.2.1
    | exact hc.2.2
    | exact ha j

theorem lookup_ready {a : Data} (h : ∀ j∈cleanupPorts,a.stacks j=[]) :
    ∀ j : Fin 320,288 ≤ j.val → j.val ≤ 300 → a.stacks j=[] := by
  intro j hj hk
  apply h
  have hm : j∈List.ofFn (fun i : Fin 16 => (⟨288+i.val,by omega⟩ : Fin 320)) := by
    apply List.mem_ofFn.mpr
    refine ⟨⟨j.val-288,by omega⟩,?_⟩
    apply Fin.ext; simp; omega
  simp only [cleanupPorts,List.mem_append]
  exact Or.inl (Or.inr hm)

theorem cleared_metadata_eq {a b : Data} (mr mc : GlobalBasisMetadata.Metadata)
    (h : ∀ j∈cleanupPorts,a.stacks j=[]) (hb : b.stacks=metadataStacks a mr mc) :
    clearedStacks b=a.stacks := by
  have hh := cleared_metadata a mr mc b.regs
  have he : b=(⟨b.regs,metadataStacks a mr mc⟩ : Data) :=
    SubexpScanPrimitives.state_ext rfl hb
  rw [he,hh,cleared_eq h]

end SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutSourceExpression
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Degree certificates for the actual typed literal and interpolation-row
sources. These remove the full-polynomial cutoff premise at R+1. -/
namespace SubexponentialSAT.SqrtLog.LayoutSourceExpression

open SubexponentialSAT SubexponentialSAT.SubexpSymbolicCost
open SubexponentialSAT.Subexp.UniversalRowProgram
open SubexponentialSAT.MulticolorTypes SubexponentialSAT.SubexpRepresentedRows SubexponentialSAT.SubexpRowInterpolation
open PolynomialExecutorProgram

/-- A native scalar literal is exactly one typed coefficient cell. -/
theorem literal_code {B d : ℕ} (c : Coeff B d) :
    SubexpPostfixControl.serializeCode DensePolynomialProgram.encode
      (Algorithm.Expr.lit [c]).compile = SubexpKernelControl.pushWord (RingProgram.flat c) := by
  simp [Algorithm.Expr.compile,SubexpPostfixControl.serializeCode,
    SubexpPostfixControl.serializeInstr,DensePolynomialProgram.encode,SubexpKernelControl.pushWord]

theorem literal_meaning {C O : Type*} [CommRing O] (ops : RepresentedRing C O) (c : C) :
    ((Algorithm.Expr.lit [c]).map (meaning ops)).eval = Polynomial.C (ops.decode c) := by
  simp [Algorithm.Expr.map,Algorithm.Expr.eval,meaning,PolynomialAlgorithm.denote]

theorem literal_natDegree {C O : Type*} [CommRing O] (ops : RepresentedRing C O) (c : C) :
    (((Algorithm.Expr.lit [c]).map (meaning ops)).eval).natDegree = 0 := by
  rw [literal_meaning]
  simp

end SubexponentialSAT.SqrtLog.LayoutSourceExpression

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutProgramSourceWitness
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A complete typed witness for one actual universal source word: compiler
bytes, full polynomial meaning, degree, and physical byte length. -/
namespace SubexponentialSAT.SqrtLog.LayoutProgram.SourceWitness
open SubexponentialSAT.Subexp SubexponentialSAT.SubexpSymbolicCost SubexponentialSAT.MulticolorTypes
open SubexponentialSAT.SubexpRepresentedRows SubexponentialSAT.SubexpRowInterpolation
open PolynomialExecutorProgram

variable {B d r Q : ℕ} {O : Type*} [CommRing O]

theorem literal (ops : RepresentedRing (Coeff B d) O) (R L : ℕ) (c : Coeff B d)
    (hlen : (SubexpKernelControl.pushWord (RingProgram.flat c)).length ≤ L) :
    Generated ops R L (Polynomial.C (ops.decode c))
      (SubexpKernelControl.pushWord (RingProgram.flat c)) := by
  refine ⟨.lit [c],(LayoutSourceExpression.literal_code c).symm,
    LayoutSourceExpression.literal_meaning ops c,?_,hlen⟩
  rw [LayoutSourceExpression.literal_natDegree]
  exact Nat.zero_le _

theorem literal_zero (ops : RepresentedRing (Coeff B d) O) (R L : ℕ)
    (hlen : (SubexpKernelControl.pushWord (RingProgram.flat ops.zeroRun.1)).length ≤ L) :
    Generated ops R L 0 (SubexpKernelControl.pushWord (RingProgram.flat ops.zeroRun.1)) := by
  simpa only [ops.zero_correct,Polynomial.C_0] using literal ops R L ops.zeroRun.1 hlen

theorem literal_one (ops : RepresentedRing (Coeff B d) O) (R L : ℕ)
    (hlen : (SubexpKernelControl.pushWord (RingProgram.flat ops.oneRun.1)).length ≤ L) :
    Generated ops R L 1 (SubexpKernelControl.pushWord (RingProgram.flat ops.oneRun.1)) := by
  simpa only [ops.one_correct,Polynomial.C_1] using literal ops R L ops.oneRun.1 hlen

end SubexponentialSAT.SqrtLog.LayoutProgram.SourceWitness

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutProgramSourceConfiguration
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.Packing.nonemptyUniversal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Concrete numerical and cache inputs to the source bank. The state predicate
contains byte representations only; it contains no program-service premise. -/
namespace SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp SubexponentialSAT.MulticolorTypes
open IntegerRingLiftProgram RowSelectionProgram

variable {r Q d : ℕ}

theorem Ready.frame {p : Parameters r Q d} {a b : Data} (h : Ready p a)
    (hb : b.stacks=a.stacks) : Ready p b := by
  constructor
  · exact h.work.frame hb
  · intro u y; exact inputFields_store_frame a b p.saved p.start u y (h.input u y) hb
  · exact cachedReady_store_frame p.t p.model p.modulus p.cache _ _ _ a b h.ring hb
  · simpa only [hb] using h.inverseDenominator
  · simpa only [hb] using h.nodes
  · simpa only [hb] using h.limit
  · simpa only [hb] using h.inverses
  · simpa only [hb] using h.negatives
  · simpa only [hb] using h.differences
  · simpa only [hb] using h.ringWidth
  · simpa only [hb] using h.rowWidth
  · simpa only [hb] using h.zero
  · simpa only [hb] using h.one

end SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutProgramSourceDispatch
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Native control branches for source-polynomial lookup. Every literal and
conditional is executed; the universal-branch premise is an actual trace of
that fixed command and is supplied by the native table/emitter composition. -/
namespace SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp

theorem cleared_eq_of_stacks {a b : Data} (h : b.stacks=a.stacks) :
    clearedStacks b=clearedStacks a :=
  congrArg (fun f : Fin 320 → List Bool => fun j => if j∈cleanupPorts then [] else f j) h

/-- Insert the two already-tested covered cases around the concrete native
universal source trace, without changing its output store. -/
theorem covered_attach {a b z : Data} {nc nu : ℕ}
    (hc : Eval compareBlocks nc a b) (h5 : a.regs 5=true) (h7 : b.regs 7=true)
    (hu : Eval (.seq universal cleanup) nu b z) :
    Eval (.seq covered cleanup) (nc+nu+2) a z := by
  cases hu with
  | seq hu hclean =>
    have he := (Eval.ite_true (no:=zero) h5
      (hc.seq (Eval.ite_true (no:=zero) h7 hu))).seq hclean
    change Eval (.seq covered cleanup) _ a z at he
    convert he using 1 ; omega

theorem selected_attach {a z : Data} {n : ℕ} {coveredFlag : Bool}
    (hf : a.regs 4=coveredFlag)
    (he : Eval (.seq (if coveredFlag then covered else uncovered) cleanup) n a z) :
    Eval (.seq (.ite 4 covered uncovered) cleanup) (n+1) a z := by
  cases coveredFlag
  · simp only [Bool.false_eq_true,ite_false] at he
    cases he with
    | seq h hclean =>
      simpa only [Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using
        (Eval.ite_false (yes:=covered) hf h).seq hclean
  · simp only [ite_true, if_true] at he
    cases he with
    | seq h hclean =>
      simpa only [Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using
        (Eval.ite_true (no:=uncovered) hf h).seq hclean

end SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutProgramSourceBankRun
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.Packing.nonemptyUniversal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Complete packed source dispatch from actual metadata. All possible
branches execute native commands and return an exact typed compiler source. -/
namespace SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp SubexponentialSAT.MulticolorTypes
open SubexponentialSAT.Subexp.ConstructivePacking IntegerRingLiftProgram RowSelectionProgram

variable {r Q d D : ℕ}

private theorem unary_inj {x y : Fin D} :
    List.replicate x.val true=List.replicate y.val true ↔ x=y := by
  constructor
  · intro h; apply Fin.ext; simpa using congrArg List.length h
  · rintro rfl; rfl

theorem command_eval_oai (p : Parameters r Q d)
    (P : PackingData (Fin D) (UniversalType r Q 1)) (row col : Fin D)
    (a : Data) (ha : Ready p a) (S : ℕ)
    (hclean : ∀ j∈cleanupPorts,a.stacks j=[])
    (hmeta : a.stacks 306=SelectorProgram.rawRecords (metadataRecords P))
    (hrow : a.stacks 304=List.replicate row.val true)
    (hcol : a.stacks 305=List.replicate col.val true)
    (hsize : ∀ j,(a.stacks j).length ≤ S)
    (hmetadata : ∀ v,MetadataBound (PackingMetadata.value P CollisionProgram.encodeType v) S)
    (hQ : Q ≤ S) (hR : p.R ≤ S) (hW : p.ringWidth.length ≤ S) (hRW : p.rowWidth.length ≤ S) :
    ∃ n ≤ lookupBudget P row col+uniformBudget p S+200*S+300,
      ∃ b : Data, ∃ bytes : List Bool, Eval command n a b ∧
        b.stacks=Function.update a.stacks 287 bytes ∧
        SourceWitness.Generated p.ops p.R (UniversalRowSourceBound.sourceLengthBound S)
          (packedValue P p.rows row col) bytes := by
  let mr := PackingMetadata.value P CollisionProgram.encodeType row
  let mc := PackingMetadata.value P CollisionProgram.encodeType col
  have hkey : Function.Injective (fun v : Fin D=>List.replicate v.val true) := by
    intro x y h; exact unary_inj.mp h
  obtain ⟨nl,hnl,b,hl,hbs,h4,h5⟩ := lookup_eval a (metadataRecords P)
    (List.replicate row.val true) (List.replicate col.val true) mr mc
    (PackingMetadata.lookup_eq P _ _ hkey row) (PackingMetadata.lookup_eq P _ _ hkey col)
    hmeta hrow hcol (lookup_ready hclean)
  change nl ≤ lookupBudget P row col at hnl
  have hbready := ha.metadata mr mc hbs
  have hbsize := metadata_length mr mc S hbs hsize (hmetadata row) (hmetadata col)
  have hbclear := cleared_metadata_eq mr mc hclean hbs
  have hbLit : LiteralReady b := hbready.work.literal
  have hbCmp : CompareReady b := hbready.work.compare
  have hzlen := LayoutSourceExpression.literal_length_le_sourceLengthBound p.ops.zeroRun.1
    (p.hringWidth ▸ hW)
  have holen := LayoutSourceExpression.literal_length_le_sourceLengthBound p.ops.oneRun.1
    (p.hringWidth ▸ hW)
  have hzero := SourceWitness.literal_zero p.ops p.R _ hzlen
  have hone := SourceWitness.literal_one p.ops p.R _ holen
  cases hv : P.lookup row with
  | none =>
    have hb4 : b.regs 4=false := by
      simpa [mr,PackingMetadata.value,hv,GlobalBasisMetadata.Metadata.coveredFlag] using h4
    obtain ⟨nu,hnu,z,hu,hzs⟩ := uncovered_cleanup b hbLit hbCmp S hbsize
    have hs := selected_attach (coveredFlag:=false) hb4 hu
    have hbr : b.stacks 304=List.replicate row.val true := by
      rw [hbs,metadata_frame a mr mc 304 (Or.inr (by decide))]; exact hrow
    have hbc : b.stacks 305=List.replicate col.val true := by
      rw [hbs,metadata_frame a mr mc 305 (Or.inr (by decide))]; exact hcol
    let bytes := SubexpKernelControl.pushWord
      (if row=col then RingProgram.flat p.ops.oneRun.1 else RingProgram.flat p.ops.zeroRun.1)
    refine ⟨nl+(nu+1),by omega,z,bytes,hl.seq hs,?_,?_⟩
    · simpa only [hbclear,hbr,hbc,unary_inj,hbready.one,hbready.zero] using hzs
    · by_cases heq : row=col
      · subst col
        simpa [bytes,packedValue,hv] using hone
      · simpa [bytes,packedValue,hv,heq,eq_comm] using hzero
  | some z =>
    rcases z with ⟨j,u⟩
    have hb4 : b.regs 4=true := by
      simpa [mr,PackingMetadata.value,hv,GlobalBasisMetadata.Metadata.coveredFlag] using h4
    cases hw : P.lookup col with
    | none =>
      have hb5 : b.regs 5=false := by
        simpa [mc,PackingMetadata.value,hw,GlobalBasisMetadata.Metadata.coveredFlag] using h5
      obtain ⟨nu,hnu,z,hu,hzs⟩ := covered_uncovered_cleanup b hbLit hb5 S hbsize
      have hs := selected_attach (coveredFlag:=true) hb4 hu
      refine ⟨nl+(nu+1),by omega,z,SubexpKernelControl.pushWord (RingProgram.flat p.ops.zeroRun.1),hl.seq hs,?_,?_⟩
      · simpa only [hbclear,hbready.zero] using hzs
      · simpa only [packedValue,hv,hw] using hzero
    | some z =>
      rcases z with ⟨k,y⟩
      have hb5 : b.regs 5=true := by
        simpa [mc,PackingMetadata.value,hw,GlobalBasisMetadata.Metadata.coveredFlag] using h5
      have hbu : b.stacks 289=CollisionProgram.encodeType u := by
        simp [hbs,metadataStacks,mr,PackingMetadata.value,hv,GlobalBasisMetadata.Metadata.typeCode]
      have hby : b.stacks 292=CollisionProgram.encodeType y := by
        simp [hbs,metadataStacks,mc,PackingMetadata.value,hw,GlobalBasisMetadata.Metadata.typeCode]
      have hblock : b.stacks 288=b.stacks 291 ↔ j=k := by
        simp [hbs,metadataStacks,mr,mc,PackingMetadata.value,hv,hw,
          GlobalBasisMetadata.Metadata.block,PackingMetadata.unary,Fin.val_inj]
      obtain ⟨nc,hnc,m,hcmp,hms,_,h7⟩ := compareBlocks_eval b hbCmp.1 hbCmp.2.1 hbCmp.2.2.1 hbCmp.2.2.2
      have hmready := hbready.frame hms
      have hmsize : ∀ i,(m.stacks i).length ≤ S := by simpa only [hms] using hbsize
      have hmclear : clearedStacks m=a.stacks := (cleared_eq_of_stacks hms).trans hbclear
      have hnc' : nc ≤ 27*S+32 := by have h1:=hbsize 288; have h2:=hbsize 291; omega
      by_cases heq : j=k
      · have hm7 : m.regs 7=true := by simp [h7,hblock,heq]
        obtain ⟨codes,nu,hnu,z,bytes,hu,hzs,hgen⟩ := universal_generated p m hmready u y
          (by simpa only [hms] using hbu) (by simpa only [hms] using hby) S hmsize hQ hR hW hRW
        have hbound := (nativeBudget_le p S m codes u y
          (hmready.work.work 23 (by decide) (Or.inl (by decide)))
          (hmready.work.work 24 (by decide) (Or.inl (by decide))) hmsize hQ hW hRW).trans
          (universalBudget_le p S u y)
        have hs := selected_attach (coveredFlag:=true) hb4 (covered_attach hcmp hb5 hm7 hu)
        refine ⟨nl+(nc+nu+2+1),by omega,z,bytes,hl.seq hs,?_,?_⟩
        · simpa only [hmclear] using hzs
        · simpa only [packedValue,hv,hw,ite_eq_left heq] using hgen
      · have hm7 : m.regs 7=false := by simp [h7,hblock,heq]
        obtain ⟨nu,hnu,z,hu,hzs⟩ := literal_cleanup_eval 313 (Or.inl rfl) m
          hmready.work.temp hmready.work.literal.2.1 hmready.work.literal.2.2.1
          hmready.work.output S hmsize
        cases hu with
        | seq hli hcl =>
          have hc := (Eval.ite_true (no:=zero) hb5
            (hcmp.seq (Eval.ite_false (yes:=universal) hm7 hli))).seq hcl
          have hs := selected_attach (coveredFlag:=true) hb4 hc
          have h313 := hmsize 313
          refine ⟨_,by omega,z,SubexpKernelControl.pushWord (RingProgram.flat p.ops.zeroRun.1),hl.seq hs,?_,?_⟩
          · simpa only [hmclear,hmready.zero] using hzs
          · simpa only [packedValue,hv,hw,ite_eq_right heq] using hzero

end SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank

end OAI.Algorithms
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank.command_eval_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank.command_eval_oai
