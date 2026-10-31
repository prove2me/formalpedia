-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram.native_relSourceSpec
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T10:46:03.812788+00:00
-- url     : https://prove2.me/submissions/9c8d2cc0-460c-4b4b-b0ea-ce93eddfbed9

import Mathlib
import Definitions.Def_OAIQ081S186
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_LayoutProgram_SourceBank_command_eval

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

end SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutSourceRowsProgramSourceCall
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram
open SubexponentialSAT BitProgram StructuredCalls

theorem sourcePorts_injective : Function.Injective sourcePorts := Fin.castAdd_injective _ _

theorem packedSource_transport (a : Data) (n : ℕ) (rf : Fin 16 → Bool) (bits : List Bool)
    (he : Eval LayoutProgram.SourceBank.command n (projectState id sourcePorts a)
      (⟨rf,Function.update (a.stacks ∘ sourcePorts) 287 bits⟩ : State 16 320)) :
    ∃ e : Data, Eval packedSource (n+1) a e ∧ e.stacks=Function.update a.stacks 287 bits := by
  let out : State 16 320 := ⟨rf,Function.update (a.stacks ∘ sourcePorts) 287 bits⟩
  have hc := eval_liftCommand_from_state LayoutProgram.SourceBank.command 304 287
    id sourcePorts a Function.injective_id sourcePorts_injective he
  refine ⟨embedState id sourcePorts a out,hc,?_⟩
  change Function.extend sourcePorts (Function.update (a.stacks ∘ sourcePorts) 287 bits)
    a.stacks=Function.update a.stacks 287 bits
  rw [ProgramLinking.extend_update sourcePorts_injective]
  have hb := congrArg StructuredProgram.State.stacks
    (embedState_project id sourcePorts a Function.injective_id sourcePorts_injective)
  change Function.extend sourcePorts (a.stacks ∘ sourcePorts) a.stacks=a.stacks at hb
  rw [hb]
  rfl

end SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutSourceRowsProgramSourceFrame
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.Packing.nonemptyUniversal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms


namespace SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram
open SubexponentialSAT BitProgram StructuredCalls
open LayoutProgram
attribute [local simp] Fin.coe_ofNat_eq_mod

theorem sourceReady_index_frame {r Q d : ℕ} (p : SourceBank.Parameters r Q d)
    (a b : SourceBank.Data) (h : SourceBank.Ready p a)
    (hf : ∀ j : Fin 320, j≠304 → j≠305 → b.stacks j=a.stacks j) :
    SourceBank.Ready p b := by
  have hlow : SourceBank.lowStore b=SourceBank.lowStore a := by
    funext i
    apply hf
    all_goals
      intro he
      have hv := congrArg Fin.val he
      have hi := i.isLt
      change i.val=_ at hv
      omega
  have hcleanup : ∀ j∈SourceBank.cleanupPorts, j≠304 ∧ j≠305 := by
    intro j hj
    simp [SourceBank.cleanupPorts] at hj
    constructor <;> intro h <;> subst j <;> simp at hj
  constructor
  · constructor
    · intro j hj hk
      rw [hf j (hcleanup j hj).1 (hcleanup j hj).2]
      exact h.work.work j hj hk
    · rw [hf 319 (by decide) (by decide)]; exact h.work.temp
    · rw [hf 287 (by decide) (by decide)]; exact h.work.output
    · rw [hf 37 (by decide) (by decide)]; exact h.work.count
    · rw [hf 64 (by decide) (by decide)]; exact h.work.tableCount
    · rw [hf 65 (by decide) (by decide)]; exact h.work.tableAccum
    · intro j hj
      rw [hf j (by intro he; subst j; norm_num at hj) (by intro he; subst j; norm_num at hj)]
      exact h.work.low j hj
  · intro u y
    exact SourceBank.inputFields_frame a b p.saved p.start u y (h.input u y) hlow
  · rw [hlow]; exact h.ring
  · rw [hf 252 (by decide) (by decide)]; exact h.inverseDenominator
  · rw [hf 22 (by decide) (by decide)]; exact h.nodes
  · rw [hf 47 (by decide) (by decide)]; exact h.limit
  · rw [hf 308 (by decide) (by decide)]; exact h.inverses
  · rw [hf 309 (by decide) (by decide)]; exact h.negatives
  · rw [hf 310 (by decide) (by decide)]; exact h.differences
  · rw [hf 311 (by decide) (by decide)]; exact h.ringWidth
  · rw [hf 312 (by decide) (by decide)]; exact h.rowWidth
  · rw [hf 313 (by decide) (by decide)]; exact h.zero
  · rw [hf 314 (by decide) (by decide)]; exact h.one

theorem source_fiber_projection (base : Store) (ids : List ℕ) (acc : List Bool) (i : ℕ) :
    (Function.update (fiberState base ids acc) 305 (List.replicate i true)) ∘ sourcePorts=
      Function.update (base ∘ sourcePorts) 305 (List.replicate i true) := by
  funext j
  have hp : (sourcePorts j).val < 320 := j.isLt
  have h328 : sourcePorts j≠328 := by intro he; rw [he] at hp; norm_num at hp
  have h329 : sourcePorts j≠329 := by intro he; rw [he] at hp; norm_num at hp
  have h333 : sourcePorts j≠333 := by intro he; rw [he] at hp; norm_num at hp
  have h305 : sourcePorts j=305 ↔ j=305 := by simp [sourcePorts,Fin.ext_iff]
  simp [Function.comp_def,fiberState,Function.update_apply,h328,h329,h333,h305]

end SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutSourceRowsProgramPacked
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.Packing.nonemptyUniversal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Discharge of the source callback by the actual packed-source dispatcher.
All premises below are stored-byte and cache invariants. -/

namespace SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram
open SubexponentialSAT BitProgram StructuredCalls SubexponentialSAT.Subexp
open SubexponentialSAT.Subexp.ConstructivePacking SubexponentialSAT.MulticolorTypes
open LayoutProgram
attribute [local simp] Fin.coe_ofNat_eq_mod

theorem lookupBudget_le {r Q D : ℕ}
    (P : PackingData (Fin D) (UniversalType r Q 1)) (row col : Fin D) (S : ℕ)
    (hm : (SelectorProgram.rawRecords (SourceBank.metadataRecords P)).length ≤ S)
    (hr : row.val ≤ S) (hc : col.val ≤ S) :
    SourceBank.lookupBudget P row col ≤ 800*(2*S+1)^2+1 := by
  unfold SourceBank.lookupBudget GlobalBasisMetadata.volume
  simp only [List.length_replicate]
  calc
    _ ≤ 400*(2*S+1)^2+400*(2*S+1)^2+1 := by gcongr <;> omega
    _ = _ := by ring

theorem native_relSourceSpec_oai {r Q d D : ℕ} (p : SourceBank.Parameters r Q d)
    (P : PackingData (Fin D) (UniversalType r Q 1)) (row : Fin D)
    (base : Store) (I S : ℕ) (hID : I < D) (hIS : I ≤ S)
    (hready : SourceBank.Ready p (⟨fun _ => false,base ∘ sourcePorts⟩ : SourceBank.Data))
    (hclean : ∀ j∈SourceBank.cleanupPorts, base (sourcePorts j)=[])
    (hmeta : base 306=SelectorProgram.rawRecords (SourceBank.metadataRecords P))
    (hrow : base 304=List.replicate row.val true)
    (hsize : ∀ j : Fin 320, (base (sourcePorts j)).length ≤ S)
    (hmetadata : ∀ v,SourceBank.MetadataBound (PackingMetadata.value P CollisionProgram.encodeType v) S)
    (hQ : Q ≤ S) (hR : p.R ≤ S) (hW : p.ringWidth.length ≤ S) (hRW : p.rowWidth.length ≤ S) :
    RelSourceSpec packedSource base
      (fun e : Algorithm.Expr (List (PolynomialExecutorProgram.Coeff (SubexpLiftRing.baseWidth 3 p.t) d)) =>
        SubexpPostfixControl.serializeCode DensePolynomialProgram.encode e.compile)
      (TypedSourceRel DensePolynomialProgram.encode (PolynomialExecutorProgram.meaning p.ops)
        (packedSourceValue p P row) (Subexp.UniversalRowSourceBound.sourceLengthBound S))
      I (nativeSourceBudget p S) (Subexp.UniversalRowSourceBound.sourceLengthBound S) := by
  intro i hi ids acc regs
  let col : Fin D := ⟨i,by omega⟩
  let a : Data := ⟨regs,Function.update (fiberState base ids acc) 305 (List.replicate i true)⟩
  let small := projectState id sourcePorts a
  have hs : small.stacks=Function.update (base ∘ sourcePorts) 305 (List.replicate i true) :=
    source_fiber_projection base ids acc i
  have ha : SourceBank.Ready p small := sourceReady_index_frame p _ small hready (by
    intro j hj hk
    simp [hs,hk])
  have hc : ∀ j∈SourceBank.cleanupPorts,small.stacks j=[] := by
    intro j hj
    have hne : j≠305 := by
      intro h
      subst j
      simp [SourceBank.cleanupPorts] at hj
    simpa [hs,Function.update_apply,hne,Function.comp_def] using hclean j hj
  have hss : ∀ j,(small.stacks j).length ≤ S := by
    intro j
    by_cases hj : j=305
    · subst j; simp only [hs,Function.update_self,List.length_replicate]; omega
    · simpa [hs,Function.update_apply,hj,Function.comp_def] using hsize j
  obtain ⟨n,hn,b,bytes,he,hb,hgen⟩ := SourceBank.command_eval p P row col small ha S hc
    (by simpa [hs,sourcePorts] using hmeta) (by simpa [hs,sourcePorts] using hrow)
    (by simp [hs,col]) hss hmetadata hQ hR hW hRW
  obtain ⟨e,hbytes,hm,hd,hl⟩ := hgen
  have hb' : b=(⟨b.regs,Function.update (a.stacks ∘ sourcePorts) 287 bytes⟩ : SourceBank.Data) := by
    apply SubexpScanPrimitives.state_ext
    · rfl
    · exact hb
  rw [hb'] at he
  obtain ⟨out,hout,host⟩ := packedSource_transport a n b.regs bytes he
  have ho : out=(⟨out.regs,Function.update a.stacks 287 bytes⟩ : Data) := by
    apply SubexpScanPrimitives.state_ext
    · rfl
    · exact host
  rw [ho,hbytes] at hout
  refine ⟨e,n+1,out.regs,⟨?_,?_⟩,?_,?_,hout⟩
  · simpa [packedSourceValue,col,show i < D by omega] using hm
  · simpa only [hbytes] using hl
  · simpa only [hbytes] using hl
  · have hml : (SelectorProgram.rawRecords (SourceBank.metadataRecords P)).length ≤ S := by
      simpa [sourcePorts,hmeta] using hsize 306
    have hrl : row.val ≤ S := by simpa [sourcePorts,hrow] using hsize 304
    have hcl : col.val ≤ S := by dsimp [col]; omega
    have hbnd := lookupBudget_le P row col S hml hrl hcl
    unfold nativeSourceBudget
    omega

end SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram

end OAI.Algorithms
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram.native_relSourceSpec_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram.native_relSourceSpec_oai
