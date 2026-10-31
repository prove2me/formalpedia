-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram.staged_native_row_relSourceSpec
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T10:47:15.960996+00:00
-- url     : https://prove2.me/submissions/2a4495b2-3442-4264-8c4c-3c277a82b4b9

import Mathlib
import Definitions.Def_OAIQ081S186
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_LayoutSourceRowsProgram_native_relSourceSpec

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

theorem WorkReady.frame {a b : Data} (h : WorkReady a) (hb : b.stacks=a.stacks) : WorkReady b := by
  constructor
  · intro j hj hk; rw [hb]; exact h.work j hj hk
  · rw [hb]; exact h.temp
  · rw [hb]; exact h.output
  · rw [hb]; exact h.count
  · rw [hb]; exact h.tableCount
  · rw [hb]; exact h.tableAccum
  · intro j hj; rw [hb]; exact h.low j hj

end SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank

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
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutSourceRowsProgramCore
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Native framing and postfix accumulation for complete source rows. The
local bank is relocated as a whole by the leaf controller. No polynomial
value is an instruction or an input to these controllers. -/
namespace SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram
open SubexponentialSAT BitProgram StructuredCalls

theorem ExecutesIn.seq {a b : Code} {A B : ℕ} {s t u : Store}
    (ha : ExecutesIn a A s t) (hb : ExecutesIn b B t u) :
    ExecutesIn (.seq a b) (A+B) s u := by
  intro regs
  obtain ⟨na,ra,hna,hea⟩ := ha regs
  obtain ⟨nb,rb,hnb,heb⟩ := hb ra
  exact ⟨na+nb,rb,by omega,hea.seq heb⟩

theorem transfer_run (src dst : Fin 340) (s : Store) (h : src ≠ dst) :
    ExecutesIn (transfer src dst) (3*(s src).length+3) s
      (Function.update (Function.update s src []) dst ((s src).reverse++s dst)) := by
  intro regs
  have he := SubexpScanPrimitives.transfer_eval (⟨regs,s⟩ : Data) src dst 0 1 h (by decide)
  exact ⟨_,_,le_rfl,he⟩

end SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutSourceRowsProgramPackedModel
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram
open SubexponentialSAT BitProgram StructuredCalls SubexponentialSAT.Subexp
open SubexponentialSAT.Subexp.ConstructivePacking SubexponentialSAT.MulticolorTypes LayoutProgram
attribute [local simp] Fin.coe_ofNat_eq_mod

theorem rowState_source_projection (base : Store) (j : ℕ) (remaining acc : List Bool) :
    rowState base j remaining acc ∘ sourcePorts=base ∘ sourcePorts := by
  funext i
  have hp : (sourcePorts i).val < 320 := i.isLt
  have h320 : sourcePorts i≠320 := by intro he; rw [he] at hp; norm_num at hp
  have h331 : sourcePorts i≠331 := by intro he; rw [he] at hp; norm_num at hp
  have h332 : sourcePorts i≠332 := by intro he; rw [he] at hp; norm_num at hp
  simp [rowState,h320,h331,h332]

end SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutSourceRowsProgramStaging
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The source numerator uses empty scalar work tapes5/10. The polynomial
executor retains its modulus/width there. Two reversible transfers isolate
these phases without touching the native high arithmetic cache. -/
namespace SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram
open SubexponentialSAT BitProgram StructuredCalls
attribute [local simp] Fin.coe_ofNat_eq_mod

theorem stageScalarWork_run (s : Store) (h335 : s 335=[]) (h336 : s 336=[]) :
    ExecutesIn stageScalarWork (3*(s 5).length+3*(s 10).length+6) s (stagedSourceStore s) := by
  let s1 := Function.update (Function.update s 5 []) 335 (s 5).reverse
  have h1 : ExecutesIn (transfer 5 335) (3*(s 5).length+3) s s1 := by
    simpa [s1,h335] using transfer_run 5 335 s (by decide)
  have h2 := transfer_run 10 336 s1 (by decide)
  have he : Function.update (Function.update s1 10 []) 336 ((s1 10).reverse++s1 336)=stagedSourceStore s := by
    funext i
    simp only [s1,stagedSourceStore,clearedSourceStore,Function.update_apply]
    split_ifs <;> simp_all
  rw [he] at h2
  convert h1.seq h2 using 1 <;> simp [stageScalarWork,s1] ; omega

theorem unstageScalarWork_run (s : Store) (bits : List Bool)
    (h335 : s 335=[]) (h336 : s 336=[]) :
    ExecutesIn unstageScalarWork (3*(s 5).length+3*(s 10).length+6)
      (Function.update (stagedSourceStore s) 287 bits) (Function.update s 287 bits) := by
  let a := Function.update (stagedSourceStore s) 287 bits
  let b := Function.update (Function.update a 335 []) 5 ((a 335).reverse++a 5)
  have h1 := transfer_run 335 5 a (by decide)
  have h2 := transfer_run 336 10 b (by decide)
  have he : Function.update (Function.update b 336 []) 10 ((b 336).reverse++b 10)=
      Function.update s 287 bits := by
    funext i
    by_cases hi335 : i=335
    · subst i; simp [b,a,stagedSourceStore,clearedSourceStore,h335]
    by_cases hi336 : i=336
    · subst i; simp [b,a,stagedSourceStore,clearedSourceStore,h336]
    by_cases hi5 : i=5
    · subst i; simp [b,a,stagedSourceStore,clearedSourceStore]
    by_cases hi10 : i=10
    · subst i; simp [b,a,stagedSourceStore,clearedSourceStore]
    by_cases hi287 : i=287
    · subst i; simp [b,a,stagedSourceStore,clearedSourceStore]
    simp [b,a,stagedSourceStore,clearedSourceStore,
      hi335,hi336,hi5,hi10,hi287]
  rw [he] at h2
  convert h1.seq h2 using 1 <;> simp [unstageScalarWork,b,a,stagedSourceStore,clearedSourceStore] ; omega

theorem stagedSourceStore_projection (s : Store) :
    stagedSourceStore s ∘ sourcePorts=clearedSourceStore s ∘ sourcePorts := by
  funext i
  have hi : (sourcePorts i).val < 320 := i.isLt
  have h335 : sourcePorts i≠335 := by intro h; rw [h] at hi; norm_num at hi
  have h336 : sourcePorts i≠336 := by intro h; rw [h] at hi; norm_num at hi
  simp [stagedSourceStore,h335,h336]

theorem stagedSourceStore_fiber (s : Store) (ids : List ℕ) (acc : List Bool) (i : ℕ) :
    stagedSourceStore (Function.update (fiberState s ids acc) 305 (List.replicate i true))=
      Function.update (fiberState (stagedSourceStore s) ids acc) 305 (List.replicate i true) := by
  funext j
  simp only [stagedSourceStore,clearedSourceStore,fiberState,Function.update_apply]
  split_ifs <;> simp_all

theorem stagedPackedSource_eval {W : Type*} (encode : W → List Bool) (R : W → Prop)
    (K : ℕ) (s : Store) (h335 : s 335=[]) (h336 : s 336=[])
    (hraw : ∀ regs,∃ w n rf,R w ∧ n ≤ K ∧ Eval packedSource n
      (⟨regs,stagedSourceStore s⟩ : Data)
      (⟨rf,Function.update (stagedSourceStore s) 287 (encode w)⟩ : Data))
    (regs : Fin 16 → Bool) :
    ∃ w n rf,R w ∧ n ≤ K+6*(s 5).length+6*(s 10).length+12 ∧
      Eval stagedPackedSource n (⟨regs,s⟩ : Data)
        (⟨rf,Function.update s 287 (encode w)⟩ : Data) := by
  obtain ⟨n1,r1,hn1,he1⟩ := stageScalarWork_run s h335 h336 regs
  obtain ⟨w,n2,r2,hw,hn2,he2⟩ := hraw r1
  obtain ⟨n3,r3,hn3,he3⟩ := unstageScalarWork_run s (encode w) h335 h336 r2
  exact ⟨w,n1+(n2+n3),r3,hw,by omega,he1.seq (he2.seq he3)⟩

end SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutSourceRowsProgramStagedPacked
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.Packing.nonemptyUniversal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram
open SubexponentialSAT BitProgram StructuredCalls SubexponentialSAT.Subexp
open SubexponentialSAT.Subexp.ConstructivePacking SubexponentialSAT.MulticolorTypes LayoutProgram
attribute [local simp] Fin.coe_ofNat_eq_mod

theorem staged_native_relSourceSpec {r Q d D : ℕ} (p : SourceBank.Parameters r Q d)
    (P : PackingData (Fin D) (UniversalType r Q 1)) (row : Fin D)
    (base : Store) (I S : ℕ) (hID : I < D) (hIS : I ≤ S)
    (h335 : base 335=[]) (h336 : base 336=[])
    (hready : SourceBank.Ready p (⟨fun _ => false,clearedSourceStore base ∘ sourcePorts⟩ : SourceBank.Data))
    (hclean : ∀ j∈SourceBank.cleanupPorts,base (sourcePorts j)=[])
    (hmeta : base 306=SelectorProgram.rawRecords (SourceBank.metadataRecords P))
    (hrow : base 304=List.replicate row.val true)
    (hsize : ∀ j : Fin 320,(base (sourcePorts j)).length ≤ S)
    (hmetadata : ∀ v,SourceBank.MetadataBound (PackingMetadata.value P CollisionProgram.encodeType v) S)
    (hQ : Q ≤ S) (hR : p.R ≤ S) (hW : p.ringWidth.length ≤ S) (hRW : p.rowWidth.length ≤ S) :
    RelSourceSpec stagedPackedSource base
      (fun e : Algorithm.Expr (List (PolynomialExecutorProgram.Coeff (SubexpLiftRing.baseWidth 3 p.t) d)) =>
        SubexpPostfixControl.serializeCode DensePolynomialProgram.encode e.compile)
      (TypedSourceRel DensePolynomialProgram.encode (PolynomialExecutorProgram.meaning p.ops)
        (packedSourceValue p P row) (Subexp.UniversalRowSourceBound.sourceLengthBound S))
      I (stagedSourceBudget p S) (Subexp.UniversalRowSourceBound.sourceLengthBound S) := by
  have hp := stagedSourceStore_projection base
  have heq (j : Fin 320) : stagedSourceStore base (sourcePorts j)=clearedSourceStore base (sourcePorts j) :=
    congrFun hp j
  have hc : ∀ j∈SourceBank.cleanupPorts,stagedSourceStore base (sourcePorts j)=[] := by
    intro j hj
    rw [heq]
    simp only [clearedSourceStore,Function.update_apply]
    split_ifs <;> first | rfl | exact hclean j hj
  have hz : ∀ j : Fin 320,(stagedSourceStore base (sourcePorts j)).length ≤ S := by
    intro j
    rw [heq]
    simp only [clearedSourceStore,Function.update_apply]
    split_ifs <;> first | exact Nat.zero_le _ | exact hsize j
  have raw := native_relSourceSpec p P row (stagedSourceStore base) I S hID hIS
    (hready.frame hp) hc
    (by simpa [stagedSourceStore,clearedSourceStore] using hmeta)
    (by simpa [stagedSourceStore,clearedSourceStore] using hrow)
    hz hmetadata hQ hR hW hRW
  intro i hi ids acc regs
  let st := Function.update (fiberState base ids acc) 305 (List.replicate i true)
  obtain ⟨e,n,rf,hr,hn,he⟩ := stagedPackedSource_eval _
    (TypedSourceRel DensePolynomialProgram.encode (PolynomialExecutorProgram.meaning p.ops)
      (packedSourceValue p P row) (Subexp.UniversalRowSourceBound.sourceLengthBound S) i)
    (nativeSourceBudget p S) st
    (by simp [st,fiberState,h335]) (by simp [st,fiberState,h336]) (by
      intro rr
      obtain ⟨e,k,rr',hr,_,hk,he⟩ := raw i hi ids acc rr
      exact ⟨e,k,rr',hr,hk,by simpa only [st,stagedSourceStore_fiber] using he⟩) regs
  refine ⟨e,n,rf,hr,hr.2,?_,he⟩
  have h5 : (st 5).length ≤ S := by simpa [st,fiberState,sourcePorts] using hsize 5
  have h10 : (st 10).length ≤ S := by simpa [st,fiberState,sourcePorts] using hsize 10
  unfold stagedSourceBudget
  omega

theorem cleared_rowState_source_projection (base : Store) (j : ℕ) (remaining acc : List Bool) :
    clearedSourceStore (rowState base j remaining acc) ∘ sourcePorts=
      clearedSourceStore base ∘ sourcePorts := by
  funext i
  have h := congrFun (rowState_source_projection base j remaining acc) i
  simp only [Function.comp_def,clearedSourceStore,Function.update_apply]
  split_ifs <;> first | rfl | exact h

theorem staged_native_row_relSourceSpec_oai {r Q d D : ℕ} (p : SourceBank.Parameters r Q d)
    (P : PackingData (Fin D) (UniversalType r Q 1)) (row : Fin D)
    (base : Store) (I S : ℕ) (hID : I < D) (hIS : I ≤ S)
    (h335 : base 335=[]) (h336 : base 336=[])
    (hready : SourceBank.Ready p (⟨fun _ => false,clearedSourceStore base ∘ sourcePorts⟩ : SourceBank.Data))
    (hclean : ∀ j∈SourceBank.cleanupPorts,base (sourcePorts j)=[])
    (hmeta : base 306=SelectorProgram.rawRecords (SourceBank.metadataRecords P))
    (hrow : base 304=List.replicate row.val true)
    (hsize : ∀ j : Fin 320,(base (sourcePorts j)).length ≤ S)
    (hmetadata : ∀ v,SourceBank.MetadataBound (PackingMetadata.value P CollisionProgram.encodeType v) S)
    (hQ : Q ≤ S) (hR : p.R ≤ S) (hW : p.ringWidth.length ≤ S) (hRW : p.rowWidth.length ≤ S)
    (j : ℕ) (remaining acc : List Bool) :
    RelSourceSpec stagedPackedSource (rowState base j remaining acc)
      (fun e : Algorithm.Expr (List (PolynomialExecutorProgram.Coeff (SubexpLiftRing.baseWidth 3 p.t) d)) =>
        SubexpPostfixControl.serializeCode DensePolynomialProgram.encode e.compile)
      (TypedSourceRel DensePolynomialProgram.encode (PolynomialExecutorProgram.meaning p.ops)
        (packedSourceValue p P row) (Subexp.UniversalRowSourceBound.sourceLengthBound S))
      I (stagedSourceBudget p S) (Subexp.UniversalRowSourceBound.sourceLengthBound S) := by
  have heq := rowState_source_projection base j remaining acc
  have he (i : Fin 320) : (rowState base j remaining acc) (sourcePorts i)=base (sourcePorts i) :=
    congrFun heq i
  exact staged_native_relSourceSpec p P row _ I S hID hIS
    (by simp [rowState,h335]) (by simp [rowState,h336])
    (hready.frame (cleared_rowState_source_projection base j remaining acc))
    (fun i hi => (he i).trans (hclean i hi))
    (by simpa [sourcePorts] using (he 306).trans hmeta)
    (by simpa [sourcePorts] using (he 304).trans hrow)
    (fun i => by rw [he]; exact hsize i) hmetadata hQ hR hW hRW

end SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram

end OAI.Algorithms
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram.staged_native_row_relSourceSpec_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram.staged_native_row_relSourceSpec_oai
