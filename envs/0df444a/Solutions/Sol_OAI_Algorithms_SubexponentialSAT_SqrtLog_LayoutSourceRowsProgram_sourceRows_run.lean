-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram.sourceRows_run
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T10:46:28.01935+00:00
-- url     : https://prove2.me/submissions/6bc19b27-e274-47b4-b117-230c13e917c9

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S186
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_LayoutSourceRowsProgram_sourceRows_absent_model
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_LayoutSourceRowsProgram_sourceRows_present_from_rows
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_LayoutSourceRowsProgram_sourceRows_relSpec
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_LayoutSourceRowsProgram_staged_native_row_relSourceSpec
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_LayoutSourceRowsProgramReadiness_model_ready_of_low_agreement

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutOwnerFiberProgramBounds
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LayoutOwnerFiberProgram
open SubexponentialSAT BitProgram StructuredCalls

theorem mem_fiberIndices_bounds (query index : ℕ) (ps : List (ℕ × ℕ))
    {i : ℕ} (hi : i ∈ fiberIndices query index ps) :
    index ≤ i ∧ i < index+ps.length := by
  induction ps generalizing index with
  | nil => simp [fiberIndices] at hi
  | cons p ps ih =>
      by_cases h : p.1=query
      · simp only [fiberIndices,h,ite_true, if_true,List.mem_cons] at hi
        rcases hi with rfl | hi
        · simp
        · have hh := ih (index+1) hi
          simp only [List.length_cons]
          omega
      · simp only [fiberIndices,h,ite_false] at hi
        have hh := ih (index+1) hi
        simp only [List.length_cons]
        omega

theorem mem_fiberIndices_lt (query : ℕ) (ps : List (ℕ × ℕ))
    {i : ℕ} (hi : i ∈ fiberIndices query 0 ps) : i < ps.length := by
  have hh := mem_fiberIndices_bounds query 0 ps hi
  omega

end SubexponentialSAT.SqrtLog.LayoutOwnerFiberProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutSourcePlanLookup
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Full pair-plan lookup at the source-row ABI. All query construction, record
comparison, index increments and cleanup are native paid instructions. -/
namespace SubexponentialSAT.SqrtLog.LayoutSourcePlanLookup
open SubexponentialSAT BitProgram StructuredCalls

theorem pair_index_mem (ps : List (ℕ × ℕ)) (p : ℕ × ℕ) (h : p ∈ ps) :
    ps.idxOf p < ps.length ∧ ps[ps.idxOf p]?=some p := by
  constructor
  · simpa only [List.idxOf,beq_eq_decide] using List.idxOf_lt_length_iff.mpr h
  · simpa only [List.idxOf,beq_eq_decide] using List.getElem?_idxOf h

end SubexponentialSAT.SqrtLog.LayoutSourcePlanLookup

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutSourceRowsProgramSemantics
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The exact polynomial computed by the native owner-fiber traversal. -/
namespace SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram
open SubexponentialSAT
open scoped BigOperators

variable {A : Type*}

section Polynomial
variable [CommRing A]

theorem list_sum_degree (ps : List (Polynomial A)) (R : ℕ)
    (h : ∀ p∈ps, p.natDegree ≤ R) : ps.sum.natDegree ≤ R := by
  induction ps with
  | nil => simp
  | cons p ps ih =>
      have hp := h p (by simp)
      have ht := ih (by intro q hq; exact h q (by simp [hq]))
      exact (Polynomial.natDegree_add_le p ps.sum).trans (max_le hp ht)

theorem ownerSum_degree (ps : List (ℕ × ℕ)) (owner : ℕ) (value : ℕ → Polynomial A) (R : ℕ)
    (h : ∀ i∈LayoutOwnerFiberProgram.fiberIndices owner 0 ps, (value i).natDegree ≤ R) :
    (ownerSum ps owner value).natDegree ≤ R := by
  apply list_sum_degree
  intro p hp
  obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hp
  exact h i hi

theorem trunc_full_degree (P : Polynomial A) (R : ℕ) (h : P.natDegree ≤ R) :
    Truncation.trunc (R+1) P=P := by
  ext j
  rw [Truncation.coeff_trunc]
  split_ifs with hj
  · rfl
  · symm
    apply Polynomial.coeff_eq_zero_of_natDegree_lt
    omega

/-- The full T cutoff is independent of the later Z-jet cutoff. -/
theorem ownerSum_full_degree (ps : List (ℕ × ℕ)) (owner : ℕ) (value : ℕ → Polynomial A) (R : ℕ)
    (h : ∀ i∈LayoutOwnerFiberProgram.fiberIndices owner 0 ps, (value i).natDegree ≤ R) :
    Truncation.trunc (R+1) (ownerSum ps owner value)=ownerSum ps owner value :=
  trunc_full_degree _ R (ownerSum_degree ps owner value R h)

end Polynomial
end SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutSourceRowsProgramModelAssembly
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Composition of the actual outer controller and the actual polynomial
executor. Only the concrete packed-source command contract is supplied by
the layout dispatcher; arithmetic and row traversal are fully discharged. -/
namespace SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram
open SubexponentialSAT BitProgram StructuredCalls
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing
attribute [local simp] Fin.coe_ofNat_eq_mod

theorem sourceRows_present_model (t : ℕ) (ht : 0 < t) {d : ℕ} (hd : 0 < d)
    (a : RingModel.Data d) (M : SubexpPreparedQuartic.Modulus 3 t)
    (cache : RingProgram.ScalarCache 3 t) (hz : BinaryArithmetic.toNat cache.zero.val < 3^t)
    (R : ℕ) (width : List Bool) (frame : Fin 6 → List Bool)
    (source : Code) (s : Store) (v N f K L : ℕ) (ps : List (ℕ × ℕ))
    (value : ℕ → Polynomial (a.O t))
    (hinit : LayoutSourceRowsProgramInitialize.Ready (s ∘ initializationPorts)
      (R+1) (d*baseWidth 3 t))
    (hv : s 233=LayoutSourcePlanLookup.unary v)
    (hN : s 212=LayoutSourcePlanLookup.unary N)
    (hf : s 216=LayoutSourcePlanLookup.unary f)
    (hplan : s 337=LayoutOwnerFiberProgram.stream ps)
    (hmem : (v,N+f) ∈ ps)
    (hlookup : LayoutSourcePlanLookup.Native.Clean
      (⟨fun _ => false,initializeFinish s (R+1) (d*baseWidth 3 t)⟩ : Data))
    (hclean : RowsClean (preparedSourceStore s (R+1) (d*baseWidth 3 t) ps v N f)) (hwork : RowWorkClean (preparedSourceStore s (R+1) (d*baseWidth 3 t) ps v N f))
    (howner : ∀ i : Fin 11, 2 ≤ i.val → (preparedSourceStore s (R+1) (d*baseWidth 3 t) ps v N f) (ownerStacks i)=[])
    (H : DensePolynomialProgram.PairSpec.BaseReady 3 t M cache
      (HornerProgram.modelTable t a M cache) (s ∘ executorPorts) width frame)
    (E : LayoutSourceRowsProgramReadiness.Empty s)
    (hsource : ∀ j, j < N → ∀ remaining acc,
      RelSourceSpec source (rowState (preparedSourceStore s (R+1) (d*baseWidth 3 t) ps v N f) j remaining acc)
        (fun e : Algorithm.Expr (List (PolynomialExecutorProgram.Coeff (baseWidth 3 t) d)) =>
          SubexpPostfixControl.serializeCode DensePolynomialProgram.encode e.compile)
        (TypedSourceRel DensePolynomialProgram.encode
          (PolynomialExecutorProgram.meaning (RingProgram.modelRing t ht hd a M cache)) value L)
        (ps.length-1) K L)
    (hdegree : ∀ i, i < ps.length → (value i).natDegree ≤ R)
    (regs : Fin 16 → Bool) :
    ∃ rows n rf,
      RowProperty DensePolynomialProgram.encode
        (fun j out => PolynomialExecutorProgram.meaning (RingProgram.modelRing t ht hd a M cache) out=
          ownerSum ps j value) ((R+1)*(d*baseWidth 3 t)) 0 rows ∧ rows.length=N ∧
      n ≤ LayoutSourceRowsProgramInitialize.budget (R+1) (d*baseWidth 3 t)+
        LayoutSourcePlanLookup.pairBudget v N f ps+
        N*(uniformRowBudget N ps (ps.length-1) K L (R+1) d (baseWidth 3 t)
          ((preparedSourceStore s (R+1) (d*baseWidth 3 t) ps v N f) 21).length ((preparedSourceStore s (R+1) (d*baseWidth 3 t) ps v N f) 26).length+19*((R+1)*(d*baseWidth 3 t))+39)+
        2*(ps.idxOf (v,N+f))+23 ∧
      Eval (sourceRowsWith source) n (⟨regs,s⟩ : Data)
        (⟨rf,Function.update (initializeFinish s (R+1) (d*baseWidth 3 t)) 205
          (Encoding.encodeList DensePolynomialProgram.encode rows)⟩ : Data) := by
  let p := preparedSourceStore s (R+1) (d*baseWidth 3 t) ps v N f
  have Hready := LayoutSourceRowsProgramReadiness.model_ready_of_low_agreement
    t a M cache hz s p (R+1) width frame H E (by
      intro i hi
      have hn : i≠304 := by intro he; subst i; norm_num at hi
      simp [p,preparedSourceStore,hn])
  have hsp : p 337=LayoutOwnerFiberProgram.stream ps := by
    simpa [p,preparedSourceStore,initializeFinish] using hplan
  have hids : ∀ j, j < N → ∀ i∈LayoutOwnerFiberProgram.fiberIndices j 0 ps,
      i ≤ ps.length-1 := by
    intro j hj i hi
    have hl := LayoutOwnerFiberProgram.mem_fiberIndices_lt j ps hi
    omega
  have hrs := sourceRows_relSpec t ht hd a M cache hz (R+1) width frame
    source p (ps.length-1) K L N ps (fun _ => value) hsource hsp howner hwork hids Hready
  have hrfull : RelRowSpec (sourceRowWith source) p DensePolynomialProgram.encode
      (fun j out => PolynomialExecutorProgram.meaning (RingProgram.modelRing t ht hd a M cache) out=
        ownerSum ps j value) N
      (uniformRowBudget N ps (ps.length-1) K L (R+1) d (baseWidth 3 t)
        (p 21).length (p 26).length) ((R+1)*(d*baseWidth 3 t)) := by
    intro j hj remaining acc rr
    obtain ⟨out,n,rf,hm,hl,hn,he⟩ := hrs j hj remaining acc rr
    refine ⟨out,n,rf,?_,hl,hn,he⟩
    rw [ownerSum_full_degree ps j value R (by
      intro i hi
      exact hdegree i (LayoutOwnerFiberProgram.mem_fiberIndices_lt j ps hi))] at hm
    exact hm
  exact sourceRows_present_from_rows source s (R+1) (d*baseWidth 3 t) v N f ps
    hinit hv hN hf hplan hmem hlookup DensePolynomialProgram.encode _ _ _ hrfull hclean regs

end SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutSourceRowsProgramSourceMeaning
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.Packing.nonemptyUniversal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram
open SubexponentialSAT BitProgram StructuredCalls
open SubexponentialSAT.Subexp.ConstructivePacking SubexponentialSAT.MulticolorTypes LayoutProgram

theorem packedSourceValue_degree {r Q d D : ℕ} (p : SourceBank.Parameters r Q d)
    (P : PackingData (Fin D) (UniversalType r Q 1)) (row : Fin D) (i : ℕ) :
    (packedSourceValue p P row i).natDegree ≤ p.R := by
  unfold packedSourceValue
  split_ifs with hi
  · unfold packedValue
    split
    · split_ifs <;> simp
    · split
      · simp
      · split_ifs
        · exact LayoutScaledMatrices.sourceRow_degree _ _ _ _ _ _ _
        · simp
  · simp

end SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutSourceRowsProgramNative
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.Packing.nonemptyUniversal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Complete source-table execution from physical layout metadata and ring
caches. No polynomial table or source-command service is an input. -/
namespace SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram
open SubexponentialSAT BitProgram StructuredCalls SubexponentialSAT.Subexp
open SubexponentialSAT.Subexp.ConstructivePacking SubexponentialSAT.MulticolorTypes LayoutProgram
open SubexponentialSAT.SubexpLiftRing

theorem sourceRows_run_oai {r Q d : ℕ} (p : SourceBank.Parameters r Q d)
    (ps : List (ℕ × ℕ)) (P : PackingData (Fin ps.length) (UniversalType r Q 1))
    (s : Store) (v N f S : ℕ) (width : List Bool) (frame : Fin 6 → List Bool)
    (hinit : LayoutSourceRowsProgramInitialize.Ready (s ∘ initializationPorts)
      (p.R+1) (d*baseWidth 3 p.t))
    (hv : s 233=LayoutSourcePlanLookup.unary v)
    (hN : s 212=LayoutSourcePlanLookup.unary N)
    (hf : s 216=LayoutSourcePlanLookup.unary f)
    (hplan : s 337=LayoutOwnerFiberProgram.stream ps)
    (hlookup : LayoutSourcePlanLookup.Native.Clean
      (⟨fun _ => false,initializeFinish s (p.R+1) (d*baseWidth 3 p.t)⟩ : Data))
    (hclean : RowsClean (preparedSourceStore s (p.R+1) (d*baseWidth 3 p.t) ps v N f))
    (hwork : RowWorkClean (preparedSourceStore s (p.R+1) (d*baseWidth 3 p.t) ps v N f))
    (howner : ∀ i : Fin 11, (2 : ℕ) ≤ i.val →
      (preparedSourceStore s (p.R+1) (d*baseWidth 3 p.t) ps v N f) (ownerStacks i)=[])
    (H : DensePolynomialProgram.PairSpec.BaseReady 3 p.t p.modulus p.cache
      (HornerProgram.modelTable p.t p.model p.modulus p.cache) (s ∘ executorPorts) width frame)
    (E : LayoutSourceRowsProgramReadiness.Empty s)
    (hready : SourceBank.Ready p (⟨fun _ => false,
      clearedSourceStore (preparedSourceStore s (p.R+1) (d*baseWidth 3 p.t) ps v N f) ∘ sourcePorts⟩ : SourceBank.Data))
    (hsourceClean : ∀ j∈SourceBank.cleanupPorts,
      (preparedSourceStore s (p.R+1) (d*baseWidth 3 p.t) ps v N f) (sourcePorts j)=[])
    (hmeta : s 306=SelectorProgram.rawRecords (SourceBank.metadataRecords P))
    (hsize : ∀ j : Fin 320,
      ((preparedSourceStore s (p.R+1) (d*baseWidth 3 p.t) ps v N f) (sourcePorts j)).length ≤ S)
    (hmetadata : ∀ x,SourceBank.MetadataBound (PackingMetadata.value P CollisionProgram.encodeType x) S)
    (hD : ps.length ≤ S) (hQ : Q ≤ S) (hR : p.R ≤ S)
    (hW : p.ringWidth.length ≤ S) (hRW : p.rowWidth.length ≤ S)
    (regs : Fin 16 → Bool) :
    ∃ rows n rf,
      RowProperty DensePolynomialProgram.encode
        (fun j out => PolynomialExecutorProgram.meaning p.ops out=
          sourceRowFamily ps N f v (totalPackedSource p P) j)
        ((p.R+1)*(d*baseWidth 3 p.t)) 0 rows ∧ rows.length=N ∧
      n ≤ nativeRowsBudget p s v N f S ps ∧
      Eval sourceRows n (⟨regs,s⟩ : Data)
        (⟨rf,Function.update (initializeFinish s (p.R+1) (d*baseWidth 3 p.t)) 205
          (Encoding.encodeList DensePolynomialProgram.encode rows)⟩ : Data) := by
  by_cases hmem : (v,N+f)∈ps
  · have hidx := (LayoutSourcePlanLookup.pair_index_mem ps (v,N+f) hmem).1
    let row : Fin ps.length := ⟨ps.idxOf (v,N+f),hidx⟩
    let base := preparedSourceStore s (p.R+1) (d*baseWidth 3 p.t) ps v N f
    have hs := fun j (hj : j < N) remaining acc =>
      staged_native_row_relSourceSpec p P row base (ps.length-1) S (by omega) (by omega)
        (hwork 335 (by simp)) (hwork 336 (by simp)) hready hsourceClean
        (by simpa [base,preparedSourceStore,initializeFinish] using hmeta)
        (by simp [base,preparedSourceStore,row,LayoutSourcePlanLookup.unary])
        hsize hmetadata hQ hR hW hRW j remaining acc
    obtain ⟨rows,n,rf,hrows,hlen,hn,he⟩ := sourceRows_present_model
      p.t p.ht p.hd p.model p.modulus p.cache p.hz p.R width frame
      stagedPackedSource s v N f (stagedSourceBudget p S)
      (Subexp.UniversalRowSourceBound.sourceLengthBound S) ps (packedSourceValue p P row)
      hinit hv hN hf hplan hmem hlookup hclean hwork howner H E hs
      (fun i _ => packedSourceValue_degree p P row i) regs
    have hvalue : totalPackedSource p P (ps.idxOf (v,N+f))=packedSourceValue p P row := by
      funext col
      simp [totalPackedSource,hidx,row]
    have hrel : (fun j out => PolynomialExecutorProgram.meaning p.ops out=
        ownerSum ps j (packedSourceValue p P row))=
        (fun j out => PolynomialExecutorProgram.meaning p.ops out=
          sourceRowFamily ps N f v (totalPackedSource p P) j) := by
      funext j out
      simp only [sourceRowFamily,ite_eq_left hmem,hvalue]
    refine ⟨rows,n,rf,?_,hlen,?_,he⟩
    · change RowProperty DensePolynomialProgram.encode _ _ _ _ at hrows
      rw [←hrel]
      exact hrows
    · apply hn.trans
      dsimp only [nativeRowsBudget]
      gcongr <;> omega
  · obtain ⟨rows,n,rf,hrows,hlen,hn,he⟩ := sourceRows_absent_model
      p.t p.ht p.hd p.model p.modulus p.cache p.hz stagedPackedSource s (p.R+1) v N f ps
      hinit hv hN hf hplan hmem hlookup hclean regs
    have hrel : (fun (_ : ℕ) out => PolynomialExecutorProgram.meaning p.ops out=0)=
        (fun j out => PolynomialExecutorProgram.meaning p.ops out=
          sourceRowFamily ps N f v (totalPackedSource p P) j) := by
      funext j out
      simp [sourceRowFamily,hmem]
    refine ⟨rows,n,rf,?_,hlen,?_,he⟩
    · rw [←hrel]
      exact hrows
    · apply hn.trans
      dsimp only [nativeRowsBudget]
      gcongr <;> omega

end SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram

end OAI.Algorithms
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram.sourceRows_run_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram.sourceRows_run_oai
