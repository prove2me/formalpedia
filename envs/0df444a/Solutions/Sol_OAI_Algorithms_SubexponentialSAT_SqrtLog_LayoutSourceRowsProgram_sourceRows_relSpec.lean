-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram.sourceRows_relSpec
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T07:08:44.832267+00:00
-- url     : https://prove2.me/submissions/d5c5a76a-dba0-4188-ace6-bb7c775f95b9

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S144
import Definitions.Def_OAIQ081S151
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_LayoutSourceRowsProgram_sourceRowWith_run

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_DensePolynomialProgramAdd
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Native addition of dense polynomial arrays whose coefficients have an
arbitrary runtime extension degree. The fixed scanner visits base words;
there is no quartet assumption and no generated instruction table. -/

namespace SubexponentialSAT.SqrtLog.DensePolynomialProgram

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.DensePolynomialLoop
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

theorem encode_eq_flatten_words {B d : ℕ} (P : List (Coeff B d)) :
    encode P = flatten (words P) := by
  induction P with
  | nil => rfl
  | cons a P ih =>
      simp [encode, words, flatten, RingProgram.flat, List.map_ofFn, Function.comp_def,
        show (P.map RingProgram.flat).flatten = flatten (words P) from ih]

@[simp] theorem encode_length {B d : ℕ} (P : List (Coeff B d)) :
    (encode P).length = P.length * (d * B) := by
  rw [encode_eq_flatten_words, flatten_length, words_length, Nat.mul_assoc]

end SubexponentialSAT.SqrtLog.DensePolynomialProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_DensePolynomialProgramFixedBasic
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Exact-length dense arrays and their polynomial meanings, independent of
native service composition. -/
namespace SubexponentialSAT.SqrtLog.DensePolynomialProgram.Fixed
@[simp] theorem encode_length {B degree J : ℕ} (P : Array B degree J) :
    (encode P).length = J*(degree*B) := by simp [encode,P.2]

end SubexponentialSAT.SqrtLog.DensePolynomialProgram.Fixed

end OAI.Algorithms
end

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

/-- Exact list-order specification, without reindexing the original owners. -/
theorem fiberIndices_eq_filter (query index : ℕ) (ps : List (ℕ × ℕ)) :
    fiberIndices query index ps =
      (((ps.zipIdx index).filter fun x => decide (x.1.1=query)).map Prod.snd) := by
  induction ps generalizing index with
  | nil => rfl
  | cons p ps ih =>
      by_cases h : p.1=query <;> simp [fiberIndices,h,ih]

theorem fiberIndices_length_le (query index : ℕ) (ps : List (ℕ × ℕ)) :
    (fiberIndices query index ps).length ≤ ps.length := by
  rw [fiberIndices_eq_filter]
  simpa using List.length_filter_le (fun x : (ℕ × ℕ) × ℕ => decide (x.1.1=query)) (ps.zipIdx index)

theorem encodeIndices_length_le (query index : ℕ) (ps : List (ℕ × ℕ)) :
    (encodeIndices (fiberIndices query index ps)).length ≤ ps.length*(index+ps.length+1) := by
  induction ps generalizing index with
  | nil => simp [fiberIndices,encodeIndices]
  | cons p ps ih =>
      have hh := ih (index+1)
      by_cases h : p.1=query <;>
        simp [fiberIndices,h,encodeIndices,Encoding.encodeNat] at * <;> nlinarith

theorem stream_length (ps : List (ℕ × ℕ)) :
    (stream ps).length=8*mass ps+24*ps.length+1 := by
  induction ps with
  | nil => simp [stream,Encoding.encodeList,mass]
  | cons p ps ih =>
      change (true::(Encoding.frame (pairPayload p.1 p.2)++stream ps)).length=_
      simp only [List.length_cons,List.length_append,Encoding.length_frame,pairPayload_length,ih]
      simp only [mass,List.map_cons,List.sum_cons]
      unfold mass at ih
      omega

theorem scanCost_le (query index : ℕ) (ps : List (ℕ × ℕ)) :
    scanCost query index ps ≤
      1+71*mass ps+ps.length*(9*query+7*index+7*ps.length+210) := by
  induction ps generalizing index with
  | nil => simp [scanCost,mass]
  | cons p ps ih =>
      have hh := ih (index+1)
      simp only [scanCost,callbackCost,pairPayload_length]
      simp only [mass,List.map_cons,List.sum_cons,List.length_cons]
      unfold mass at hh
      nlinarith

/-- Polynomial in the actual encoded source length and unary query size.
No list expansion or unit-cost arithmetic appears in the execution theorem. -/
theorem budget_polynomial (query : ℕ) (ps : List (ℕ × ℕ)) :
    budget query ps ≤ 1000*((stream ps).length+query+1)^2 := by
  have hL := stream_length ps
  have hD : ps.length ≤ (stream ps).length := by omega
  have hM : mass ps ≤ (stream ps).length := by omega
  have hs := scanCost_le query 0 ps
  have he := encodeIndices_length_le query 0 ps
  have hm := Nat.mul_le_mul hD
    (show 9*query+10*ps.length+215 ≤ 9*query+10*(stream ps).length+215 by omega)
  unfold budget
  nlinarith

end SubexponentialSAT.SqrtLog.LayoutOwnerFiberProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutSourceRowsProgramContext
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Exact extraction of the native executor context from the source worker.
The four dispatcher ports are excluded from this context. -/
namespace SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram
open SubexponentialSAT BitProgram StructuredCalls
open SubexponentialSAT.SubexpRowPostfixInterpreter (ports physicalCfg contextStore)
open SubexponentialSAT.SubexpRowPostfixContext (operandStore)
attribute [local simp] Fin.coe_ofNat_eq_mod

/-- The executor context discards its source and saved controls. Thus a new
postfix source on333 does not change any arithmetic readiness premise. -/
theorem executionContext_evaluation (s : Store) :
    executionContext (evaluationInput s)=executionContext (Function.update s 21 []) := by
  funext i
  let p := executorPorts (ports (Fin.natAdd 4 i))
  have hp : p.val < 256 := (ports (Fin.natAdd 4 i)).isLt
  have h26 : p≠26 := by
    intro h
    have he : ports (Fin.natAdd 4 i)=26 := by
      apply Fin.ext
      have hh := congrArg (fun k : Fin 340 => k.val) h
      change (ports (Fin.natAdd 4 i)).val=26 at hh
      exact hh
    have hi : Fin.natAdd 4 i=(0 : Fin 256) := by
      simpa using congrArg ports.symm he
    have hh := congrArg Fin.val hi
    simp at hh
  have h333 : p≠333 := by intro h; rw [h] at hp; norm_num at hp
  have h335 : p≠335 := by intro h; rw [h] at hp; norm_num at hp
  have h336 : p≠336 := by intro h; rw [h] at hp; norm_num at hp
  change evaluationInput s p=Function.update s 21 [] p
  simp [evaluationInput,Function.update_apply,h26,h333,h335,h336]

theorem executionContext_evaluation_congr (s t : Store)
    (h : ∀ i : Fin 340, i.val < 256 → s i=t i) :
    executionContext (evaluationInput s)=executionContext (evaluationInput t) := by
  rw [executionContext_evaluation,executionContext_evaluation]
  funext i
  have hp : (executorPorts (ports (Fin.natAdd 4 i))).val < 256 :=
    (ports (Fin.natAdd 4 i)).isLt
  simp [executionContext,Function.update_apply,h _ hp]

theorem executionContext_evaluation_rowState (s : Store) (j : ℕ) (remaining acc : List Bool) :
    executionContext (evaluationInput (rowState s j remaining acc))=
      executionContext (evaluationInput s) := by
  apply executionContext_evaluation_congr
  intro i hi
  have h320 : i≠320 := by intro h; subst i; norm_num at hi
  have h331 : i≠331 := by intro h; subst i; norm_num at hi
  have h332 : i≠332 := by intro h; subst i; norm_num at hi
  simp [rowState,h320,h331,h332]

end SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutSourceRowsProgramRow
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! One source row: actual owner scan, native per-incidence source generation,
postfix summation, and native polynomial evaluation. -/
namespace SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram
open SubexponentialSAT BitProgram StructuredCalls
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

theorem sourceRowBudget_le_uniform (query N : ℕ) (hq : query ≤ N)
    (ps : List (ℕ × ℕ)) (I K L D d B a b : ℕ) :
    sourceRowBudget query ps I K L D d B a b ≤ uniformRowBudget N ps I K L D d B a b := by
  have hF := LayoutOwnerFiberProgram.fiberIndices_length_le query 0 ps
  have howner : LayoutOwnerFiberProgram.budget query ps ≤
      1000*((LayoutOwnerFiberProgram.stream ps).length+N+1)^2 :=
    (LayoutOwnerFiberProgram.budget_polynomial query ps).trans (by gcongr)
  dsimp only [sourceRowBudget,uniformRowBudget]
  gcongr

end SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutSourceRowsProgramRowsModel
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram
open SubexponentialSAT BitProgram StructuredCalls
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing
attribute [local simp] Fin.coe_ofNat_eq_mod

theorem sourceRows_relSpec_oai (t : ℕ) (ht : 0 < t) {d : ℕ} (hd : 0 < d)
    (a : RingModel.Data d) (M : SubexpPreparedQuartic.Modulus 3 t)
    (cache : RingProgram.ScalarCache 3 t) (hz : BinaryArithmetic.toNat cache.zero.val < 3^t)
    (D : ℕ) (width : List Bool) (frame : Fin 6 → List Bool)
    (source : Code) (base : Store) (I K L N : ℕ) (ps : List (ℕ × ℕ))
    (value : ℕ → ℕ → Polynomial (a.O t))
    (spec : ∀ j, j < N → ∀ remaining acc,
      RelSourceSpec source (rowState base j remaining acc)
        (fun e : Algorithm.Expr (List (PolynomialExecutorProgram.Coeff (baseWidth 3 t) d)) =>
          SubexpPostfixControl.serializeCode DensePolynomialProgram.encode e.compile)
        (TypedSourceRel DensePolynomialProgram.encode
          (PolynomialExecutorProgram.meaning (RingProgram.modelRing t ht hd a M cache)) (value j) L) I K L)
    (hs : base 337=LayoutOwnerFiberProgram.stream ps)
    (howner : ∀ i : Fin 11, 2 ≤ i.val → base (ownerStacks i)=[])
    (hwork : RowWorkClean base)
    (hI : ∀ j, j < N → ∀ i∈LayoutOwnerFiberProgram.fiberIndices j 0 ps, i ≤ I)
    (H : PolynomialExecutorProgram.Ready 3 t M cache (RingProgram.modelProgram t a M cache)
      (HornerProgram.modelTable t a M cache) D width frame
        (executionContext (evaluationInput base))) :
    RelRowSpec (sourceRowWith source) base DensePolynomialProgram.encode
      (fun j out => PolynomialExecutorProgram.meaning (RingProgram.modelRing t ht hd a M cache) out=
        Truncation.trunc D (ownerSum ps j (value j))) N
      (uniformRowBudget N ps I K L D d (baseWidth 3 t) (base 21).length (base 26).length)
      (D*(d*baseWidth 3 t)) := by
  intro j hj remaining acc regs
  let s := rowState base j remaining acc
  have howner' : ∀ i : Fin 11, 2 ≤ i.val → s (ownerStacks i)=[] := by
    intro i hi
    have hh := howner i hi
    fin_cases i <;> simp_all [s,rowState,ownerStacks]
  have H' : PolynomialExecutorProgram.Ready 3 t M cache (RingProgram.modelProgram t a M cache)
      (HornerProgram.modelTable t a M cache) D width frame
        (executionContext (evaluationInput s)) := by
    simpa only [s,executionContext_evaluation_rowState] using H
  obtain ⟨out,n,rf,hlen,hmeaning,hn,he⟩ := sourceRowWith_run t ht hd a M cache hz D width frame
    source s I K L (value j) (spec j hj remaining acc) j ps
    (by simp [s,rowState,LayoutOwnerFiberProgram.unary])
    (by simpa [s,rowState] using hs) howner'
    (by simpa [s,rowState] using hwork 305 (by simp))
    (by simpa [s,rowState] using hwork 287 (by simp))
    (by simpa [s,rowState] using hwork 333 (by simp)) (hI j hj)
    (by simpa [s,rowState] using hwork 27 (by simp))
    (by simpa [s,rowState] using hwork 28 (by simp))
    (by simpa [s,rowState] using hwork 29 (by simp))
    (by simpa [s,rowState] using hwork 335 (by simp))
    (by simpa [s,rowState] using hwork 336 (by simp)) H' regs
  refine ⟨out,n,rf,hmeaning,?_,?_,he⟩
  · simp [DensePolynomialProgram.encode_length,hlen]
  · have hb := sourceRowBudget_le_uniform j N (by omega) ps I K L D d (baseWidth 3 t)
      (base 21).length (base 26).length
    apply le_trans _ hb
    simpa [s,rowState] using hn

end SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram

end OAI.Algorithms
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram.sourceRows_relSpec_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram.sourceRows_relSpec_oai
