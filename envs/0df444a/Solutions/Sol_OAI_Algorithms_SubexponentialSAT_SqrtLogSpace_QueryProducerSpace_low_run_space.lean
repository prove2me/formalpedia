-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryProducerSpace.low_run_space
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T11:15:14.56822+00:00
-- url     : https://prove2.me/submissions/d81cc253-f606-4566-a311-7b75635a0bda

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S188
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_PerturbationAssembly_LowInput_run_polynomial
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_StructuredSpace_local_stack_bound

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PerturbationEmitProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Native emission of the positive part of a shifted coefficient array.
The dimensions and the singleton support mask are runtime data. The constant
cell is consumed without emission; all later cells are framed, including zero
coefficients. No normalization or arithmetic oracle is used. -/


namespace SubexponentialSAT.SqrtLog.PerturbationEmitProgram
open SubexponentialSAT BitProgram StructuredCalls SubexpConvolutionControl
open PerturbationProgram _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.Squarefree

theorem emitted_typed {n d B : ℕ} (v : Fin n) (j : ℕ)
    (cs : List (Coefficient d B)) (acc : List (Index (Fin n) × Coefficient d B)) :
    emitted (encodeMask {v}) j (cs.map RingProgram.flat) (dictionaryBits acc) =
      dictionaryBits ((entries v j cs).reverse++acc) := by
  induction cs generalizing j acc with
  | nil => simp [emitted,entries]
  | cons c cs ih =>
      simp only [List.map_cons,emitted,record_typed]
      rw [show Encoding.frame (encodeIndex (⟨0,j,{v}⟩ : Index (Fin n))) ++
          Encoding.frame (RingProgram.flat c) ++ dictionaryBits acc =
          dictionaryBits ((⟨0,j,{v}⟩,c)::acc) by rw [dictionaryBits_cons]]
      rw [ih]
      simp [entries,List.reverse_cons,List.append_assoc]

end SubexponentialSAT.SqrtLog.PerturbationEmitProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PerturbationAssemblyStoredBytes
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Exact byte order of the physical row scan. No sparse normalization or
deletion of zero coefficient records is used by this bridge. -/
namespace SubexponentialSAT.SqrtLog.PerturbationAssembly
open SubexponentialSAT
open SubexponentialSAT.SubexpSymbolicCost
open DensePolynomialProgram _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.Squarefree PerturbationProgram

private theorem entries_coefficientRecords {B d n : ℕ} (v : Fin n)
    (j : ℕ) (cs : List (Coeff B d)) :
    PerturbationEmitProgram.entries v j cs = coefficientRecords v j cs := by
  induction cs generalizing j with
  | nil => rfl
  | cons c cs ih => simp only [PerturbationEmitProgram.entries,coefficientRecords,ih]

theorem coordinateResult_dictionary {B d n : ℕ}
    (ops : RingProgram (Coeff B d)) (J : ℕ) (theta : Coeff B d)
    (v : Fin n) (P : List (Coeff B d))
    (acc : List (Index (Fin n) × Coeff B d)) :
    coordinateResult ops J theta v P (dictionaryBits acc) =
      dictionaryBits ((coefficientRecords v 1
        (shiftedValue ops J theta P).val.tail).reverse ++ acc) := by
  unfold coordinateResult
  rw [←List.map_tail,PerturbationEmitProgram.emitted_typed,entries_coefficientRecords]

theorem rowsResult_dictionary {B d : ℕ} (ops : RingProgram (Coeff B d))
    (J n N : ℕ) (theta : Coeff B d) (j : ℕ)
    (rows : List (Fixed.Array B d N)) (acc : List (Index (Fin n) × Coeff B d)) :
    rowsResult (scanStep ops J n N theta) j rows (dictionaryBits acc) =
      dictionaryBits ((scanRecords ops J n N theta j rows).reverse ++ acc) := by
  induction rows generalizing j acc with
  | nil => simp [rowsResult,scanRecords]
  | cons p ps ih =>
      simp only [rowsResult]
      by_cases hj : j < n
      · rw [scanStep,dite_eq_left hj,coordinateResult_dictionary,ih]
        simp [scanRecords,List.reverse_append,hj,List.append_assoc]
      · rw [scanStep,dite_eq_right hj,ih]
        simp [scanRecords,hj]

end SubexponentialSAT.SqrtLog.PerturbationAssembly

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PerturbationAssemblyStoredLow
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The actual low-variable worker's byte output, including its internally
computed beta, is the unnormalized Stored incidence dictionary. -/
namespace SubexponentialSAT.SqrtLog.PerturbationAssembly
open SubexponentialSAT
open DensePolynomialProgram _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.Squarefree PerturbationProgram
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

theorem originKey_eq_encodeIndex (n : ℕ) :
    originKey n = encodeIndex (Index.origin : Index (Fin n)) := by
  simp [originKey,PerturbationEmitProgram.keyBits,PerturbationProgram.Key.bits,
    encodeIndex,Index.origin,encodeMask,Encoding.encodeNat]

theorem origin_dictionary {B d : ℕ} (n : ℕ) (beta : Coeff B d) :
    Encoding.frame (originKey n) ++ Encoding.frame (RingProgram.flat beta) =
      dictionaryBits [((Index.origin : Index (Fin n)),beta)] := by
  simp [dictionaryBits,originKey_eq_encodeIndex]

theorem lowOutput_dictionary (t : ℕ) {d : ℕ} (a : RingModel.Data d)
    (M : SubexpPreparedQuartic.Modulus 3 t) (cache : RingProgram.ScalarCache 3 t)
    (J N : ℕ) (theta : Coeff (baseWidth 3 t) d)
    (rows : List (Fixed.Array (baseWidth 3 t) d N × Bool)) :
    lowOutput t a M cache J N theta rows [] =
      dictionaryBits (outputWords (RingProgram.modelProgram t a M cache) J theta
        (PerturbationBetaProgram.runValue t a M cache theta (pairedRows rows))
        (fun v : Fin rows.length => rows[v].1.val)) := by
  have he : (rows.map Prod.fst).zipIdx 0 =
      List.ofFn (fun v : Fin rows.length => (rows[v].1,v.val)) := by
    apply List.ext_getElem
    · simp
    · intro i hi hj
      simp [List.getElem_zipIdx]
  have hr : scanRecords (RingProgram.modelProgram t a M cache) J rows.length N
      theta 0 (rows.map Prod.fst) =
      (List.ofFn fun v : Fin rows.length => coefficientRecords v 1
        (shiftedValue (RingProgram.modelProgram t a M cache) J theta rows[v].1.val).val.tail).flatten := by
    unfold scanRecords
    rw [he,List.flatMap_def,List.map_ofFn]
    congr 1
    apply congrArg List.ofFn
    funext v
    simp only [Function.comp_apply,dite_eq_left v.isLt]
  rw [lowOutput,List.append_nil,origin_dictionary,rowsResult_dictionary,hr]
  simp only [outputWords,rawWords,List.reverse_cons]

end SubexponentialSAT.SqrtLog.PerturbationAssembly

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_QueryIncidenceSpace
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryProducerSpace

open OAI BitProgram StructuredCalls
open OAI.Algorithms.SubexponentialSAT.SqrtLog OAI.Algorithms.SubexponentialSAT.SubexpLiftRing OAI.Algorithms.SubexponentialSAT.SubexpQuarticRing
open MomentsProgram TruncatedRingProgram
open scoped BigOperators


/-- The byte ABI of the native incidence emitter is the product dictionary ABI. -/
theorem dictionaryBits_productBytes {n B d : ℕ} (source : List (Product.Entry n B d)) :
    PerturbationProgram.dictionaryBits source = Product.bytes source := by
  induction source with
  | nil => rfl
  | cons a source ih =>
    simpa only [PerturbationProgram.dictionaryBits_cons, Product.bytes, Normalize.bytes,
      Squarefree.Program.encodeDictionary, List.map_cons, Squarefree.Program.rawEntries] using
      congrArg (fun bits => Encoding.frame (Squarefree.encodeIndex a.1) ++
        Encoding.frame (RingProgram.flat a.2) ++ bits) ih

theorem lowOutput_productBytes (t : ℕ) {d : ℕ} (model : RingModel.Data d)
    (M : SubexpPreparedQuartic.Modulus 3 t) (cache : RingProgram.ScalarCache 3 t)
    (J N : ℕ) (theta : DensePolynomialProgram.Coeff (baseWidth 3 t) d)
    (rows : List (DensePolynomialProgram.Fixed.Array (baseWidth 3 t) d N × Bool)) :
    PerturbationAssembly.lowOutput t model M cache J N theta rows [] =
      Product.bytes (emittedSource t model M cache J N theta rows) := by
  rw [PerturbationAssembly.lowOutput_dictionary, dictionaryBits_productBytes]
  rfl


/-- The fixed native emitter actually computes beta and all singleton records;
all source prefixes are charged before the immediate correction substitution. -/
theorem low_run_space_oai (t : ℕ) {d : ℕ} (model : RingModel.Data d)
    (M : SubexpPreparedQuartic.Modulus 3 t) (cache : RingProgram.ScalarCache 3 t)
    (J N : ℕ) (theta : DensePolynomialProgram.Coeff (baseWidth 3 t) d)
    (rows : List (DensePolynomialProgram.Fixed.Array (baseWidth 3 t) d N × Bool))
    (low : SubexpConvolutionControl.Store)
    (hinput : PerturbationAssembly.LowInput t model M cache J N theta rows low)
    (hout : low 217 = []) (regs : Fin 16 → Bool) :
    let source := emittedSource t model M cache J N theta rows
    let bound := PerturbationAssembly.lowWorkPolynomial rows.length N J t d
      ((low 192).length + (low 193).length + (low 243).length) + 1
    ∃ steps rr, steps ≤ bound ∧
      Trace lowProgram steps
        ((⟨regs, low⟩ : State 16 256).withPC (some lowProgram.entry))
        ((⟨rr, Function.update low 217 (Product.bytes source)⟩ : State 16 256).withPC none) ∧
      ∀ prefixSteps intermediate, prefixSteps ≤ steps →
        Trace lowProgram prefixSteps
          ((⟨regs, low⟩ : State 16 256).withPC (some lowProgram.entry)) intermediate →
        ∀ i, (intermediate.stacks i).length ≤ stackBits low + bound := by
  dsimp only
  obtain ⟨steps, rr, hb, he⟩ := hinput.run_polynomial regs
  rw [hout, lowOutput_productBytes] at he
  have ht := compiled_halt_trace he 205 217
  refine ⟨steps + 1, rr, by omega, ht, ?_⟩
  intro prefixSteps intermediate hp htrace i
  exact StructuredSpace.local_stack_bound lowProgram
    (steps := PerturbationAssembly.lowWorkPolynomial rows.length N J t d
      ((low 192).length + (low 193).length + (low 243).length) + 1)
    (by rfl) prefixSteps intermediate (by omega) htrace i

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryProducerSpace
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryProducerSpace.low_run_space_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryProducerSpace.low_run_space_oai
