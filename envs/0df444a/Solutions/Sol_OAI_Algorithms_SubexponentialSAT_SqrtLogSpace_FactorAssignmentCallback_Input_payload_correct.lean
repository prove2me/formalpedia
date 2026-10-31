-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentCallback.Input.payload_correct
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T10:10:30.331902+00:00
-- url     : https://prove2.me/submissions/14f14e9b-e44a-49aa-8429-cd85b66abb8f

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S181
import Definitions.Def_OAIQ081S183
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_FactorAssignmentCallback_Input_staged_factorJet
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_FactorTableDenotation_low_payload_realizes
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_FactorTableNative_Ready_staged_common

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_RingProgramSerialization
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.RingProgram

open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing SubexponentialSAT.BinaryArithmetic

theorem flat_eq_encode {d B : ℕ} (hB : 0 < B) (x : Code (Word B) d) :
    flat x = SubexponentialSAT.StackEncoding.encodeDataStack (wordBlockCode B hB) (List.ofFn x) := by
  have aux (xs : List (Word B)) :
      (xs.map Subtype.val).flatten =
        SubexponentialSAT.StackEncoding.encodeDataStack (wordBlockCode B hB) xs := by
    induction xs with
    | nil => rfl
    | cons x xs ih => simpa only [List.map_cons, List.flatten_cons,
        SubexponentialSAT.StackEncoding.encodeDataStack_cons, wordBlockCode] using congrArg (x.val ++ ·) ih
  change (List.ofFn (Subtype.val ∘ x)).flatten = _
  simpa only [List.map_ofFn] using aux (List.ofFn x)

theorem flat_injective {d B : ℕ} (hB : 0 < B) :
    Function.Injective (flat : Code (Word B) d → List Bool) := by
  intro x y h
  rw [flat_eq_encode hB, flat_eq_encode hB] at h
  exact List.ofFn_injective (SubexponentialSAT.StackEncoding.encodeDataStack_injective _ h)

end SubexponentialSAT.SqrtLog.RingProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_SquarefreeIndexEncoding
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.decidableMemJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.decidableMemSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A self-delimiting encoding of sparse keys: two unary numeric fields,
followed by exactly n support bits. The encoding works without precision
assumptions; the precision assumptions only bound its length. -/

namespace SubexponentialSAT.SqrtLog.Squarefree

theorem encodeMask_injective {n : ℕ} :
    Function.Injective (encodeMask (n := n)) := by
  intro a b h
  have hf : (fun i : Fin n => decide (i ∈ a)) =
      (fun i : Fin n => decide (i ∈ b)) := List.ofFn_injective h
  ext i
  have hi := congrFun hf i
  by_cases ha : i ∈ a <;> by_cases hb : i ∈ b <;> simp_all

theorem encodeIndex_injective {n : ℕ} :
    Function.Injective (encodeIndex (n := n)) := by
  intro a b h
  have hfirst : a.u = b.u ∧
      Encoding.encodeNat a.z ++ encodeMask a.vars =
        Encoding.encodeNat b.z ++ encodeMask b.vars := by
    simpa [encodeIndex, List.append_assoc] using congrArg Encoding.readNat h
  have hsecond : a.z = b.z ∧ encodeMask a.vars = encodeMask b.vars := by
    simpa using congrArg Encoding.readNat hfirst.2
  have hs := encodeMask_injective hsecond.2
  cases a
  cases b
  cases hfirst.1
  cases hsecond.1
  cases hs
  rfl

end SubexponentialSAT.SqrtLog.Squarefree

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HashInputProgramLoopFinal
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Public raw-input ABI and the uniform paid execution theorem. All control
tables are fixed independently of source size, raw tuple length and ring width.
Repeated source references and zero coefficients remain separate records. -/
namespace SubexponentialSAT.SqrtLog.HashInputProgram.Loop
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

theorem original_payload_length_le (clauses : List (List Bool)) (p : List Bool)
    (hp : p∈clauses) : p.length ≤ (Encoding.encodeList id clauses).length := by
  induction clauses with
  | nil => simp at hp
  | cons q qs ih =>
      have hq := Encoding.length_frame q
      simp only [Encoding.encodeList,id_eq,Encoding.length_frame,List.length_cons,List.length_append] at *
      rcases List.mem_cons.mp hp with rfl | hp
      · omega
      · have hh := ih hp
        omega

end SubexponentialSAT.SqrtLog.HashInputProgram.Loop

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramFactorDispatch
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The factor dispatcher in the native leaf's actual bank.  The parsed ID
is retained for incidence preparation.  The mark flag is read from a tape,
not inserted as a program parameter. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.FactorDispatch

open SubexponentialSAT BitProgram StructuredCalls SubexpScanPrimitives

theorem stackMap_injective : Function.Injective stackMap := by decide

end SubexponentialSAT.SqrtLog.LeafProgram.FactorDispatch

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_GlobalBasisMetadata
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Physical packing metadata lookup

The raw packing table and query remain on stacks 0 and 1. A successful lookup
returns either a block/type pair on 2/3, or a leftover rank on 4. Register 4
distinguishes those cases; all other registers and stacks 5 through 11 are
cleared. Keys, indices, and type encodings are runtime words.
-/

namespace SubexponentialSAT.Subexp.GlobalBasisMetadata

open BitProgram StructuredCalls SubexpScanPrimitives


theorem payload_length_le (records : List (List Bool × List Bool)) (query payload : List Bool)
    (h : records.lookup query = some payload) :
    payload.length ≤ (SelectorProgram.rawRecords records).length := by
  obtain ⟨before, after, rfl, _⟩ := List.lookup_eq_some_iff.mp h
  simp [SelectorProgram.rawRecords, List.flatMap_append]
  omega

end SubexponentialSAT.Subexp.GlobalBasisMetadata

end OAI.Algorithms
end

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
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutOwnerFiberProgramBounds
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LayoutOwnerFiberProgram
open SubexponentialSAT BitProgram StructuredCalls

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

end SubexponentialSAT.SqrtLog.LayoutOwnerFiberProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramIncidence
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The selected-factor incidence service with a concrete source generator.
All ring/layout inputs are copied from persistent masters, and the complete
private worker is reclaimed after exporting the actual lookup table. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.Incidence
open SubexponentialSAT BitProgram StructuredCalls SubexpSetupStorage

theorem mem_workerPorts (i : Fin 768) : i ∈ workerPorts ↔ 340 ≤ i.val ∧ i.val < 680 := by
  simp only [workerPorts,List.mem_map,List.mem_finRange,true_and]
  constructor
  · rintro ⟨j,hj⟩
    have hv := congrArg Fin.val hj
    change 340+j.val=i.val at hv
    omega
  · intro hi
    refine ⟨⟨i.val-340,by omega⟩,?_⟩
    apply Fin.ext
    change 340+(i.val-340)=i.val
    omega

end SubexponentialSAT.SqrtLog.LeafProgram.Incidence

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_HeadEvaluation
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.decidableMemJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.decidableMemSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Restricted sums over the actual Boolean heads. All products are formed in
one coefficient ring before any additive coefficient readout. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadEvaluation
open OAI.Algorithms.SubexponentialSAT.SqrtLog
open scoped BigOperators

variable {V R : Type*} [DecidableEq V]

variable [CommSemiring R]

theorem subset_weight (U E : Finset V) :
    Squarefree.weight (fun v => if v ∈ U then (1:R) else 0) E =
      if E ⊆ U then 1 else 0 := by
  simp only [Squarefree.weight, Finset.prod_boole, Finset.subset_iff]

theorem specialize_atom (U : Finset V) (a : Squarefree.Index V) (c : R) :
    Moments.jetScalar (V := V) (Moments.jetEval (fun v => if v ∈ U then (1:R) else 0)
      (by intro v; split <;> simp) (Squarefree.Sparse.atom a c)) =
      if a.vars ⊆ U then Squarefree.Sparse.atom ⟨a.u,a.z,∅⟩ c else 0 := by
  simp only [Moments.jetScalar,Moments.jetEval,Polynomial.coe_mapRingHom,
    Squarefree.Sparse.atom,Polynomial.map_monomial,Squarefree.eval_monomial]
  rw [subset_weight]
  split <;> simp [Squarefree.scalar,Squarefree.monomial,show (1 : Squarefree.Support V) = ⟨∅⟩ from rfl]

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadEvaluation
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_TruncatedRingProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Native arithmetic after immediate Boolean specialization

The existing finite sparse-product program is used with empty formal support.
Its keys still carry the ambient input coordinate type; this does not compress
the declared variables. There are at most `u * J` retained entries, including
zero cutoffs. Polynomial local time therefore bounds all its source prefixes,
including the table, inputs, output, normalization copies and arithmetic scratch.
-/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.TruncatedRingProgram

open scoped BigOperators
open OAI OAI.Algorithms.SubexponentialSAT.SqrtLog OAI.Algorithms.SubexponentialSAT.SubexpLiftRing OAI.Algorithms.SubexponentialSAT.SubexpQuarticRing
open MomentsProgram BitProgram

/- The two fields coincide with LeafProgram.NativeSemantics.Good. The
arithmetic layer states them transparently to avoid importing the factor
interpreter. Conversion in either direction supplies `valid` and `nodup`.
The proof bodies below are the original finite-program validity arguments. -/
section NativeValidity

namespace Good

variable {n B d u J : ℕ} {vars : Finset (Fin n)}

 theorem nil : Good (B := B) (d := d) vars u J [] :=
  ⟨by simp, by simp [Squarefree.Sparse.keys]⟩

end Good

/-- The native constant keeps its origin record exactly at positive cutoffs. -/
theorem constant_good {n B d : ℕ} (u J : ℕ)
    (c : RingProgram.Code (Word B) d) :
    Good (n := n) ∅ u J (Squarefree.Sparse.constant u J c) := by
  by_cases h : 0 < u ∧ 0 < J
  · constructor
    · intro a ha
      simp only [Squarefree.Sparse.constant, ite_eq_left h, List.mem_singleton] at ha
      subst a
      simp [Product.ValidKey, Squarefree.Index.Kept, Squarefree.Index.Valid,
        Squarefree.Index.origin, h.1, h.2]
    · simp [Squarefree.Sparse.constant, h, Squarefree.Sparse.keys]
  · simpa only [Squarefree.Sparse.constant, ite_eq_right h] using
      (Good.nil (n := n) (B := B) (d := d) (vars := ∅) (u := u) (J := J))


end NativeValidity

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.TruncatedRingProgram
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_FactorTableProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! The actual selected-factor table runs over ambient variable IDs. Each low
payload is specialized immediately before its framed table entry is retained.
The source scratch embedding excludes persistent layout masters. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableProgram
open OAI.Algorithms.SubexponentialSAT.SqrtLog
open OAI BitProgram StructuredCalls SubexpConvolutionControl SubexpScanPrimitives
open SubexpPolynomialConstructor PerturbationAssembly OAI.Algorithms.SubexponentialSAT.SubexpLiftRing

attribute [local simp] Fin.coe_ofNat_eq_mod

private theorem decodeBasePort_low (i : Fin 896) (hi : i.val < 768) :
    decodeBasePort i = i.val := by
  have h885 : i ≠ 885 := by intro h; subst i; norm_num [Fin.coe_ofNat_eq_mod] at hi
  have h886 : i ≠ 886 := by intro h; subst i; norm_num [Fin.coe_ofNat_eq_mod] at hi
  have h887 : i ≠ 887 := by intro h; subst i; norm_num [Fin.coe_ofNat_eq_mod] at hi
  have h888 : i ≠ 888 := by intro h; subst i; norm_num [Fin.coe_ofNat_eq_mod] at hi
  have h889 : i ≠ 889 := by intro h; subst i; norm_num [Fin.coe_ofNat_eq_mod] at hi
  have h890 : i ≠ 890 := by intro h; subst i; norm_num [Fin.coe_ofNat_eq_mod] at hi
  have h891 : i ≠ 891 := by intro h; subst i; norm_num [Fin.coe_ofNat_eq_mod] at hi
  have h892 : i ≠ 892 := by intro h; subst i; norm_num [Fin.coe_ofNat_eq_mod] at hi
  simp only [decodeBasePort, ite_eq_right h885, ite_eq_right h886, ite_eq_right h887,
    ite_eq_right h888, ite_eq_right h889, ite_eq_right h890, ite_eq_right h891,
    ite_eq_right h892]

private theorem decodeBasePort_basePort (i : Fin 768) : decodeBasePort (basePort i) = i.val := by
  unfold basePort
  split_ifs with h1 h2 h3 h4 h5 h6 h7 h8
  · subst i; rfl
  · subst i; rfl
  · subst i; rfl
  · subst i; rfl
  · subst i; rfl
  · subst i; rfl
  · subst i; rfl
  · subst i; rfl
  · exact decodeBasePort_low _ i.isLt

theorem basePort_injective : Function.Injective basePort := by
  intro i j hij
  apply Fin.ext
  have hv := congrArg decodeBasePort hij
  simpa only [decodeBasePort_basePort] using hv

theorem basePort_protected (i : Fin 768) :
    basePort i ≠ 640 ∧ basePort i ≠ 641 ∧ basePort i ≠ 642 ∧ basePort i ≠ 647 ∧
      basePort i ≠ 650 ∧ basePort i ≠ 651 ∧ basePort i ≠ 670 ∧ basePort i ≠ 671 := by
  simp only [basePort]
  split_ifs <;> simp_all [Fin.ext_iff, Fin.coe_ofNat_eq_mod]

theorem basePort_high (i : Fin 768) :
    (basePort i).val < 768 ∨ (885 ≤ (basePort i).val ∧ (basePort i).val ≤ 892) := by
  simp only [basePort]
  split_ifs <;> simp_all only [Fin.val_castAdd, Fin.coe_ofNat_eq_mod] <;> omega

theorem basePort_outside (i : Fin 896)
    (hi : i ∈ protectedPorts ∨ (768 ≤ i.val ∧ (i.val < 885 ∨ 892 < i.val))) :
    ¬ ∃ j, basePort j = i := by
  rintro ⟨j, hj⟩
  rcases hi with hi | hi
  · simp only [protectedPorts, List.mem_cons, List.mem_nil_iff, or_false] at hi
    have hp := basePort_protected j
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hp.1 hj
    · exact hp.2.1 hj
    · exact hp.2.2.1 hj
    · exact hp.2.2.2.1 hj
    · exact hp.2.2.2.2.1 hj
    · exact hp.2.2.2.2.2.1 hj
    · exact hp.2.2.2.2.2.2.1 hj
    · exact hp.2.2.2.2.2.2.2 hj
  · have hm := basePort_high j
    rw [hj] at hm
    omega

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableProgram
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramFactorDispatchFrame
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Exact byte-store frame for the paid factor dispatcher. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.FactorDispatch
open SubexponentialSAT BitProgram StructuredCalls SubexpScanPrimitives

theorem finished_stacks (a : Data) (rf : Fin 8 → Bool)
    (rows clauses : List (List Bool)) (marked : Bool) (mark factor : ℕ)
    (hrows : a.stacks 701 = Encoding.encodeList id rows)
    (hclauses : a.stacks 700 = Encoding.encodeList id clauses)
    (hcount : a.stacks 704 = List.replicate rows.length true)
    (hmark : a.stacks 705 = Encoding.encodeNat mark)
    (hwork : ∀ i ∈ scratch, a.stacks i = []) :
    (finished a rf rows clauses marked mark factor).stacks =
      Function.update a.stacks 154
        (LeafFactorDispatchProgram.selectedPayload rows clauses marked mark factor) := by
  funext i
  by_cases hin : ∃ j, stackMap j = i
  · obtain ⟨j,rfl⟩ := hin
    rw [show (finished a rf rows clauses marked mark factor).stacks (stackMap j) =
        LeafFactorDispatchProgram.outputStacks rows clauses marked mark factor j from
      embedState_stack register stackMap (staged a) _ stackMap_injective j]
    fin_cases j <;>
      simp_all [stackMap,LeafFactorDispatchProgram.outputStacks,
        LeafFactorDispatchProgram.baseStacks,LeafFactorDispatchProgram.unary,scratch]
  · have h152 : i ≠ 152 := by intro h; subst i; exact hin ⟨2,rfl⟩
    have h154 : i ≠ 154 := by intro h; subst i; exact hin ⟨15,rfl⟩
    rw [show (finished a rf rows clauses marked mark factor).stacks i = (staged a).stacks i from
      embedState_stack_frame register stackMap (staged a) _ i hin]
    simp [staged,copied,afterCopy,StackRoutines.copyStacks,h152,h154]

end SubexponentialSAT.SqrtLog.LeafProgram.FactorDispatch

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_FactorAssignmentProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! The accepted-assignment factor product uses the original finite-ring
indicator and clause programs after the concrete specialized table producer.
Every cache is rebuilt from persistent source words by paid native copies;
neutral factor IDs leave the running multiplicative identity unchanged. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentProgram

open OAI BitProgram StructuredCalls SubexpSetupStorage
open SqrtLog SqrtLog.LeafProgram
noncomputable section

theorem callbackInitial_low (a : Data) (i : Fin 768) :
    (callbackInitial a).stacks (lowStack i) =
      if i ∈ callbackScratch then [] else a.stacks (lowStack i) := by
  exact (embedState_stack localRegister lowStack a
    (clearManyState callbackScratch (projectState localRegister lowStack a))
    (Fin.castAdd_injective _ _) i).trans
    (clearMany_stacks callbackScratch (projectState localRegister lowStack a) i)

theorem callbackInitial_frame (a : Data) (i : Fin 896)
    (hi : i ∉ callbackScratch.map lowStack) :
    (callbackInitial a).stacks i = a.stacks i := by
  by_cases hlt : i.val < 768
  · let j : Fin 768 := ⟨i.val, hlt⟩
    have hj : lowStack j = i := Fin.ext rfl
    have hn : j ∉ callbackScratch := by
      intro hm
      exact hi (List.mem_map.mpr ⟨j, hm, hj⟩)
    rw [← hj, callbackInitial_low, ite_eq_right hn]
  · apply embedState_stack_frame
    rintro ⟨j, hj⟩
    have hv := congrArg Fin.val hj
    change j.val = i.val at hv
    omega

end
end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentProgram
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

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryProducerSpace
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_FactorTableSpace
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Space for one actual ambient-coordinate table construction. Its unary
traversal has only n iterations, so its polynomial local time bounds every
source prefix. No outer signature or finite-difference iteration count occurs
in this estimate. The concrete literal and staging traces are instantiated by
the factor-table producer, rather than supplied to a final counting endpoint. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableSpace

open SqrtLog

open BitProgram StructuredCalls FactorTableProgram

theorem initialized_frame (a : OuterData) (i : Fin 896) (hi : i ∉ writtenPorts) :
    (initialized a).stacks i = a.stacks i := by
  rw [initialized, SubexpSetupStorage.clearMany_stacks, ite_eq_right]
  intro he
  apply hi
  rcases List.mem_append.mp he with he | he
  · obtain ⟨j, hj, hji⟩ := List.mem_map.mp he
    exact List.mem_append_left _ (List.mem_map.mpr ⟨j, (List.mem_filter.mp hj).1, hji⟩)
  · exact List.mem_append_right _ he

private theorem original_staged_worker_frame (a : LeafProgram.Incidence.Data) (i : Fin 768)
    (hi : i ∉ LeafProgram.Incidence.workerPorts) :
    (LeafProgram.Incidence.staged a).stacks i = a.stacks i := by
  have h550 : i ≠ 550 := by
    intro he
    subst i
    exact hi ((LeafProgram.Incidence.mem_workerPorts 550).mpr (by decide))
  change Function.update (SubexpSetupStorage.copyManyState LeafProgram.Incidence.pairs a).stacks
    550 _ i = a.stacks i
  rw [Function.update_of_ne h550]
  apply SubexpSetupStorage.copyMany_frame
  intro p hp he
  apply hi
  rw [he]
  apply (LeafProgram.Incidence.mem_workerPorts p.2).mpr
  simp only [LeafProgram.Incidence.pairs, List.mem_cons, List.mem_nil_iff, or_false] at hp
  rcases hp with h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h <;> subst p <;> decide

/-- All caller masters outside the finite write set survive actual staging. -/
theorem staged_frame (a : OuterData) (i : Fin 896) (hi : i ∉ writtenPorts) :
    (staged a).stacks i = a.stacks i := by
  by_cases himage : ∃ j, basePort j = i
  · obtain ⟨j, rfl⟩ := himage
    have hj : j ∉ LeafProgram.Incidence.workerPorts := by
      intro hj
      exact hi (List.mem_append_left _ (List.mem_map.mpr ⟨j, hj, rfl⟩))
    rw [staged, embedState_stack _ _ _ _ basePort_injective,
      original_staged_worker_frame _ j hj]
    simpa only [projectState, Function.comp_apply] using initialized_frame a (basePort j) hi
  · change (embedState id basePort (initialized a) _).stacks i = a.stacks i
    rw [embedState_stack_frame _ _ _ _ i himage]
    exact initialized_frame a i hi

/-- The protected caller regions include every low node port except the
export62, all eight layout masters, and high ports outside the private bank. -/
theorem caller_port_not_written (i : Fin 896)
    (hi : (i.val < 340 ∧ i ≠ 62) ∨ i ∈ protectedPorts ∨
      (768 ≤ i.val ∧ i ≠ 881 ∧ i ≠ 882 ∧ (i.val < 885 ∨ 892 < i.val))) :
    i ∉ writtenPorts := by
  intro hm
  rcases List.mem_append.mp hm with hm | hm
  · obtain ⟨j, hj, hji⟩ := List.mem_map.mp hm
    rcases hi with hi | hi | hi
    · have hw := (LeafProgram.Incidence.mem_workerPorts j).mp hj
      have hb : 340 ≤ (basePort j).val := by
        simp only [basePort]
        split_ifs <;> simp_all only [Fin.coe_ofNat_eq_mod, Fin.val_castAdd] <;> omega
      have hv := congrArg Fin.val hji
      omega
    · exact basePort_outside i (Or.inl hi) ⟨j, hji⟩
    · exact basePort_outside i (Or.inr ⟨hi.1, hi.2.2.2⟩) ⟨j, hji⟩
  · simp only [List.mem_cons, List.mem_nil_iff, or_false] at hm
    rcases hm with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
      norm_num [protectedPorts, Fin.ext_iff, Fin.coe_ofNat_eq_mod] at hi

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableSpace
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_FactorTableNative
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.Packing.nonemptyUniversal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Physical source preparation for the specialized factor table. The old
master-word argument is generalized to the actually selected unary factor,
then transported through the fixed protected-port embedding. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableNative
open OAI BitProgram StructuredCalls SubexpLiftRing SubexpQuarticRing
open OAI.Algorithms.SubexponentialSAT.SqrtLog OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram
open PerturbationAssembly LayoutProgram SubexpSetupStorage DensePolynomialProgram
open OAI.Algorithms.SubexponentialSAT.Subexp OAI.Algorithms.SubexponentialSAT.Subexp.ConstructivePacking OAI.Algorithms.SubexponentialSAT.MulticolorTypes
attribute [local simp] Fin.coe_ofNat_eq_mod

variable {r Q d n J S f : ℕ} {p : SourceBank.Parameters r Q d}
    {ps : List (ℕ × ℕ)} {P : PackingData (Fin ps.length) (UniversalType r Q 1)}
    {a : SourceReady.Data} {theta : DensePolynomialProgram.Coeff (baseWidth 3 p.t) d}

/-- Actual retained words discharge the source's per-entry size requirements.
The metadata bound follows from physical lookup serialization, and the
incidence count follows from the actual addressed plan stream. -/
theorem Ready.of_masters {r Q d u J n f B S : ℕ}
    {p : SourceBank.Parameters r Q d} {ps : List (ℕ × ℕ)}
    {P : PackingData (Fin ps.length) (UniversalType r Q 1)}
    {theta : Coeff (baseWidth 3 p.t) d} {a : FactorTableProgram.OuterData}
    (hu : 0 < u) (hJ : 0 < J)
    (hscalar : ScalarMasters p.t p.model p.modulus p.cache J p.R theta
      (projectState id FactorTableProgram.basePort a) n)
    (hmasters : SourceMasters p ps P (projectState id FactorTableProgram.basePort a))
    (hselected : a.stacks 556 = List.replicate f true)
    (hmask : (a.stacks 857).length = n)
    (hincoming : ∀ i, (a.stacks i).length ≤ B)
    (hsize : 1029*B+99+n+n*FactorTableProgram.literalRecordBound n
      (specializedPayloadBound n u J (baseWidth 3 p.t) d)+1 ≤ S)
    (hRQ : p.R+1 ≤ Q) : Ready p ps P u J n f B S theta a := by
  have hBS : B ≤ S := by omega
  have hcap (i : Fin 768) :
      ((projectState id FactorTableProgram.basePort a).stacks i).length ≤ B :=
    hincoming (FactorTableProgram.basePort i)
  have hrow := hcap 716
  rw [hmasters.rowWidth,p.hrowWidth,p.hringWidth] at hrow
  have hnodes := hcap 131
  rw [hmasters.nodes,List.length_replicate] at hnodes
  have hmetadata := hcap 135
  rw [hmasters.metadata] at hmetadata
  have hplans := hcap 136
  rw [hmasters.plans] at hplans
  have hincidence : ps.length ≤ B := by
    have hlength := LayoutOwnerFiberProgram.stream_length ps
    omega
  have hn := hincoming 857
  rw [hmask] at hn
  have hf := hincoming 556
  rw [hselected,List.length_replicate] at hf
  refine ⟨hu,hJ,hscalar,hmasters,hselected,hmask,hincoming,hsize,
    ((Nat.mul_le_mul_right _ hRQ).trans hrow).trans hBS,
    (hRQ.trans hnodes).trans hBS,?_,hincidence.trans hBS,hn.trans hBS,
    hf.trans hBS,hplans.trans hBS⟩
  intro x
  have hinj : Function.Injective (fun v : Fin ps.length => List.replicate v.val true) := by
    intro v w he
    apply Fin.ext
    simpa only [List.length_replicate] using congrArg List.length he
  have hl := PackingMetadata.lookup_eq P (fun v => List.replicate v.val true)
    CollisionProgram.encodeType hinj x
  have hp := ((GlobalBasisMetadata.payload_length_le _ _ _ hl).trans hmetadata).trans hBS
  have hb (m : GlobalBasisMetadata.Metadata) :
      m.block.length ≤ m.encode.length ∧ m.typeCode.length ≤ m.encode.length ∧
        m.rank.length ≤ m.encode.length := by
    cases m <;> simp [GlobalBasisMetadata.Metadata.block,GlobalBasisMetadata.Metadata.typeCode,
      GlobalBasisMetadata.Metadata.rank,GlobalBasisMetadata.Metadata.encode,Encoding.length_frame] <;> omega
  exact ⟨(hb _).1.trans hp,(hb _).2.1.trans hp,(hb _).2.2.trans hp⟩

theorem staged_mask (a : FactorTableProgram.OuterData) :
    (FactorTableProgram.staged a).stacks 857 = a.stacks 857 :=
  FactorTableSpace.staged_frame a 857
    (FactorTableSpace.caller_port_not_written 857 (Or.inr (Or.inr (by decide))))

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableNative
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_FactorAssignmentBranches
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Actual ordinary and marked factor branches. The physical factor ID is
converted to the unary source counter, then the specialized table is produced
before the original finite-ring arithmetic is run. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentBranches

open OAI BitProgram StructuredCalls SubexpLiftRing SubexpQuarticRing
open SqrtLog SqrtLog.LeafProgram HashCircuitProgram HashCircuitProgram.Native
open IdempotentApplyProgram.Steps MomentsProgram NativeSemantics
open FactorAssignmentProgram
open Subexp.ConstructivePacking MulticolorTypes LayoutProgram DensePolynomialProgram

theorem identified_stacks (a : FactorAssignmentProgram.Data) (factor : ℕ) :
    (identified a factor).stacks = Function.update a.stacks 556 (List.replicate factor true) := by
  funext i
  by_cases hi : i.val < 768
  · let j : Fin 768 := ⟨i.val, hi⟩
    have hj : lowStack j = i := Fin.ext rfl
    rw [← hj, identified, embedState_stack id lowStack a _ (Fin.castAdd_injective _ _) j]
    by_cases h556 : j = 556
    · rw [h556]
      rfl
    · have hne : lowStack j ≠ (556 : Fin 896) := by
        intro he
        apply h556
        apply Fin.ext
        have hv := congrArg (fun k : Fin 896 => k.val) he
        exact hv
      simp [FactorID.output, Function.update_of_ne h556,
        Function.update_of_ne hne, projectState]
  · have h556 : i ≠ 556 := by
      intro he
      have hv := congrArg (fun k : Fin 896 => k.val) he
      change i.val = 556 at hv
      omega
    rw [identified, embedState_stack_frame _ _ _ _ i, Function.update_of_ne h556]
    rintro ⟨j, hj⟩
    have hv := congrArg Fin.val hj
    change j.val = i.val at hv
    omega


end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentBranches
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_FactorAssignmentCallback
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! The actual specialized callback dispatches one stored original factor ID.
The general dispatch theorem fixes its physical payload, flags and exact frame;
hash and marked branch correctness is supplied by their concrete native proofs. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentCallback

open OAI BitProgram StructuredCalls
open SqrtLog SqrtLog.LeafProgram MomentsProgram FactorAssignmentProgram

noncomputable section
attribute [local simp] Fin.coe_ofNat_eq_mod

/-- The paid clear preserves an already established callback boundary. -/
theorem callbackInitial_stacks (a : FactorAssignmentProgram.Data)
    (hclean : ∀ i ∈ callbackScratch, a.stacks (lowStack i) = []) :
    (callbackInitial a).stacks = a.stacks := by
  funext i
  by_cases hi : i ∈ callbackScratch.map lowStack
  · obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hi
    rw [callbackInitial_low, ite_eq_left hj, hclean j hj]
  · exact callbackInitial_frame a i hi

private theorem dispatchInput_frame (a : FactorAssignmentProgram.Data) (i : Fin 768)
    (hi : i ∉ callbackScratch) :
    (dispatchInput a).stacks i = a.stacks (lowStack i) :=
  (callbackInitial_low a i).trans (ite_eq_right hi)

private theorem dispatchInput_work (a : FactorAssignmentProgram.Data) :
    ∀ i ∈ FactorDispatch.scratch, (dispatchInput a).stacks i = [] := by
  intro i hi
  have hmem : i ∈ callbackScratch := by
    simp only [callbackScratch, List.mem_append]
    exact Or.inl (Or.inl (Or.inr hi))
  exact (callbackInitial_low a i).trans (ite_eq_left hmem)

/-- All caller stacks are restored except the actual selected payload154.
This frame applies to hash, marked and neutral IDs, without an early exit. -/
theorem dispatched_stacks (a : FactorAssignmentProgram.Data) (rf : Fin 8 → Bool)
    (rows clauses : List (List Bool)) (marked : Bool) (mark factor : ℕ)
    (hrows : a.stacks 701 = Encoding.encodeList id rows)
    (hclauses : a.stacks 700 = Encoding.encodeList id clauses)
    (hcount : a.stacks 704 = List.replicate rows.length true)
    (hmark : a.stacks 705 = Encoding.encodeNat mark) :
    (dispatched a rf rows clauses marked mark factor).stacks =
      Function.update (callbackInitial a).stacks 154
        (LeafFactorDispatchProgram.selectedPayload rows clauses marked mark factor) := by
  have hr : (dispatchInput a).stacks 701 = Encoding.encodeList id rows :=
    (dispatchInput_frame a 701 (by decide)).trans hrows
  have hc : (dispatchInput a).stacks 700 = Encoding.encodeList id clauses :=
    (dispatchInput_frame a 700 (by decide)).trans hclauses
  have hn : (dispatchInput a).stacks 704 = List.replicate rows.length true :=
    (dispatchInput_frame a 704 (by decide)).trans hcount
  have hm : (dispatchInput a).stacks 705 = Encoding.encodeNat mark :=
    (dispatchInput_frame a 705 (by decide)).trans hmark
  have hlow := FactorDispatch.finished_stacks (dispatchInput a) rf rows clauses
    marked mark factor hr hc hn hm (dispatchInput_work a)
  funext i
  by_cases hi : i.val < 768
  · let j : Fin 768 := ⟨i.val, hi⟩
    have hj : lowStack j = i := Fin.ext rfl
    rw [← hj]
    change (embedState id lowStack (callbackInitial a)
      (FactorDispatch.finished (dispatchInput a) rf rows clauses marked mark factor)).stacks
      (lowStack j) = _
    rw [embedState_stack id lowStack _ _ (Fin.castAdd_injective _ _) j, hlow]
    by_cases h154 : j = 154
    · rw [h154]
      simp [lowStack]
    · have hwide : lowStack j ≠ 154 := by
        intro he
        apply h154
        exact Fin.ext (congrArg (fun k : Fin 896 => k.val) he)
      simp only [Function.update_of_ne h154, Function.update_of_ne hwide]
      rfl
  · have h154 : i ≠ 154 := by intro he; subst i; norm_num at hi
    rw [Function.update_of_ne h154]
    apply embedState_stack_frame
    rintro ⟨j, hj⟩
    have hv := congrArg Fin.val hj
    change j.val = i.val at hv
    omega

end
end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentCallback
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_FactorTableDenotation
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.Packing.nonemptyUniversal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! The actual normalized incidence payload has the canonical scalarized
source denotation. Source arrays are witnesses produced by the finite source
machine; their full polynomial meanings identify one fixed incidence jet. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableDenotation
open OAI OAI.Algorithms.SubexponentialSAT.SqrtLog OAI.Algorithms.SubexponentialSAT.SubexpLiftRing OAI.Algorithms.SubexponentialSAT.SubexpQuarticRing
open MomentsProgram TruncatedRingProgram DensePolynomialProgram
open OAI.Algorithms.SubexponentialSAT.Subexp.ConstructivePacking OAI.Algorithms.SubexponentialSAT.MulticolorTypes LayoutProgram
open scoped BigOperators
noncomputable section
variable {R : Type*} [CommRing R]

theorem product_bytes_injective {n B d : ℕ} (hB : 0 < B) :
    Function.Injective (Product.bytes : List (Product.Entry n B d) → List Bool) := by
  intro xs
  induction xs with
  | nil =>
      intro ys h
      cases ys with
      | nil => rfl
      | cons y ys =>
          have hl := congrArg List.length h
          simp [Product.bytes, Normalize.bytes, Squarefree.Program.encodeDictionary,
            Squarefree.Program.rawEntries] at hl
          omega
  | cons x xs ih =>
      intro ys h
      cases ys with
      | nil =>
          have hl := congrArg List.length h
          simp [Product.bytes, Normalize.bytes, Squarefree.Program.encodeDictionary,
            Squarefree.Program.rawEntries] at hl
      | cons y ys =>
          change (Encoding.frame (Squarefree.encodeIndex x.1) ++
            Encoding.frame (RingProgram.flat x.2)) ++ Product.bytes xs =
            (Encoding.frame (Squarefree.encodeIndex y.1) ++
            Encoding.frame (RingProgram.flat y.2)) ++ Product.bytes ys at h
          rw [List.append_assoc, List.append_assoc] at h
          obtain ⟨hk, ht⟩ := Encoding.frame_append_injective h
          obtain ⟨hc, ht⟩ := Encoding.frame_append_injective ht
          exact congrArg₂ List.cons (Prod.ext (Squarefree.encodeIndex_injective hk)
            (RingProgram.flat_injective hB hc)) (ih ht)

theorem specializedJet_atom_origin {n : ℕ} (u J : ℕ) (mask : List Bool) (c : R) :
    specializedJet (n := n) u J mask (Squarefree.Sparse.atom Squarefree.Index.origin c) =
      Squarefree.canonical u J (Squarefree.Sparse.atom Squarefree.Index.origin c) := by
  unfold specializedJet
  rw [HeadEvaluation.specialize_atom]
  simp [Squarefree.Index.origin]
theorem rawDenote_constant {n B d : ℕ} (u J : ℕ)
    (f : RingProgram.Code (Word B) d → R) (c : RingProgram.Code (Word B) d) :
    rawDenote (n := n) f (Squarefree.Sparse.constant u J c) =
      Squarefree.canonical u J (Squarefree.Sparse.atom Squarefree.Index.origin (f c)) := by
  have hm : Dictionary.denoteTable f (Squarefree.Sparse.constant (V := Fin n) u J c) =
      Squarefree.Sparse.constant u J (f c) := by
    by_cases h : 0 < u ∧ 0 < J <;>
      simp [Squarefree.Sparse.constant, h, Dictionary.denoteTable]
  change Squarefree.Sparse.denote _ = _
  rw [hm, Squarefree.Sparse.denote_constant]


/-- High coordinates return the physically stored scalar zero or one, with the
same origin encoding used by the low producer. -/
theorem constant_payload_realizes {n B d : ℕ} (u J : ℕ) (hu : 0 < u) (hJ : 0 < J)
    (f : RingProgram.Code (Word B) d → R) (c : RingProgram.Code (Word B) d)
    (mask : List Bool) :
    ∃ entries : List (Product.Entry n B d),
      Encoding.frame (PerturbationAssembly.originKey n) ++ Encoding.frame (RingProgram.flat c) =
        Product.bytes entries ∧ Good ∅ u J entries ∧
      rawDenote f entries = specializedJet u J mask (Squarefree.Sparse.atom Squarefree.Index.origin (f c)) := by
  refine ⟨Squarefree.Sparse.constant u J c, ?_, constant_good u J c, ?_⟩
  · rw [show Squarefree.Sparse.constant (V := Fin n) u J c = [(Squarefree.Index.origin, c)] by
      simp [Squarefree.Sparse.constant, hu, hJ]]
    exact (PerturbationAssembly.origin_dictionary n c).trans
      (QueryProducerSpace.dictionaryBits_productBytes _)
  · rw [rawDenote_constant, specializedJet_atom_origin]

/-- The actual producer's branch-sensitive bytes admit a valid typed witness
with the fixed source meaning. No coefficient values are supplied by a caller. -/
theorem payload_realizes {r Q d : ℕ} (p : SourceBank.Parameters r Q d)
    (ps : List (ℕ × ℕ)) (P : PackingData (Fin ps.length) (UniversalType r Q 1))
    (u J n f j : ℕ) (hu : 0 < u) (hJ : 0 < J)
    (theta : Coeff (baseWidth 3 p.t) d) (s : FactorTableProgram.OuterStore)
    (payload : List Bool) (hc : (s 546).length = n)
    (hz : s 547 = RingProgram.flat p.ops.zeroRun.1)
    (ho : s 548 = RingProgram.flat p.ops.oneRun.1)
    (h : FactorTableNative.PayloadMeaning p ps P u J n f theta s j payload) :
    ∃ entries : List (Product.Entry n (baseWidth 3 p.t) d),
      payload = Product.bytes entries ∧ Good ∅ u J entries ∧
      rawDenote p.ops.decode entries = specializedJet u J (s 857)
        (PerturbationAssembly.sourceIncidenceJet p ps P n f j theta
          (FactorTableProgram.projectBase s)) := by
  have hsource := h.source
  cases hb : (s 574).getD j false
  · simp only [hb, Bool.false_eq_true, ite_false] at hsource
    obtain ⟨xs, hx, hs, hpayload⟩ := hsource
    obtain ⟨entries, hbytes, hgood, hmeaning⟩ :=
      low_payload_realizes p ps P u J n f j hu hJ theta xs hx (s 546) (s 857) hc hs
    refine ⟨entries, hpayload.trans hbytes, hgood, ?_⟩
    simpa only [PerturbationAssembly.sourceIncidenceJet,
      show FactorTableProgram.projectBase s 574 = s 574 from rfl,
      show FactorTableProgram.projectBase s 546 = s 546 from rfl,
      hb, Bool.false_eq_true, ite_false, fixedLowJet] using hmeaning
  · simp only [hb, ite_true, if_true] at hsource
    let c := if (s 575).getD j false then p.ops.oneRun.1 else p.ops.zeroRun.1
    have hbytes : payload = Encoding.frame (PerturbationAssembly.originKey n) ++
        Encoding.frame (RingProgram.flat c) := by
      rw [hsource]
      cases hh : (s 575).getD j false <;>
        simp only [c, hh, Bool.false_eq_true, ite_false, ite_true, if_true, hz, ho]
    have hvalue : p.ops.decode c = if (s 575).getD j false then 1 else 0 := by
      cases hh : (s 575).getD j false <;>
        simp only [c, hh, Bool.false_eq_true, ite_false, ite_true, if_true,
          p.ops.one_correct, p.ops.zero_correct]
    obtain ⟨entries, he, hg, hv⟩ := constant_payload_realizes (n := n) u J hu hJ p.ops.decode c (s 857)
    refine ⟨entries, hbytes.trans he, hg, ?_⟩
    rw [hvalue] at hv
    simpa only [PerturbationAssembly.sourceIncidenceJet,
      show FactorTableProgram.projectBase s 574 = s 574 from rfl,
      show FactorTableProgram.projectBase s 575 = s 575 from rfl,
      hb, ite_true, if_true] using hv

/-- Exact physical byte decoding transports the source meaning to the same
entries consumed by the actual arithmetic run. No semantic encoding
injectivity or extra validity premise is required. -/
theorem payload_typed_correct {r Q d : ℕ} (p : SourceBank.Parameters r Q d)
    (ps : List (ℕ × ℕ)) (P : PackingData (Fin ps.length) (UniversalType r Q 1))
    (u J n f j : ℕ) (hu : 0 < u) (hJ : 0 < J)
    (theta : Coeff (baseWidth 3 p.t) d) (s : FactorTableProgram.OuterStore)
    (payload : List Bool) (hc : (s 546).length = n)
    (hz : s 547 = RingProgram.flat p.ops.zeroRun.1)
    (ho : s 548 = RingProgram.flat p.ops.oneRun.1)
    (h : FactorTableNative.PayloadMeaning p ps P u J n f theta s j payload)
    (entries : List (Product.Entry n (baseWidth 3 p.t) d))
    (hbytes : payload = Product.bytes entries) :
    Good ∅ u J entries ∧
      rawDenote p.ops.decode entries = specializedJet u J (s 857)
        (PerturbationAssembly.sourceIncidenceJet p ps P n f j theta
          (FactorTableProgram.projectBase s)) := by
  obtain ⟨semantic, hs, hg, hv⟩ :=
    payload_realizes p ps P u J n f j hu hJ theta s payload hc hz ho h
  have he : entries = semantic := product_bytes_injective
    (Nat.mul_pos p.ht (Nat.zero_lt_succ _)) (hbytes.symm.trans hs)
  simpa only [he] using And.intro hg hv

end
end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableDenotation
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_FactorAssignmentCallbackNative
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.Packing.nonemptyUniversal _root_.OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FiniteFallback.literalFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Concrete physical inputs for the streamed factor callback. The source
context is the actual q.ctx, and the dispatcher determines every selected row
and clause. These predicates contain stored words and finite size bounds only.
Their construction from the actual loader/cache run remains an integration step. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentCallback
open OAI BitProgram StructuredCalls SubexpLiftRing SubexpQuarticRing
open SqrtLog SqrtLog.LeafProgram HashCircuitProgram HashCircuitProgram.Native
open IdempotentApplyProgram.Steps MomentsProgram NativeSemantics
open FactorAssignmentProgram
open Subexp.ConstructivePacking MulticolorTypes LayoutProgram DensePolynomialProgram

noncomputable section

variable {r Q n d A S : ℕ} {q : Factor.Spec r Q n d}
  {one seed : FactorAssignmentLoop.Raw n (baseWidth 3 q.p.t) d}
  {a : FactorAssignmentProgram.Data} {f : ℕ}

theorem Input.fetched_stacks (h : Input q A S one seed a f) (rf : Fin 8 → Bool) :
    (fetched q a f rf).stacks = Function.update a.stacks 154
      (LeafFactorDispatchProgram.selectedPayload q.rawRows q.clauses q.marked q.mark f) := by
  rw [fetched, dispatched_stacks a rf q.rawRows q.clauses q.marked q.mark f
    h.rows h.clauses h.count h.mark, callbackInitial_stacks a h.blank]

theorem Input.fetched_frame (h : Input q A S one seed a f) (rf : Fin 8 → Bool)
    (i : Fin 896) (hi : i ≠ 154) : (fetched q a f rf).stacks i = a.stacks i := by
  rw [h.fetched_stacks rf, Function.update_of_ne hi]

/-- A selected record is bounded by the actual serialized master containing
it. This includes the neutral empty payload. -/
theorem Input.payload_length (h : Input q A S one seed a f) :
    (LeafFactorDispatchProgram.selectedPayload q.rawRows q.clauses q.marked q.mark f).length ≤ A := by
  unfold LeafFactorDispatchProgram.selectedPayload
  split_ifs with hh hm
  · rw [List.getD_eq_getElem _ _ hh]
    exact (HashInputProgram.Loop.original_payload_length_le q.rawRows _
      (List.getElem_mem hh)).trans (by rw [← h.rows]; exact h.incoming 701)
  · have hb : q.marked = true := (Bool.and_eq_true_iff.mp hm).1
    have hv : q.mark < q.clauses.length := by
      simpa only [Factor.Spec.clauses, HashInputProgram.Expansion.encodedClauses,
        List.length_map] using q.markValid hb
    rw [List.getD_eq_getElem _ _ hv]
    exact (HashInputProgram.Loop.original_payload_length_le q.clauses _
      (List.getElem_mem hv)).trans (by rw [← h.clauses]; exact h.incoming 700)
  · simp

theorem Input.fetched_wordBound (h : Input q A S one seed a f) (rf : Fin 8 → Bool) :
    ∀ i, ((fetched q a f rf).stacks i).length ≤ A := by
  intro i
  rw [h.fetched_stacks rf]
  by_cases hi : i = 154
  · subst i
    simpa only [Function.update_self] using h.payload_length
  · simpa only [Function.update_of_ne hi] using h.incoming i

/-- Source master words survive dispatch and the concrete unary factor-ID
conversion; only the selected payload154 and selected-factor word556 change. -/
theorem Input.table_frame (h : Input q A S one seed a f) (rf : Fin 8 → Bool)
    (i : Fin 768) (hi154 : FactorTableProgram.basePort i ≠ 154)
    (hi556 : FactorTableProgram.basePort i ≠ 556) :
    (projectState id FactorTableProgram.basePort
      (FactorAssignmentBranches.tableInput (fetched q a f rf) f)).stacks i =
      (projectState localRegister FactorTableProgram.basePort a).stacks i := by
  change (FactorAssignmentBranches.identified (fetched q a f rf) f).stacks
    (FactorTableProgram.basePort i) = a.stacks (FactorTableProgram.basePort i)
  rw [FactorAssignmentBranches.identified_stacks, Function.update_of_ne hi556,
    h.fetched_frame rf _ hi154]

theorem Input.table_scalar (h : Input q A S one seed a f) (rf : Fin 8 → Bool) :
    FactorTableNative.ScalarMasters q.p.t q.p.model q.p.modulus q.p.cache q.J q.p.R
      q.theta (projectState id FactorTableProgram.basePort
        (FactorAssignmentBranches.tableInput (fetched q a f rf) f)) n := by
  have H := h.table_frame rf
  refine ⟨h.scalar.widthPositive, h.scalar.zeroCanonical, h.scalar.zeroBits,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [H 194 (by decide) (by decide)]; exact h.scalar.modulus
  · rw [H 202 (by decide) (by decide)]; exact h.scalar.width
  · rw [H 203 (by decide) (by decide)]; exact h.scalar.zero
  · rw [H 201 (by decide) (by decide)]; exact h.scalar.table
  · rw [H 204 (by decide) (by decide)]; exact h.scalar.degree
  · rw [H 145 (by decide) (by decide)]; exact h.scalar.choicesLength
  · rw [H 280 (by decide) (by decide)]; exact h.scalar.zeroWord
  · rw [H 207 (by decide) (by decide)]; exact h.scalar.oneWord
  · rw [H 78 (by decide) (by decide)]; exact h.scalar.thetaWord
  · rw [H 128 (by decide) (by decide)]; exact h.scalar.ambientCount
  · rw [H 243 (by decide) (by decide)]; exact h.scalar.targetCount
  · rw [H 138 (by decide) (by decide)]; exact h.scalar.radius
  · rw [H 703 (by decide) (by decide)]; exact h.scalar.highLength

theorem Input.table_masters (h : Input q A S one seed a f) (rf : Fin 8 → Bool) :
    FactorTableNative.SourceMasters q.p q.ps q.packing
      (projectState id FactorTableProgram.basePort
        (FactorAssignmentBranches.tableInput (fetched q a f rf) f)) := by
  have H := h.table_frame rf
  constructor
  · rw [H 130 (by decide) (by decide)]; exact h.masters.colors
  · rw [H 131 (by decide) (by decide)]; exact h.masters.nodes
  · rw [H 132 (by decide) (by decide)]; exact h.masters.typeWidth
  · rw [H 710 (by decide) (by decide)]; exact h.masters.positive
  · rw [H 711 (by decide) (by decide)]; exact h.masters.negative
  · rw [H 140 (by decide) (by decide)]; exact h.masters.scalarWidth
  · rw [H 712 (by decide) (by decide)]; exact h.masters.power
  · exact h.masters.powerNegative
  · rw [H 138 (by decide) (by decide)]; exact h.masters.radius
  · rw [H 139 (by decide) (by decide)]; exact h.masters.offset
  · rw [H 135 (by decide) (by decide)]; exact h.masters.metadata
  · rw [H 136 (by decide) (by decide)]; exact h.masters.plans
  · rw [H 713 (by decide) (by decide)]; exact h.masters.inverses
  · rw [H 714 (by decide) (by decide)]; exact h.masters.negatives
  · rw [H 715 (by decide) (by decide)]; exact h.masters.differences
  · rw [H 717 (by decide) (by decide)]; exact h.masters.ringWidth
  · rw [H 716 (by decide) (by decide)]; exact h.masters.rowWidth
  · rw [H 280 (by decide) (by decide)]; exact h.masters.zero
  · rw [H 207 (by decide) (by decide)]; exact h.masters.one
  · rw [H 211 (by decide) (by decide)]; exact h.masters.minusOne
  · rw [H 728 (by decide) (by decide)]; exact h.masters.inverseDenominator

/-- The actual source-table readiness is derived from fixed physical masters
and the already stored original ID; it is not provided by a caller service. -/
theorem Input.table_ready (h : Input q A S one seed a f) (rf : Fin 8 → Bool) :
    FactorTableNative.Ready q.p q.ps q.packing q.u q.J n f A S q.theta
      (FactorAssignmentBranches.tableInput (fetched q a f rf) f) := by
  apply FactorTableNative.Ready.of_masters q.hu q.hJ (h.table_scalar rf) (h.table_masters rf)
  · change (FactorAssignmentBranches.identified (fetched q a f rf) f).stacks 556 = _
    simp only [FactorAssignmentBranches.identified_stacks, Function.update_self]
  · change ((FactorAssignmentBranches.identified (fetched q a f rf) f).stacks 857).length = n
    rw [FactorAssignmentBranches.identified_stacks, Function.update_of_ne (by decide),
      h.fetched_frame rf 857 (by decide)]
    exact h.correction
  · intro i
    change ((FactorAssignmentBranches.identified (fetched q a f rf) f).stacks i).length ≤ A
    rw [FactorAssignmentBranches.identified_stacks]
    by_cases hi : i = 556
    · subst i
      have hf := h.incoming 149
      rw [h.factor, List.length_reverse] at hf
      simp only [Encoding.length_encodeNat] at hf
      simp only [Function.update_self, List.length_replicate]
      omega
    · rw [Function.update_of_ne hi]
      exact h.fetched_wordBound rf i
  · exact h.size
  · exact h.radius

/-- Correction specialization retains the precise current U word, separately
from the high mask and current-head mask. -/
theorem Input.staged_correction (h : Input q A S one seed a f) (rf : Fin 8 → Bool) :
    (FactorTableProgram.staged
      (FactorAssignmentBranches.tableInput (fetched q a f rf) f)).stacks 857 = a.stacks 857 := by
  rw [FactorTableNative.staged_mask]
  change (FactorAssignmentBranches.identified (fetched q a f rf) f).stacks 857 = _
  rw [FactorAssignmentBranches.identified_stacks, Function.update_of_ne (by decide)]
  exact h.fetched_frame rf 857 (by decide)

/-- The exact entries consumed by native arithmetic have the original source
meaning. The byte-injectivity theorem transports denotation without replacing
those entries by another valid representation. -/
theorem Input.payload_correct_oai (h : Input q A S one seed a f)
    (rf : Fin 8 → Bool) (v : Fin n)
    (entries : FactorAssignmentLoop.Raw n (baseWidth 3 q.p.t) d)
    (hm : FactorTableNative.PayloadMeaning q.p q.ps q.packing q.u q.J n f q.theta
      (FactorTableProgram.staged
        (FactorAssignmentBranches.tableInput (fetched q a f rf) f)).stacks v.val
      (Product.bytes entries)) :
    TruncatedRingProgram.Good ∅ q.u q.J entries ∧
      TruncatedRingProgram.rawDenote q.p.ops.decode entries =
        FactorTableDenotation.specializedJet q.u q.J (a.stacks 857)
          (Factor.factorJet q.p q.ps q.packing n f v.val q.theta (a.stacks ∘ lowStack)) := by
  have hc := (h.table_ready rf).staged_common
  have hv := FactorTableDenotation.payload_typed_correct q.p q.ps q.packing
    q.u q.J n f v.val q.hu q.hJ q.theta _ _ hc.choicesLength hc.zeroWord hc.oneWord hm entries rfl
  rw [h.staged_correction rf, h.staged_factorJet rf v.val] at hv
  exact hv

end
end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentCallback
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentCallback.Input.payload_correct_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentCallback.Input.payload_correct_oai
