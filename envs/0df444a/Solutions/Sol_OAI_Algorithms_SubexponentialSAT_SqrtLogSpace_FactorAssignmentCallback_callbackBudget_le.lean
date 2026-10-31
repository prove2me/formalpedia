-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentCallback.callbackBudget_le
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T11:22:23.303459+00:00
-- url     : https://prove2.me/submissions/025f944d-2336-40db-8f12-7c4c6ee59c6b

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S189
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_FactorTableSpace_staged_stack_bound

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
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramFactorBoundsPolynomial
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Uniform numerical bounds. Z bounds encoded sizes and retained capacity,
not merely the bit length of the original formula. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.FactorBounds
open HashCircuitProgram

theorem expansionBound_le (b ml m sourceLength weightLength count Z : ℕ) (hZ : 1 ≤ Z)
    (hb : b ≤ Z) (hml : ml ≤ Z) (hm : m ≤ Z) (hs : sourceLength ≤ Z)
    (hw : weightLength ≤ Z) (hc : count ≤ Z) :
    expansionBound b ml m sourceLength weightLength count ≤ 2000*Z^3 := by
  have h : expansionBound b ml m sourceLength weightLength count ≤ expansionBound Z Z Z Z Z Z := by
    dsimp only [expansionBound,HashInputProgram.Loop.termBudget,HashInputProgram.LoopDecode.budget]
    gcongr
  apply h.trans
  have he : expansionBound Z Z Z Z Z Z = 464*Z^3+586*Z^2+217*Z+3 := by
    dsimp only [expansionBound,HashInputProgram.Loop.termBudget,HashInputProgram.LoopDecode.budget]
    ring
  rw [he]
  have h0 : 1 ≤ Z^3 := Nat.one_le_pow _ _ hZ
  have h1 : Z ≤ Z^3 := by simpa using Nat.pow_le_pow_right hZ (show 1 ≤ 3 by decide)
  have h2 : Z^2 ≤ Z^3 := Nat.pow_le_pow_right hZ (by decide)
  omega

end SubexponentialSAT.SqrtLog.LeafProgram.FactorBounds

end OAI.Algorithms
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

/-- The entire native table construction costs a fixed quadratic polynomial
in the per-literal budget, ambient dimension and specialized payload width. -/
theorem tableBudget_le (n K L : ℕ) :
    tableBudget n K L ≤ 64 * (n + K + L + 1) ^ 2 := by
  let T := n + K + L + 1
  have hT : 1 ≤ T := by dsimp [T]; omega
  have hn : n ≤ T := by dsimp [T]; omega
  have hK : K ≤ T := by dsimp [T]; omega
  have hrow : 2 * n + 2 * L + 4 ≤ 4 * T := by dsimp [T]; omega
  have htable : n * (2 * n + 2 * L + 4) ≤ T * (4 * T) :=
    Nat.mul_le_mul hn hrow
  have hbody : n * (K + 2) ≤ T * (T + 2) :=
    Nat.mul_le_mul hn (Nat.add_le_add_right hK 2)
  have hsquare : T ≤ T ^ 2 := by nlinarith
  change 7 * n + n * (K + 2) + 6 * (n * (2 * n + 2 * L + 4)) + 16 ≤ 64 * T ^ 2
  nlinarith

theorem entryPorts_length_le : entryPorts.length ≤ 348 := by
  have hfilter := List.length_filter_le (fun i : Fin 768 => i ≠ 556)
    LeafProgram.Incidence.workerPorts
  have hworker : LeafProgram.Incidence.workerPorts.length = 340 := by
    simp only [LeafProgram.Incidence.workerPorts, List.length_map, List.length_finRange]
  rw [hworker] at hfilter
  simpa only [entryPorts, List.length_append, List.length_map,
    List.length_cons, List.length_nil] using Nat.add_le_add_right hfilter 8

/-- All pre/postprocessing and the actual table loop fit a fixed quadratic
polynomial; the degree is independent of the input and every traversal count. -/
theorem commandBudget_le (B n K L : ℕ) :
    commandBudget B n K L ≤ 1000000 * (B + n + K + L + 1) ^ 2 := by
  let T := B + n + K + L + 1
  have hT : 1 ≤ T := by dsimp [T]; omega
  have hB : B ≤ T := by dsimp [T]; omega
  have hn : n ≤ T := by dsimp [T]; omega
  have hsq : T ≤ T ^ 2 := by nlinarith
  have hrow : literalRecordBound n L ≤ 4 * T := by
    dsimp [literalRecordBound, T]
    omega
  have htable : n * literalRecordBound n L ≤ 4 * T ^ 2 := by
    have h := Nat.mul_le_mul hn hrow
    nlinarith
  have hmid : middleBound B n L ≤ 1132 * T ^ 2 := by
    dsimp only [middleBound]
    nlinarith
  have hlocal : tableBudget n K L ≤ 64 * T ^ 2 := by
    apply (tableBudget_le n K L).trans
    gcongr
    dsimp [T]
    omega
  have hclear : entryPorts.length * (2 * B + 3) ≤ 1740 * T ^ 2 := by
    have h := Nat.mul_le_mul_right (2 * B + 3) entryPorts_length_le
    nlinarith
  dsimp only [commandBudget]
  change _ ≤ 1000000 * T ^ 2
  nlinarith

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

theorem Input.tableTime_le (h : Input q A S one seed a f) (rf : Fin 8 → Bool) :
    FactorAssignmentBranches.tableTime q.p q.u q.J n A S (fetched q a f rf) f ≤
      tableBudget q A S := by
  have hstage := FactorTableSpace.staged_stack_bound
    (FactorAssignmentBranches.tableInput (fetched q a f rf) f) A
    (h.table_ready rf).incoming 574
  have hwork : FactorTableNative.specializedLiteralWork q.p q.u q.J n S
      ((FactorTableProgram.staged
        (FactorAssignmentBranches.tableInput (fetched q a f rf) f)).stacks 574).length ≤
      FactorTableNative.specializedLiteralWork q.p q.u q.J n S (1029*A+99) := by
    unfold FactorTableNative.specializedLiteralWork
    omega
  apply (FactorTableSpace.commandBudget_le A n _ _).trans
  unfold tableBudget
  gcongr

theorem Input.factor_le (h : Input q A S one seed a f) : f ≤ A := by
  have hf := h.incoming 149
  rw [h.factor, List.length_reverse] at hf
  simp only [Encoding.length_encodeNat] at hf
  omega

/-- The actual dispatcher pays for all losing records in both encoded masters. -/
theorem Input.dispatchBudget_le (h : Input q A S one seed a f) :
    LeafFactorDispatchProgram.budget q.rawRows q.clauses q.mark f ≤ 102*A+138 := by
  have hrow := h.incoming 701
  have hclause := h.incoming 700
  have hcount := h.incoming 704
  have hmark := h.incoming 705
  rw [h.rows] at hrow
  rw [h.clauses] at hclause
  rw [h.count, List.length_replicate] at hcount
  rw [h.mark] at hmark
  simp only [Encoding.length_encodeNat] at hmark
  have hid := h.factor_le
  unfold LeafFactorDispatchProgram.budget LeafFactorDispatchProgram.dispatchBound
    LeafFactorDispatchProgram.branchBound
  omega

theorem callbackBudget_le_oai (h : Input q A S one seed a f) (width Z : ℕ)
    (hZ : 1 ≤ Z) (hA : A ≤ Z) (hbit : q.bitWidth ≤ Z)
    (hshape : d*baseWidth 3 q.p.t ≤ Z)
    (hhashScale : ∀ hf : f < q.rows.length,
      FactorEvaluationSpace.inputScale (baseWidth 3 q.p.t) d n q.u q.J
        width q.rows[f].length q.digits.length ≤ Z)
    (hmarkScale : FactorEvaluationSpace.inputScale (baseWidth 3 q.p.t) d n q.u q.J
      q.markedClause.length 0 0 ≤ Z)
    (rf : Fin 8 → Bool) :
    callbackBudget q A S width a f rf ≤ uniformCallbackBudget q A S Z := by
  have hclear' : clearCallbackCost a ≤ callbackScratch.length * (2*A+3)+1 := by
    unfold clearCallbackCost
    have hc := SubexpSetupStorage.clearManyCost_le callbackScratch
      (projectState localRegister lowStack a) A (fun i => h.incoming (lowStack i))
    omega
  have hraw := h.incoming 149
  have hdispatch := h.dispatchBudget_le
  have htable := h.tableTime_le rf
  have hid := h.factor_le
  have hp : ((fetched q a f rf).stacks 154).length ≤ A := h.fetched_wordBound rf 154
  have hmod : ((fetched q a f rf).stacks 707).length ≤ Z :=
    (h.fetched_wordBound rf 707).trans hA
  have hclauses : (Encoding.encodeList id q.clauses).length ≤ Z := by
    rw [← h.clauses]
    exact (h.incoming 700).trans hA
  have hcount : q.clauses.length ≤ Z :=
    (Nat.le_succ _).trans ((Encoding.length_encodeList_lower id q.clauses).trans hclauses)
  by_cases hf : f < q.rows.length
  · have hs := hhashScale hf
    have hterms : q.rows[f].length ≤ Z := by
      unfold FactorEvaluationSpace.inputScale at hs
      omega
    have hexp := FactorBounds.expansionBound_le q.bitWidth
      ((fetched q a f rf).stacks 707).length q.clauses.length
      (Encoding.encodeList id q.clauses).length ((d-1+1)*baseWidth 3 q.p.t)
      q.rows[f].length Z hZ hbit hmod hcount hclauses
      (by simpa only [Nat.sub_add_cancel q.p.hd] using hshape) hterms
    change HashInputProgram.Loop.uniformBudget q.p.t (d-1) q.bitWidth
      ((fetched q a f rf).stacks 707) q.clauses q.rows[f].length ≤ 2000*Z^3 at hexp
    have hservice : FactorEvaluationSpace.serviceBudget (baseWidth 3 q.p.t) d n q.u q.J
        width q.rows[f].length q.digits.length ≤ 14000000*Z^9 := by
      unfold FactorEvaluationSpace.serviceBudget
      gcongr
    simp only [callbackBudget, dite_eq_left hf, hashBranchBudget, uniformCallbackBudget]
    omega
  · have hservice : FactorEvaluationSpace.serviceBudget (baseWidth 3 q.p.t) d n q.u q.J
        q.markedClause.length 0 0 ≤ 14000000*Z^9 := by
      unfold FactorEvaluationSpace.serviceBudget
      gcongr
    simp only [callbackBudget, dite_eq_right hf, uniformCallbackBudget]
    split
    · unfold markedBranchBudget
      omega
    · omega

end
end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentCallback
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentCallback.callbackBudget_le_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentCallback.callbackBudget_le_oai
