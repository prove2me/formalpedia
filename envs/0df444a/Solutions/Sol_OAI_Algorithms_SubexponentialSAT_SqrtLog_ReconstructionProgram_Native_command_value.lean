-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLog.ReconstructionProgram.Native.command_value
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T08:20:07.163818+00:00
-- url     : https://prove2.me/submissions/b8915fc4-2063-440d-80a1-b4789e5e58ec

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S136
import Definitions.Def_OAIQ081S158
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_DensePolynomialProgram_PairSpec_BaseReady_frame
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_ReconstructionProgram_Entry_prepare_run
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_ReconstructionProgram_Native_middle_run
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_ReconstructionProgram_controller_run_framed

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
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpCRTOuterFinish
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Final cleanup and complete tape-loop costs for scalar reconstruction.
The arithmetic-middle premise below is an actual execution of a fixed command;
its concrete implementation is assembled separately from the CRT services. -/

namespace SubexponentialSAT.SubexpCRTOuterProgram

open BitProgram StructuredCalls SubexpScanPrimitives
open scoped BigOperators

/-- With the fixed input order, the physically counted index is the current
node's original index, even though processed nodes are stored in reverse. -/
theorem traversal_index {Q : ℕ} (processed remaining : List (Fin Q)) (current : Fin Q)
    (hfull : List.finRange Q = processed.reverse ++ current :: remaining) :
    processed.length = current.val := by
  have hn := List.nodup_finRange Q
  rw [hfull] at hn
  have hm := List.nodup_cons.mp (List.nodup_middle.mp hn)
  have hnot : current ∉ processed.reverse := by
    intro h
    exact hm.1 (List.mem_append_left _ h)
  have hi := congrArg (List.idxOf current) hfull
  rw [List.idxOf_finRange, List.idxOf_append_of_notMem hnot,
    List.idxOf_cons_self, List.length_reverse, Nat.add_zero] at hi
  exact hi.symm

end SubexponentialSAT.SubexpCRTOuterProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_ReconstructionProgramBounds
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Polynomial majorants for the physical middle and outer traversal. The
native service costs can be substituted directly in these inequalities. -/
namespace SubexponentialSAT.SqrtLog.ReconstructionProgram

open SubexponentialSAT SubexpCRTOuterProgram

theorem middleBudget_mono {Q J W Km Ka Kl Q' J' W' Km' Ka' Kl' : ℕ}
    (hQ : Q ≤ Q') (hJ : J ≤ J') (hW : W ≤ W')
    (hm : Km ≤ Km') (ha : Ka ≤ Ka') (hl : Kl ≤ Kl') :
    Middle.budget Q J W Km Ka Kl ≤ Middle.budget Q' J' W' Km' Ka' Kl' := by
  unfold Middle.budget CofactorOuter.budget Cofactor.includeBudget Local.budget
    Horner.budget HornerProgram.budget
  gcongr

end SubexponentialSAT.SqrtLog.ReconstructionProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_ReconstructionProgramLoaded
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Framing lemmas for the exact states reached by the physical node sweep. -/

namespace SubexponentialSAT.SqrtLog.ReconstructionProgram

open SubexponentialSAT BitProgram StructuredCalls SubexpCRTOuterProgram

theorem sweepStore_frame (f : Store) (w : SweepWords) (j : Fin 320)
    (hj : j ∉ sweepChanged) : sweepStore f w j = f j := by
  simp only [sweepChanged, List.mem_cons, List.not_mem_nil, or_false, not_or] at hj
  simp [sweepStore, hj.1, hj.2.1, hj.2.2.1, hj.2.2.2.1, hj.2.2.2.2.1,
    hj.2.2.2.2.2.1, hj.2.2.2.2.2.2.1, hj.2.2.2.2.2.2.2.1, hj.2.2.2.2.2.2.2.2]

theorem initializedStacks_frame (d : Data) (J : ℕ) (exponent : List Bool) (j : Fin 320)
    (hj : j ∉ initializationChanged) : initializedStacks d J exponent j = d.stacks j := by
  simp only [initializationChanged, List.mem_cons, List.not_mem_nil, or_false, not_or] at hj
  simp [initializedStacks, hj.1, hj.2.1, hj.2.2.1, hj.2.2.2.1,
    hj.2.2.2.2.1, hj.2.2.2.2.2.1, hj.2.2.2.2.2.2]

theorem loaded_low {I C : Type*} (f : Store) (encode jet : I → List Bool)
    (encodeAcc : C → List Bool) (processed remaining : List I) (i : I) (acc : C) :
    CRTLocalProgram.LowFrame (f ∘ localPorts)
      ((sweepStore f (loadedReady encode jet encodeAcc processed remaining i acc)) ∘ localPorts) := by
  intro j hj
  apply sweepStore_frame
  simp only [sweepChanged, List.mem_cons, List.not_mem_nil, or_false]
  intro h
  have hv : (localPorts j).val = j.val := rfl
  rcases h with h | h | h | h | h | h | h | h | h <;>
    have hh := congrArg Fin.val h <;> norm_num at hh <;> omega

theorem loaded_update_acc {I C : Type*} (f : Store) (encode jet : I → List Bool)
    (encodeAcc : C → List Bool) (processed remaining : List I) (i : I) (a b : C) :
    Function.update (sweepStore f (loadedReady encode jet encodeAcc processed remaining i a))
      261 (encodeAcc b) =
      sweepStore f (loadedReady encode jet encodeAcc processed remaining i b) := by
  funext j
  by_cases h : j = 261
  · subst j; simp [loadedReady, loadedWords, readyWords]
  · simp only [Function.update_of_ne h]
    simp [sweepStore, loadedReady, loadedWords, readyWords, h]

end SubexponentialSAT.SqrtLog.ReconstructionProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_ReconstructionProgramValue
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Algebraic interpretation of the values produced by the physical outer
Hermite stages. This uses precisely the coefficient list evaluated by the
native Horner loop. -/
namespace SubexponentialSAT.SqrtLog.ReconstructionProgram.Middle

open SubexponentialSAT Polynomial
open scoped BigOperators

variable {C A : Type*} [CommRing A]

/-- The semantic target of the native node contributions is the ordinary
Hermite reconstruction, with no full reconstructed polynomial materialized. -/
theorem sum_node_terms {Q : ℕ} (theta : Fin Q → A) (J : ℕ)
    (inverse : Fin Q → A) (jets : Fin Q → A[X]) :
    ((List.finRange Q).map (fun i => (JetCRT.cofactor theta J i).eval 0 *
      (TruncatedInverse.correction theta J inverse jets i).eval (-theta i))).sum =
      SubexpCRTAtZero.value theta J inverse jets := by
  rw [← List.ofFn_eq_map, List.sum_ofFn]
  rfl

end SubexponentialSAT.SqrtLog.ReconstructionProgram.Middle

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_ReconstructionProgramState
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The concrete caller frame seen at every loaded Hermite node. -/

namespace SubexponentialSAT.SqrtLog.ReconstructionProgram.NativeState

open SubexponentialSAT BitProgram StructuredCalls SubexpCRTOuterProgram

theorem initialized_low (input : Data) (J : ℕ) (exponent : List Bool) :
    CRTLocalProgram.LowFrame
      ((Function.update input.stacks 104 (input.stacks 280)) ∘ localPorts)
      ((initializedStacks input J exponent) ∘ localPorts) := by
  intro i hi
  have hn (j : Fin 320) (hj : 205 ≤ j.val) : localPorts i ≠ j := by
    intro he; have hval := congrArg Fin.val he
    change i.val = j.val at hval
    omega
  simp [initializedStacks,
    hn 261 (by decide), hn 268 (by decide), hn 277 (by decide),
    hn 214 (by decide), hn 257 (by decide), hn 266 (by decide)]

theorem workingClean_frame {I C : Type*} (input : Data) (J : ℕ) (exponent : List Bool)
    (encode jet : I → List Bool) (encodeAcc : C → List Bool)
    (processed remaining : List I) (i : I) (acc : C)
    (hc : ∀ j ∈ workingClean, input.stacks j = []) :
    ∀ j ∈ workingClean, sweepStore (initializedStacks input J exponent)
      (loadedReady encode jet encodeAcc processed remaining i acc) j = [] := by
  intro j hj
  have hs : List.Disjoint workingClean sweepChanged := by
    simp [List.Disjoint, workingClean, Middle.cleanPorts,
      CofactorOuter.cleanPorts, Scalar.cleanPorts, Horner.cleanPorts,
      CRTLocalProgram.localWork, SubexpConvolutionControl.bufferPorts,
      sweepChanged, localPorts]
  have hi : List.Disjoint workingClean initializationChanged := by
    simp [List.Disjoint, workingClean, Middle.cleanPorts,
      CofactorOuter.cleanPorts, Scalar.cleanPorts, Horner.cleanPorts,
      CRTLocalProgram.localWork, SubexpConvolutionControl.bufferPorts,
      initializationChanged, localPorts]
  rw [sweepStore_frame _ _ j (fun h => (List.disjoint_left.mp hs) hj h),
    initializedStacks_frame _ _ _ j (fun h => (List.disjoint_left.mp hi) hj h)]
  exact hc j hj

theorem entry_workingClean (input : Data) (hc : ∀ j ∈ cleanPorts, input.stacks j = []) :
    ∀ j ∈ workingClean, Entry.prepared input.stacks j = [] := by
  intro j hj
  have hd : List.Disjoint workingClean ([5,10] : List (Fin 320)) := by
    simp [List.Disjoint, workingClean, Middle.cleanPorts,
      CofactorOuter.cleanPorts, Scalar.cleanPorts, Horner.cleanPorts,
      CRTLocalProgram.localWork, SubexpConvolutionControl.bufferPorts, localPorts]
  have h5 : j ≠ (5 : Fin 320) := by
    intro he; exact (List.disjoint_left.mp hd) hj (by simp [he])
  have h10 : j ≠ (10 : Fin 320) := by
    intro he; exact (List.disjoint_left.mp hd) hj (by simp [he])
  simpa [Entry.prepared, h5, h10] using hc j (by simp [cleanPorts, hj])

theorem entry_initialClean (input : Data) (hc : ∀ j ∈ cleanPorts, input.stacks j = []) :
    ∀ j ∈ initialCleanPorts, Entry.prepared input.stacks j = [] := by
  intro j hj
  have hd : List.Disjoint initialCleanPorts ([5,10] : List (Fin 320)) := by
    simp [List.Disjoint, initialCleanPorts]
  have h5 : j ≠ (5 : Fin 320) := by
    intro he; exact (List.disjoint_left.mp hd) hj (by simp [he])
  have h10 : j ≠ (10 : Fin 320) := by
    intro he; exact (List.disjoint_left.mp hd) hj (by simp [he])
  simpa [Entry.prepared, h5, h10] using hc j (by simp [cleanPorts, hj])

end SubexponentialSAT.SqrtLog.ReconstructionProgram.NativeState

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_ReconstructionProgramModel
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Complete execution of the fixed native CRT table in the actual searched
ring model. The hypotheses describe input bytes and clean workspace only. -/
namespace SubexponentialSAT.SqrtLog.ReconstructionProgram.Native

open SubexponentialSAT BitProgram StructuredCalls SubexpCRTOuterProgram
open SubexpLiftRing SubexpQuarticRing
open DensePolynomialProgram

private theorem localBudget_index_mono (Q q t d J i j : ℕ) (h : i ≤ j) :
    CRTLocalProgram.Native.budget Q i q t d J ≤ CRTLocalProgram.Native.budget Q j q t d J := by
  unfold CRTLocalProgram.Native.budget CRTLocalProgram.localBudget
    CRTLocalProgram.initializationBudget CRTLocalProgram.preparationBudget
  gcongr

theorem command_value_oai (t : ℕ) (ht : 0 < t) {d Q : ℕ} (hd : 0 < d)
    (a : RingModel.Data d) (M : SubexpPreparedQuartic.Modulus 3 t)
    (cache : RingProgram.ScalarCache 3 t)
    (hcanon : BinaryArithmetic.toNat cache.zero.val < 3^t)
    (hzbits : cache.zero.val = List.replicate (baseWidth 3 t) false)
    (J : ℕ) (hJpos : 0 < J) (hB : 0 < baseWidth 3 t)
    (nodes : Fin Q → Coeff t d) (jets : Fin Q → CRTLocalProgram.Model.Poly (baseWidth 3 t) d J)
    (minusOne : Coeff t d)
    (hminus : (RingProgram.modelRing t ht hd a M cache).decode minusOne = -1)
    (input : SubexpCRTOuterProgram.Data)
    (hscalar : HornerProgram.Services.NativeReady 3 t M cache (HornerProgram.modelTable t a M cache)
      (NativeState.arithmeticBase input))
    (scalarWidth : List Bool) (frame : Fin 6 → List Bool)
    (hpoly : PairSpec.BaseReady 3 t M cache (HornerProgram.modelTable t a M cache)
      (NativeState.arithmeticBase input) scalarWidth frame)
    (hclean : ∀ j ∈ NativeState.cleanPorts, input.stacks j = [])
    (hzero : input.stacks 280 = RingProgram.flat (RingProgram.modelProgram t a M cache).zeroRun.1)
    (hone : input.stacks 207 = RingProgram.flat (RingProgram.modelProgram t a M cache).oneRun.1)
    (hneg : input.stacks 211 = RingProgram.flat minusOne)
    (hJ : input.stacks 243 = List.replicate J true)
    (hnodes : input.stacks 256 = (List.finRange Q).flatMap (fun i => RingProgram.flat (nodes i)))
    (hjets : input.stacks 265 = (List.finRange Q).flatMap (fun i => Fixed.encode (jets i)))
    (hexponent : (input.stacks 209).length = 3^d-2)
    (hprecision : (input.stacks 212).length = t) :
    let ops := RingProgram.modelRing t ht hd a M cache
    let theta := fun i => ops.decode (nodes i)
    ∃ n ≤ budget Q J t d (input.stacks 194).length (input.stacks 202).length,
      ∃ (out : Data) (b : Coeff t d), Eval command n input out ∧
      out.stacks = Function.update (Entry.prepared input.stacks) 261 (RingProgram.flat b) ∧
      ops.decode b = SubexpCRTAtZero.value theta J (LocalValue.inverse theta (3^d) t J)
        (fun i => CRTLocalProgram.Model.denote ops.decode (jets i)) := by
  let ops := RingProgram.modelRing t ht hd a M cache
  obtain ⟨r0, hentry⟩ := Entry.prepare_run input
    (hclean 5 (by simp [NativeState.cleanPorts]))
    (hclean 10 (by simp [NativeState.cleanPorts]))
    (hclean 318 (by simp [NativeState.cleanPorts, initialCleanPorts]))
  let initial : Data := ⟨r0, Entry.prepared input.stacks⟩
  have hw : (initial.stacks 280).length = d*baseWidth 3 t := by
    simp [initial, Entry.prepared, hzero, RingProgram.flat_length]
  have hmiddle : ∀ exponent, BinaryArithmetic.toNat exponent = J → exponent.length ≤ J →
      ∀ processed remaining i acc, List.finRange Q = processed.reverse ++ i :: remaining →
      ∀ rr, ∃ n ≤ middleBudget Q J t d, ∃ rf b,
        Eval middle n
          (sweepState rr (initializedStacks initial J exponent)
            (loadedReady (fun i => RingProgram.flat (nodes i)) (fun i => Fixed.encode (jets i))
              RingProgram.flat processed remaining i acc))
          (sweepState rf (initializedStacks initial J exponent)
            (loadedReady (fun i => RingProgram.flat (nodes i)) (fun i => Fixed.encode (jets i))
              RingProgram.flat processed remaining i b)) ∧
        ops.decode b = ops.decode acc + term t ht hd a M cache nodes J jets i := by
    intro exponent he hl processed remaining i acc hfull rr
    let f := initializedStacks initial J exponent
    let w := loadedReady (fun i => RingProgram.flat (nodes i)) (fun i => Fixed.encode (jets i))
      RingProgram.flat processed remaining i acc
    let current := sweepState rr f w
    have hbase : ((Function.update initial.stacks 104 (initial.stacks 280)) ∘ localPorts) =
        NativeState.arithmeticBase input := by
      simp [NativeState.arithmeticBase, initial, Entry.prepared]
    have hf : CRTLocalProgram.LowFrame (NativeState.arithmeticBase input) (current.stacks ∘ localPorts) := by
      intro j hj
      have h1 := loaded_low f (fun i => RingProgram.flat (nodes i)) (fun i => Fixed.encode (jets i))
        RingProgram.flat processed remaining i acc j hj
      have h2 := NativeState.initialized_low initial J exponent j hj
      rw [hbase] at h2
      exact h1.trans h2
    have hc := NativeState.workingClean_frame initial J exponent
      (fun i => RingProgram.flat (nodes i)) (fun i => Fixed.encode (jets i)) RingProgram.flat
      processed remaining i acc (NativeState.entry_workingClean input hclean)
    have hcMiddle : ∀ j ∈ Middle.cleanPorts, current.stacks j = [] := by
      intro j hj; exact hc j (by simp [NativeState.workingClean, hj])
    have hcLocal : ∀ j ∈ CRTLocalProgram.localWork, current.stacks (localPorts j) = [] := by
      intro j hj
      have hm : localPorts j ∈ CRTLocalProgram.localWork.map localPorts :=
        List.mem_map.mpr ⟨j, hj, rfl⟩
      exact hc _ (by simp only [NativeState.workingClean, List.mem_append, hm, or_true, true_or])
    have hcBuffers : ∀ j, current.stacks (localPorts (SubexpConvolutionControl.bufferPorts j)) = [] := by
      intro j
      have hm : localPorts (SubexpConvolutionControl.bufferPorts j) ∈
          (List.ofFn fun i => localPorts (SubexpConvolutionControl.bufferPorts i)) :=
        List.mem_ofFn.mpr ⟨j, rfl⟩
      exact hc _ (by simp only [NativeState.workingClean, List.mem_append, hm, or_true])
    have hidx := traversal_index processed remaining i hfull
    obtain ⟨n, hn, rf, b, heval, hvalue⟩ := middle_run t ht hd a M cache hcanon hzbits J hJpos hB
      nodes jets minusOne acc hminus processed remaining i hfull current
      (hscalar.frame hf) scalarWidth frame
      (PairSpec.BaseReady.frame 3 t M cache (HornerProgram.modelTable t a M cache) hpoly hf)
      hcBuffers hcMiddle hcLocal
      (by simp [current, f, initial, Entry.prepared, sweepState, sweepStore, initializedStacks, hzero])
      (by simp [current, f, initial, Entry.prepared, sweepState, sweepStore, initializedStacks, hone])
      (by simp [current, f, initial, Entry.prepared, sweepState, sweepStore, initializedStacks, hneg])
      (by simp [current, w, sweepState, loadedReady, loadedWords, readyWords])
      (by simp [current, f, initial, Entry.prepared, sweepState, sweepStore, initializedStacks,
        hnodes, List.ofFn_eq_map, List.flatMap_map])
      (by simpa [current, w, sweepState, loadedReady, loadedWords, readyWords] using hidx)
      (by simp [current, w, sweepState, loadedReady, loadedWords, readyWords])
      (by simp [current, f, initial, Entry.prepared, sweepState, sweepStore, initializedStacks, hJ])
      (by simp [current, w, sweepState, loadedReady, loadedWords, readyWords, List.flatMap_map])
      (by simp [current, w, sweepState, loadedReady, loadedWords, readyWords, List.flatMap_map])
      (by simp [current, w, sweepState, loadedReady, loadedWords, readyWords])
      (by simp [current, w, sweepState, loadedReady, loadedWords, readyWords])
      (by simp [current, f, initial, Entry.prepared, sweepState, sweepStore, initializedStacks,
        hzero, Subexp.BlockCopyProgram.copies, DensePolynomialProgram.encode])
      (by simpa [current, f, initial, Entry.prepared, sweepState, sweepStore, initializedStacks] using hexponent)
      (by simpa [current, f, initial, Entry.prepared, sweepState, sweepStore, initializedStacks] using hprecision)
    have hbound := middleBudget_mono (Q:=Q) (J:=J) (W:=d*baseWidth 3 t)
      (Km:=HornerProgram.Services.mulBudget (baseWidth 3 t) d)
      (Ka:=HornerProgram.Services.addBudget (baseWidth 3 t) d)
      le_rfl le_rfl le_rfl le_rfl le_rfl
      (localBudget_index_mono Q (3^d) t d J i.val Q (Nat.le_of_lt i.isLt))
    refine ⟨n, hn.trans hbound, rf, b, ?_, hvalue⟩
    have hout : Function.update current.stacks 261 (RingProgram.flat b) =
        (sweepState rf f (loadedReady (fun i => RingProgram.flat (nodes i))
          (fun i => Fixed.encode (jets i)) RingProgram.flat processed remaining i b)).stacks :=
      loaded_update_acc f _ _ _ processed remaining i acc b
    have hstate : (⟨rf, Function.update current.stacks 261 (RingProgram.flat b)⟩ : Data) =
        sweepState rf f (loadedReady (fun i => RingProgram.flat (nodes i))
          (fun i => Fixed.encode (jets i)) RingProgram.flat processed remaining i b) :=
      SubexpScanPrimitives.state_ext rfl hout
    rw [hstate] at heval
    exact heval
  obtain ⟨n, hn, out, b, hrun, hout, hvalue⟩ := controller_run_framed
    (fun i => RingProgram.flat (nodes i)) (fun i => Fixed.encode (jets i)) RingProgram.flat
    ops.decode (term t ht hd a M cache nodes J jets) middle initial J (middleBudget Q J t d)
    (List.finRange Q) ops.zeroRun.1
    (by simp [initial, Entry.prepared, hJ]) (NativeState.entry_initialClean input hclean)
    (by intro i; simp [hw, RingProgram.flat_length])
    (by intro i; simp [hw, Fixed.encode_length]) (by rw [hw]; exact Nat.mul_pos hd hB)
    (by simpa [initial, Entry.prepared] using hnodes)
    (by simpa [initial, Entry.prepared] using hjets)
    (by simp [initial, Entry.prepared, hzero, ops]; rfl) ops.zero_correct hmiddle
  refine ⟨_, ?_, out, b, hentry.seq hrun, hout, ?_⟩
  · simpa only [budget, hw, List.length_finRange] using Nat.add_le_add_left hn
      (Entry.budget (input.stacks 194).length (input.stacks 202).length)
  · have hsum := Middle.sum_node_terms
      (fun i => ops.decode (nodes i)) J (LocalValue.inverse (fun i => ops.decode (nodes i)) (3^d) t J)
      (fun i => CRTLocalProgram.Model.denote ops.decode (jets i))
    apply hvalue.trans
    change (List.map (fun i =>
      (JetCRT.cofactor (fun i => ops.decode (nodes i)) J i).eval 0 *
        (TruncatedInverse.correction (fun i => ops.decode (nodes i)) J
          (LocalValue.inverse (fun i => ops.decode (nodes i)) (3 ^ d) t J)
          (fun i => CRTLocalProgram.Model.denote ops.decode (jets i)) i).eval
            (-(ops.decode (nodes i)))) (List.finRange Q)).sum = _
    exact hsum

end SubexponentialSAT.SqrtLog.ReconstructionProgram.Native

end OAI.Algorithms
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLog.ReconstructionProgram.Native.command_value_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLog.ReconstructionProgram.Native.command_value_oai
