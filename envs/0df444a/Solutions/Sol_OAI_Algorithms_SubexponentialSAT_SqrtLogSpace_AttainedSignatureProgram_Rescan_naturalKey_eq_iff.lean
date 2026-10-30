-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.AttainedSignatureProgram.Rescan.naturalKey_eq_iff
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T05:01:43.177595+00:00
-- url     : https://prove2.me/submissions/130ff2d9-d30d-4fd2-8ef8-27378fce133e

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S114

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_AttainedSignatures
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# First occurrences of attained keys

The subtype below is a specification of emissions, not a stored family.
The executable scan checks a candidate against its predecessors one at a time.
The key may be an entire integer row-signature; no coordinate projection occurs.
-/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.AttainedSignatures

variable {N : ℕ} {κ : Type*} (key : Fin N → κ)

theorem assignment_word (h : ℕ) (i : Fin (2 ^ h)) :
    List.ofFn (assignmentEquiv h i) =
      ExecCNFTupleEnumeration.fixedBits h i := by
  have hv := congrArg List.Vector.toList (List.Vector.ofFn_get (Counters.wordEquiv h i))
  change List.ofFn (List.Vector.get (Counters.wordEquiv h i)) =
    List.Vector.toList (Counters.wordEquiv h i)
  simpa only [List.Vector.toList_ofFn] using hv

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.AttainedSignatures
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_BucketProgramArithmetic
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FiniteField.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A fixed binary conditional-add kernel for exact offset signatures. -/
namespace SubexponentialSAT.SqrtLog.BucketProgram

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.ArithmeticCalls
open scoped BigOperators

theorem offsetSignature_eq {h : ℕ} (W : ℤ) (row : Fin h → ℤ) (x : Fin h → Bool) :
    offsetSignature W row x = (h : ℤ)*W + ∑ i, row i*(if x i then 1 else 0) := by
  have hs (i : Fin h) : (if x i then W+row i else W) =
      W + row i*(if x i then 1 else 0) := by cases x i <;> simp
  simp only [offsetSignature, hs, Finset.sum_add_distrib, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

end SubexponentialSAT.SqrtLog.BucketProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_BucketProgramSemantics
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Exact integer meaning of the physical, canonical row keys. -/
namespace SubexponentialSAT.SqrtLog.BucketProgram

theorem canonical_injective : Function.Injective canonical := by
  intro a b h
  have := congrArg SubexponentialSAT.BinaryArithmetic.toNat h
  simpa only [canonical_value] using this

theorem rowValue_ofFn {h : ℕ} (W : List Bool) (c : Fin h → List Bool) (x : Fin h → Bool) :
    rowValue W (List.ofFn c) (List.ofFn x) =
      ∑ i, if x i then SubexponentialSAT.BinaryArithmetic.toNat (c i) else SubexponentialSAT.BinaryArithmetic.toNat W := by
  have hz : List.zipWith (fun a b => if b then SubexponentialSAT.BinaryArithmetic.toNat a
      else SubexponentialSAT.BinaryArithmetic.toNat W) (List.ofFn c) (List.ofFn x) =
      List.ofFn (fun i => if x i then SubexponentialSAT.BinaryArithmetic.toNat (c i)
        else SubexponentialSAT.BinaryArithmetic.toNat W) := by
    apply List.ext_getElem
    · simp
    · intro i h₁ h₂
      simp
  rw [rowValue, hz, List.sum_ofFn]

theorem rowValue_exact {h : ℕ} (W : List Bool) (c : Fin h → List Bool)
    (A : Fin h → ℤ) (x : Fin h → Bool)
    (hc : ∀ i, (SubexponentialSAT.BinaryArithmetic.toNat (c i) : ℤ) =
      (SubexponentialSAT.BinaryArithmetic.toNat W : ℤ) + A i) :
    (rowValue W (List.ofFn c) (List.ofFn x) : ℤ) =
      (h : ℤ)*(SubexponentialSAT.BinaryArithmetic.toNat W : ℤ) +
        ∑ i, A i*(if x i then 1 else 0) := by
  rw [rowValue_ofFn, Nat.cast_sum]
  have hs : (∑ i, ((if x i then SubexponentialSAT.BinaryArithmetic.toNat (c i)
        else SubexponentialSAT.BinaryArithmetic.toNat W) : ℕ) : ℤ) =
      offsetSignature (SubexponentialSAT.BinaryArithmetic.toNat W : ℤ) A x := by
    apply Finset.sum_congr rfl
    intro i hi
    cases hb : x i <;> simp [ hc]
  exact hs.trans (offsetSignature_eq _ _ _)

theorem rowKey_exact_iff {h : ℕ} (W : List Bool) (c : Fin h → List Bool)
    (A : Fin h → ℤ) (x y : Fin h → Bool)
    (hc : ∀ i, (SubexponentialSAT.BinaryArithmetic.toNat (c i) : ℤ) =
      (SubexponentialSAT.BinaryArithmetic.toNat W : ℤ)+A i) :
    canonical (1+rowValue W (List.ofFn c) (List.ofFn x)) =
      canonical (1+rowValue W (List.ofFn c) (List.ofFn y)) ↔
    (∑ i, A i*(if x i then 1 else 0)) = (∑ i, A i*(if y i then 1 else 0)) := by
  rw [canonical_injective.eq_iff, Nat.add_left_cancel_iff]
  have hx := rowValue_exact W c A x hc
  have hy := rowValue_exact W c A y hc
  constructor
  · intro hxy
    rw [hxy] at hx
    linarith
  · intro hxy
    have he : (rowValue W (List.ofFn c) (List.ofFn x) : ℤ) =
      rowValue W (List.ofFn c) (List.ofFn y) := by omega
    exact_mod_cast he

end SubexponentialSAT.SqrtLog.BucketProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_BucketProgramSignatureSemantics
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Equality of the complete physical key is equality of every original
integer constraint value. Framing introduces no collisions. -/
namespace SubexponentialSAT.SqrtLog.BucketProgram
open SubexponentialSAT.Subexp.MatrixProgramSupport

theorem words_injective : Function.Injective words := by
  intro xs
  induction xs with
  | nil =>
      intro ys he
      cases ys with
      | nil => rfl
      | cons y ys =>
          have hl := congrArg List.length he
          simp [words,Encoding.length_frame] at hl ; omega
  | cons x xs ih =>
      intro ys he
      cases ys with
      | nil =>
          have hl := congrArg List.length he
          simp [words,Encoding.length_frame] at hl
      | cons y ys =>
          obtain ⟨hxy,ht⟩ := Encoding.frame_append_injective he
          rw [hxy,ih ht]

theorem signatureValue_exact_iff {h k : ℕ} (W : List Bool)
    (c : Fin k → Fin h → List Bool) (A : Fin k → Fin h → ℤ)
    (x y : Fin h → Bool)
    (hc : ∀ j i, (SubexponentialSAT.BinaryArithmetic.toNat (c j i) : ℤ) =
      (SubexponentialSAT.BinaryArithmetic.toNat W : ℤ)+A j i) :
    signatureValue W (List.ofFn x) (List.ofFn (fun j => List.ofFn (c j))) =
      signatureValue W (List.ofFn y) (List.ofFn (fun j => List.ofFn (c j))) ↔
    ∀ j, (∑ i, A j i*(if x i then 1 else 0)) =
      (∑ i, A j i*(if y i then 1 else 0)) := by
  unfold signatureValue
  rw [words_injective.eq_iff,List.reverse_inj]
  simp only [List.map_ofFn]
  rw [List.ofFn_injective.eq_iff]
  constructor
  · intro he j
    exact (rowKey_exact_iff W (c j) (A j) x y (hc j)).mp (congrFun he j)
  · intro he
    funext j
    exact (rowKey_exact_iff W (c j) (A j) x y (hc j)).mpr (he j)

end SubexponentialSAT.SqrtLog.BucketProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_AttainedSignatureProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Native full-key computation for the resumable attained-signature scan

One invocation preserves the assignment and all raw integer constraint rows.
Its local polynomial-time bound controls every scratch stack at every source
prefix. The generator retains candidate and predecessor cursors separately.
-/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.AttainedSignatureProgram

open OAI.Algorithms.SubexponentialSAT.BitProgram OAI.Algorithms.SubexponentialSAT.StructuredCalls OAI.Algorithms.SubexponentialSAT.Subexp.MatrixProgramSupport
open OAI.Algorithms.SubexponentialSAT.SqrtLog.BucketProgram

/-- Every physical bit in the complete key is retained; equality is precisely
full integer-signature equality, including every original raw row. -/
theorem key_eq_iff {h d : ℕ} (W : List Bool)
    (c : Fin d → Fin h → List Bool) (A : Fin d → Fin h → ℤ)
    (x y : Fin h → Bool)
    (hc : ∀ j i, (OAI.Algorithms.SubexponentialSAT.BinaryArithmetic.toNat (c j i) : ℤ) =
      (OAI.Algorithms.SubexponentialSAT.BinaryArithmetic.toNat W : ℤ) + A j i) :
    signatureValue W (List.ofFn x) (List.ofFn (fun j => List.ofFn (c j))) =
      signatureValue W (List.ofFn y) (List.ofFn (fun j => List.ofFn (c j))) ↔
    OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSignatureBound.boolSignature A x =
      OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSignatureBound.boolSignature A y := by
  rw [signatureValue_exact_iff W c A x y hc]
  exact ⟨fun h => funext h, fun h => congrFun h⟩

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.AttainedSignatureProgram
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_AttainedSignatureRescan
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Actual bounded-word predecessor rescan and its uniform source-prefix storage. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.AttainedSignatureProgram

open OAI.Algorithms.SubexponentialSAT.BitProgram OAI.Algorithms.SubexponentialSAT.StructuredCalls OAI.Algorithms.SubexponentialSAT.Subexp.MatrixProgramSupport
open OAI.Algorithms.SubexponentialSAT.SqrtLog.BucketProgram

namespace Rescan

theorem naturalKey_eq_iff_oai {h d : ℕ} (W : List Bool)
    (c : Fin d → Fin h → List Bool) (A : Fin d → Fin h → ℤ)
    (hc : ∀ j i, (BinaryArithmetic.toNat (c j i) : ℤ) =
      (BinaryArithmetic.toNat W : ℤ) + A j i) (i j : Fin (2 ^ h)) :
    naturalKey W (List.ofFn (fun row => List.ofFn (c row))) h i =
      naturalKey W (List.ofFn (fun row => List.ofFn (c row))) h j ↔
      AttainedSignatures.integerKey A i = AttainedSignatures.integerKey A j := by
  unfold naturalKey
  rw [← AttainedSignatures.assignment_word h i, ← AttainedSignatures.assignment_word h j]
  exact key_eq_iff W c A _ _ hc


end Rescan

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.AttainedSignatureProgram
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.AttainedSignatureProgram.Rescan.naturalKey_eq_iff_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.AttainedSignatureProgram.Rescan.naturalKey_eq_iff_oai
