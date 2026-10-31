-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadSumCorrect.gate_source_iff
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T09:09:25.477261+00:00
-- url     : https://prove2.me/submissions/25c4a70a-9b91-4551-bb09-1fae9bcb2d51

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S172

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
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HeadIdentifierProgramSemantics
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.HeadIdentifierProgram
open SubexponentialSAT BitProgram StructuredCalls

theorem headOrder_ids (p : ℕ → Bool) (n : ℕ) :
    HeadScatterProgram.headIds (headOrder p n)=chosenIds p n := by
  simp [HeadScatterProgram.headIds, headOrder, count]

end SubexponentialSAT.SqrtLog.HeadIdentifierProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HighIncidenceProgramOrder
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The physical mask traverses original coordinates in descending order.
This explicit order, rather than an arbitrary finite-type equivalence,
identifies each odometer position with its actual original variable. -/
namespace SubexponentialSAT.SqrtLog.HighIncidenceProgram.Order

theorem selected_map {A : Type*} (xs : List A) (p : A → Bool) (x : A → Bool) :
    Restriction.selected true (xs.map p) (xs.map x) = (xs.filter p).map x := by
  induction xs with
  | nil => rfl
  | cons v xs ih => cases hp : p v <;> simp [Restriction.selected, hp, ih]

end SubexponentialSAT.SqrtLog.HighIncidenceProgram.Order

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafWeightProgramModel
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The native three-mask branch computes the exact squarefree head weight. -/
namespace SubexponentialSAT.SqrtLog.LeafWeightProgram

open SubexponentialSAT
open scoped BigOperators

theorem good_ofFn_iff {n : ℕ} (a s h : Fin n → Bool) :
    good (List.ofFn a) (List.ofFn s) (List.ofFn h) = true ↔
      ∀ i, s i = true → h i = true → a i = true := by
  induction n with
  | zero => simp [good]
  | succ n ih =>
    cases ha : a 0 <;> cases hs : s 0 <;> cases hh : h 0 <;>
      simp [List.ofFn_succ,good,ha,hs,hh,ih,Fin.forall_fin_succ]

end SubexponentialSAT.SqrtLog.LeafWeightProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_HeadRepresentativeSemantics
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadRepresentativeSemantics
open OAI.Algorithms.SubexponentialSAT.SqrtLog
open HeadIdentifierProgram
open _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgram

/-- The actual chosen-ID word fixes the ascending selection order. -/
theorem headOrder_stream (p : ℕ → Bool) (n : ℕ) :
    (List.finRange n).filter (fun v => p v.val)=List.ofFn (headOrder p n) := by
  apply (List.map_injective_iff.mpr (Fin.val_injective : Function.Injective (Fin.val (n:=n))))
  rw [List.map_ofFn]
  change _=HeadScatterProgram.headIds (headOrder p n)
  rw [headOrder_ids]
  simpa only [List.map_coe_finRange,chosenIds,Function.comp_def] using
    (List.filter_map (f:=(Fin.val : Fin n → ℕ)) (p:=p) (l:=List.finRange n)).symm

/-- The native selected-bit scan emits exactly the current head's ambient
coordinates in the already emitted headOrder, including the empty head. -/
theorem selected_headOrder (p : ℕ → Bool) (n : ℕ) (x : Fin n → Bool) :
    Restriction.selected true (List.ofFn (fun v : Fin n => p v.val)) (List.ofFn x) =
      List.ofFn (fun i => x (headOrder p n i)) := by
  rw [List.ofFn_eq_map,List.ofFn_eq_map,Order.selected_map,headOrder_stream,List.map_ofFn]
  rfl

/-- Combined with NativeHeadSelect.prepared_E/prepared_H, this identifies
the actual gate test with membership in E at original head coordinates. -/
theorem head_correction_iff (p : ℕ → Bool) (n : ℕ) (E : Finset (Fin n))
    (bits : Fin (count p n) → Bool) :
    LeafWeightProgram.good (List.ofFn bits)
      (Restriction.selected true (List.ofFn (fun v : Fin n => p v.val))
        (LeafWeightProgram.supportBits ⟨E⟩)) (List.replicate (count p n) true)=true ↔
      ∀ i,headOrder p n i∈E → bits i=true := by
  rw [LeafWeightProgram.supportBits,selected_headOrder,
    ←List.ofFn_const,LeafWeightProgram.good_ofFn_iff]
  simp

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadRepresentativeSemantics
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_SignatureKeySource
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.Packing.nonemptyUniversal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Actual full signature keys and the source head labels

The selected-coordinate list retains its physical order. The equivalence below
is the existing explicit selected-ID equivalence; it neither sorts assignments
nor replaces the full raw matrix by a basis.
-/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureKeySource

open scoped BigOperators
open OAI.Algorithms.SubexponentialSAT.SqrtLog
open OAI.Algorithms.SubexponentialSAT.MulticolorTypes OAI.Algorithms.SubexponentialSAT.Subexp.ConstructivePacking
open BucketTupleProgram.Concrete
open LayoutProgram


variable {r Q d n : ℕ}

/-- Reindexing the actual selected columns gives exactly the full integer
label used by source locality, with every original row retained. -/
theorem ordered_signature (p : SourceBank.Parameters r Q d) (ps : List (ℕ × ℕ))
    (P : PackingData (Fin ps.length) (UniversalType r Q 1))
    (owner : Fin ps.length → Fin n) (head : Fin Q → Fin n → Fin r)
    (H : Finset (Fin n)) (node : Fin Q) (g : Fin r)
    (js : List ℕ) (hb : ∀ v ∈ js, v < n) (hn : js.Nodup)
    (hs : ∀ v : Fin n, v.val ∈ js ↔ ∃ _ : v ∉ H, head node v = g)
    (a : Moments.Head (fun v : ResidualEmbedding.Free H => head node v.val) g → Bool) :
    LayoutSignatureBound.boolSignature
      (fun (j : Fin ps.length) (i : Fin js.length) =>
        LayoutProducedMatrix.literalNat P owner p.aWord.length p.R node j.val (js.get i))
      (freeAssignmentEquiv H (fun v => head node v.val) g js hb hn hs a) =
      HeadSourceLocality.freeLabel p ps P owner head H node g a := by
  funext j
  exact (freeOrder H (fun v => head node v.val) g js hb hn hs).sum_comp
    (fun v => LayoutProducedMatrix.literalNat P owner p.aWord.length p.R node
      j.val v.val.val.val * (if a v then 1 else 0 : ℤ))

/-- Exact byte equality of keys computed from the ordered shifted matrix is
equivalent to equality of the full source labels. The coefficient premise is
the pointwise interpretation proved for the actual native loader output. -/
theorem key_eq_freeLabel (p : SourceBank.Parameters r Q d) (ps : List (ℕ × ℕ))
    (P : PackingData (Fin ps.length) (UniversalType r Q 1))
    (owner : Fin ps.length → Fin n) (head : Fin Q → Fin n → Fin r)
    (H : Finset (Fin n)) (node : Fin Q) (g : Fin r)
    (js : List ℕ) (hb : ∀ v ∈ js, v < n) (hn : js.Nodup)
    (hs : ∀ v : Fin n, v.val ∈ js ↔ ∃ _ : v ∉ H, head node v = g)
    (W : List Bool) (c : Fin ps.length → Fin js.length → List Bool)
    (hc : ∀ j i, (BinaryArithmetic.toNat (c j i) : ℤ) =
      (BinaryArithmetic.toNat W : ℤ) +
        LayoutProducedMatrix.literalNat P owner p.aWord.length p.R node j.val (js.get i))
    (x y : Moments.Head (fun v : ResidualEmbedding.Free H => head node v.val) g → Bool) :
    BucketProgram.signatureValue W
        (List.ofFn (freeAssignmentEquiv H (fun v => head node v.val) g js hb hn hs x))
        (List.ofFn (fun j => List.ofFn (c j))) =
      BucketProgram.signatureValue W
        (List.ofFn (freeAssignmentEquiv H (fun v => head node v.val) g js hb hn hs y))
        (List.ofFn (fun j => List.ofFn (c j))) ↔
      HeadSourceLocality.freeLabel p ps P owner head H node g x =
        HeadSourceLocality.freeLabel p ps P owner head H node g y := by
  rw [AttainedSignatureProgram.key_eq_iff W c _ _ _ hc]
  rw [ordered_signature p ps P owner head H node g js hb hn hs x,
    ordered_signature p ps P owner head H node g js hb hn hs y]

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureKeySource
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_HeadSumCorrect
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.Packing.nonemptyUniversal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Semantic correctness of the concrete head accumulator. Native dictionary
witnesses are retained only for the current partial sum, and their meaning is
proved using the actual finite-ring normalization program. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadSumCorrect

open OAI BitProgram StructuredCalls SqrtLog SqrtLog.MomentsProgram
open SubexpLiftRing SubexpQuarticRing TruncatedRingProgram HeadSumProgram
open scoped BigOperators


open HeadIdentifierProgram

/-- The concrete correction gate tests the selected original coordinates of
the typed head, using the same order as its assignment counter. -/
theorem candidate_correction_iff {n r : ℕ} (H E : Finset (Fin n))
    (head : {v : Fin n // v ∉ H} → Fin r) (g : Fin r) (p : ℕ → Bool)
    (hs : ∀ v : Fin n, v.val ∈ chosenIds p n ↔ ∃ hv : v ∉ H, head ⟨v, hv⟩ = g)
    (candidate : {v : {v : Fin n // v ∉ H} // head v = g} → Bool) :
    LeafWeightProgram.good
      (List.ofFn (BucketTupleProgram.Concrete.freeAssignmentEquiv H head g (chosenIds p n)
        (chosenIds_bound p n) (chosenIds_nodup p n) hs candidate))
      (HighIncidenceProgram.Restriction.selected true (List.ofFn (fun v : Fin n => p v.val))
        (LeafWeightProgram.supportBits ⟨E⟩))
      (List.replicate (count p n) true) = true ↔
      ∀ v : {v : {v : Fin n // v ∉ H} // head v = g},
        v.val.val ∈ E → candidate v = true := by
  let bits : Fin (count p n) → Bool :=
    BucketTupleProgram.Concrete.freeAssignmentEquiv H head g (chosenIds p n)
      (chosenIds_bound p n) (chosenIds_nodup p n) hs candidate
  let order : Fin (count p n) ≃ {v : {v : Fin n // v ∉ H} // head v = g} :=
    BucketTupleProgram.Concrete.freeOrder H head g (chosenIds p n)
      (chosenIds_bound p n) (chosenIds_nodup p n) hs
  change LeafWeightProgram.good (List.ofFn bits)
    (HighIncidenceProgram.Restriction.selected true (List.ofFn (fun v : Fin n => p v.val))
      (LeafWeightProgram.supportBits ⟨E⟩))
    (List.replicate (count p n) true) = true ↔ _
  have hcorr := HeadRepresentativeSemantics.head_correction_iff p n E bits
  have hbits (i) : bits i = candidate (order i) := rfl
  have hval (i) : (order i).val.val = headOrder p n i := rfl
  constructor
  · intro h v hv
    have hc := hcorr.mp h
    obtain ⟨i, rfl⟩ := order.surjective v
    exact (hbits i).symm.trans (hc i (by simpa only [hval] using hv))
  · intro h
    apply hcorr.mpr
    intro i hi
    exact (hbits i).trans (h (order i) (by simpa only [hval] using hi))

open OAI.Algorithms.SubexponentialSAT.MulticolorTypes OAI.Algorithms.SubexponentialSAT.Subexp.ConstructivePacking
open OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram OAI.Algorithms.SubexponentialSAT.SqrtLog.BucketTupleProgram.Concrete

/-- The actual full key and correction words admit exactly the intended
original-coordinate signature fiber. Every raw matrix row is retained. -/
theorem gate_source_iff_oai {r Q d n : ℕ} (p : SourceBank.Parameters r Q d)
    (ps : List (ℕ × ℕ)) (P : PackingData (Fin ps.length) (UniversalType r Q 1))
    (owner : Fin ps.length → Fin n) (head : Fin Q → Fin n → Fin r)
    (H E : Finset (Fin n)) (node : Fin Q) (g : Fin r) (pick : ℕ → Bool)
    (hs : ∀ v : Fin n, v.val ∈ chosenIds pick n ↔ ∃ _ : v ∉ H, head node v = g)
    (W : List Bool) (c : Fin ps.length → Fin (count pick n) → List Bool)
    (hc : ∀ j i, (BinaryArithmetic.toNat (c j i) : ℤ) =
      (BinaryArithmetic.toNat W : ℤ) +
        LayoutProducedMatrix.literalNat P owner p.aWord.length p.R node j.val
          ((chosenIds pick n).get i))
    (candidate representative : Moments.Head
      (fun v : ResidualEmbedding.Free H => head node v.val) g → Bool)
    (a : HeadSumProgram.Data) (hW : a.stacks 864 = W)
    (hbits : a.stacks 859 = List.ofFn (freeAssignmentEquiv H
      (fun v => head node v.val) g (chosenIds pick n)
      (chosenIds_bound pick n) (chosenIds_nodup pick n) hs candidate))
    (hkey : a.stacks 866 = BucketProgram.signatureValue W
      (List.ofFn (freeAssignmentEquiv H (fun v => head node v.val) g (chosenIds pick n)
        (chosenIds_bound pick n) (chosenIds_nodup pick n) hs representative))
      (List.ofFn (fun j => List.ofFn (c j))))
    (hE : a.stacks 867 = HighIncidenceProgram.Restriction.selected true
      (List.ofFn (fun v : Fin n => pick v.val)) (LeafWeightProgram.supportBits ⟨E⟩))
    (hH : a.stacks 868 = List.replicate (count pick n) true) :
    gateValue a (List.ofFn (fun j => List.ofFn (c j))) = true ↔
      HeadSourceLocality.freeLabel p ps P owner head H node g candidate =
        HeadSourceLocality.freeLabel p ps P owner head H node g representative ∧
      ∀ v : Moments.Head (fun v : ResidualEmbedding.Free H => head node v.val) g,
        v.val.val ∈ E → candidate v = true := by
  rw [gateValue, hW, hbits, hkey, hE, hH, Bool.and_eq_true, decide_eq_true_eq]
  exact and_congr
    (SignatureKeySource.key_eq_freeLabel p ps P owner head H node g
      (chosenIds pick n) (chosenIds_bound pick n) (chosenIds_nodup pick n) hs W c hc
      candidate representative)
    (candidate_correction_iff H E (fun v => head node v.val) g pick hs candidate)


end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadSumCorrect
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadSumCorrect.gate_source_iff_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadSumCorrect.gate_source_iff_oai
