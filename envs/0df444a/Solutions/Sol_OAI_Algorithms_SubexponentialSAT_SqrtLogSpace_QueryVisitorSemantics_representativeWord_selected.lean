-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorSemantics.representativeWord_selected
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T10:35:41.687458+00:00
-- url     : https://prove2.me/submissions/80775406-e28e-414e-b8f6-f7d4a52663c3

import Mathlib
import Definitions.Def_OAIQ081S185

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

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadRepresentativeSemantics
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_SignatureTupleWords
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Exact physical words for the emitted numeric head representatives. These
are proof-level coordinate maps; the executable cursor retains only its bounded
binary word and uses the existing native selected-coordinate scan. -/
noncomputable section
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleWords
open Classical
open OAI.Algorithms.SubexponentialSAT.SqrtLog

open BucketTupleProgram.Concrete HeadIdentifierProgram in
/-- The numeric representative word is exactly the selected ambient bits of
its source head assignment, in the physical loader's ascending coordinate
order. This includes an empty head and does not select a key representative
in a second, potentially different order. -/
theorem representative_selected_word {n r : ℕ}
    (H : Finset (Fin n)) (head : Fin n → Fin r) (g : Fin r) (p : ℕ → Bool)
    (hs : ∀ v : Fin n,v.val∈chosenIds p n ↔ ∃ _ : v∉H,head v=g)
    (candidate : Fin (2^(chosenIds p n).length)) (current : Fin n → Bool)
    (hcurrent : ∀ (v : Fin n) (hv : v∉H) (hg : head v=g),
      current v=((freeAssignmentEquiv H (fun v => head v.val) g (chosenIds p n)
        (chosenIds_bound p n) (chosenIds_nodup p n) hs).symm
          (AttainedSignatures.assignmentEquiv (chosenIds p n).length candidate)) ⟨⟨v,hv⟩,hg⟩) :
    HighIncidenceProgram.Restriction.selected true
      (List.ofFn (fun v : Fin n => p v.val)) (List.ofFn current)=
      ExecCNFTupleEnumeration.fixedBits (chosenIds p n).length candidate.val := by
  rw [HeadRepresentativeSemantics.selected_headOrder,
    ←AttainedSignatures.assignment_word]
  apply congrArg List.ofFn
  funext i
  let order := freeOrder H (fun v => head v.val) g (chosenIds p n)
    (chosenIds_bound p n) (chosenIds_nodup p n) hs
  let rep := (freeAssignmentEquiv H (fun v => head v.val) g (chosenIds p n)
    (chosenIds_bound p n) (chosenIds_nodup p n) hs).symm
      (AttainedSignatures.assignmentEquiv (chosenIds p n).length candidate)
  have he : (order i).val.val=headOrder p n i := by apply Fin.ext; rfl
  have hc := hcurrent (order i).val.val (order i).val.property (order i).property
  change current (order i).val.val=rep (order i) at hc
  have hr : rep (order i)=AttainedSignatures.assignmentEquiv (chosenIds p n).length candidate i :=
    congrFun ((freeAssignmentEquiv H (fun v => head v.val) g (chosenIds p n)
      (chosenIds_bound p n) (chosenIds_nodup p n) hs).apply_symm_apply
        (AttainedSignatures.assignmentEquiv (chosenIds p n).length candidate)) i
  exact (he ▸ hc).trans hr

open BucketTupleProgram.Concrete HeadIdentifierProgram

theorem ambientAssignment_head {n r : ℕ} (H : Finset (Fin n)) (head : Fin n → Fin r)
    (g : Fin r) (x : Moments.Head (fun v : {v : Fin n // v∉H} => head v.val) g → Bool)
    (v : Fin n) (hv : v∉H) (hg : head v=g) :
    ambientAssignment H head g x v=x ⟨⟨v,hv⟩,hg⟩ := by
  simp only [ambientAssignment, dite_eq_left hv, dite_eq_left hg]

/-- The actual numeric candidate supplies a concrete ambient extension whose
selected word is exactly the saved representative payload. -/
theorem emitted_word {n r : ℕ}
    (H : Finset (Fin n)) (head : Fin n → Fin r) (g : Fin r) (p : ℕ → Bool)
    (hs : ∀ v : Fin n,v.val∈chosenIds p n ↔ ∃ _ : v∉H,head v=g)
    (candidate : Fin (2^(chosenIds p n).length)) :
    ExecCNFTupleEnumeration.fixedBits (chosenIds p n).length candidate.val=
      HighIncidenceProgram.Restriction.selected true
        (List.ofFn (fun v : Fin n => p v.val))
        (List.ofFn (ambientAssignment H head g
          ((freeAssignmentEquiv H (fun v => head v.val) g (chosenIds p n)
            (chosenIds_bound p n) (chosenIds_nodup p n) hs).symm
              (AttainedSignatures.assignmentEquiv (chosenIds p n).length candidate)))) :=
  (representative_selected_word H head g p hs candidate _
    (fun v hv hg => ambientAssignment_head H head g _ v hv hg)).symm

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleWords
end
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_QueryVisitorSemantics
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Concrete execution of the two representative passes. The saved frame
stack is traversed in place, and every semantic dictionary is the one written
by the actual arithmetic command. -/
noncomputable section
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorSemantics
open OAI BitProgram StructuredCalls OAI.Algorithms.SubexponentialSAT.SqrtLog
open SubexpSetupStorage LeafHeadSetupProgram
open SubexpLiftRing SubexpQuarticRing MomentsProgram TruncatedRingProgram
open QueryTupleState QueryTupleVisitor SignatureTupleProgram SignatureTupleSource


open scoped BigOperators

/-- The same physical representative word used by the key evaluator is the
selected ambient extension used by the first pass. -/
theorem representativeWord_selected_oai (s : ProducedSource) {d : ℕ}
    (q : LeafProgram.Factor.Spec s.input.r s.input.Q s.input.n d)
    (H : Finset (Fin s.input.n)) (owner : Fin q.ps.length → Fin s.input.n)
    (head : Fin s.input.Q → Fin s.input.n → Fin s.input.r)
    (facts : QueryVisitorHead.SourceFacts s.input q H owner s.owner head) (g : Fin s.input.r)
    (reps : ∀ k, Moments.Head (fun v : ResidualEmbedding.Free H => head s.input.node v.val) k → Bool) :
    QueryVisitorHead.representativeWord s.input q H owner s.owner head facts g reps=
      HighIncidenceProgram.Restriction.selected true (mask s (s.base+g.val))
        (List.ofFn (SignatureTupleWords.ambientAssignment H (head s.input.node) g (reps g))) := by
  let p := HeadIdentifierProgram.predicate s.input.rows s.input.low (s.base+g.val)
  let e := BucketTupleProgram.Concrete.freeAssignmentEquiv H
    (fun v : ResidualEmbedding.Free H => head s.input.node v.val) g
    (HeadIdentifierProgram.chosenIds p s.input.n)
    (HeadIdentifierProgram.chosenIds_bound p s.input.n)
    (HeadIdentifierProgram.chosenIds_nodup p s.input.n) (facts.selected g)
  let candidate := (AttainedSignatures.assignmentEquiv
    (HeadIdentifierProgram.chosenIds p s.input.n).length).symm (e (reps g))
  have hw := SignatureTupleWords.emitted_word H (head s.input.node) g p
    (facts.selected g) candidate
  have hbits := AttainedSignatures.assignment_word
    (HeadIdentifierProgram.chosenIds p s.input.n).length candidate
  have he : AttainedSignatures.assignmentEquiv _ candidate=e (reps g) :=
    Equiv.apply_symm_apply _ _
  rw [he] at hbits hw
  have he' : e.symm (e (reps g))=reps g := e.symm_apply_apply _
  change _=HighIncidenceProgram.Restriction.selected true (mask s (s.base+g.val))
    (List.ofFn (SignatureTupleWords.ambientAssignment H (head s.input.node) g (e.symm (e (reps g))))) at hw
  rw [he'] at hw
  exact hbits.trans hw


end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorSemantics
end
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorSemantics.representativeWord_selected_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorSemantics.representativeWord_selected_oai
