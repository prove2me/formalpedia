-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorLoad.result_mask_count
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T09:55:56.387148+00:00
-- url     : https://prove2.me/submissions/204ce687-edd5-4f47-a2db-3f61f8e038f0

import Mathlib
import Definitions.Def_OAIQ081S179
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_QueryVisitorLoad_result_mask_word

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
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HighIncidenceProgramRestriction
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Physical merge of high and free Boolean assignments in original order.
This routine never renames a variable or drops an unused coordinate. -/
namespace SubexponentialSAT.SqrtLog.HighIncidenceProgram.Restriction
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls


theorem selected_true_length (mask xs : List Bool) (hlen : mask.length = xs.length) :
    (selected true mask xs).length = Subexp.PaddedCompletion.trueCount mask := by
  induction mask generalizing xs with
  | nil => simp [selected, Subexp.PaddedCompletion.trueCount, Subexp.PaddedCompletion.successful]
  | cons b mask ih =>
      cases xs with
      | nil => simp at hlen
      | cons x xs =>
          have ht : mask.length = xs.length := by simpa using hlen
          cases b <;> simp [selected, Subexp.PaddedCompletion.trueCount,
            Subexp.PaddedCompletion.successful] at * <;> exact ih xs ht

end SubexponentialSAT.SqrtLog.HighIncidenceProgram.Restriction

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

/-- The physical selected-mask population is the actual emitted head width. -/
theorem headOrder_highCount (p : ℕ → Bool) (n : ℕ) :
    Restriction.highCount (List.ofFn (fun v : Fin n => p v.val))=count p n := by
  have hh := Restriction.selected_true_length (List.ofFn (fun v : Fin n => p v.val))
    (List.ofFn (fun _ : Fin n => true)) (by simp)
  rw [selected_headOrder,List.length_ofFn] at hh
  exact hh.symm

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadRepresentativeSemantics
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_QueryVisitorLoad
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Paid reverse-head reload for the two-pass query visitor. The same native
run returns every integer row, preserves the suspended query data, and restores
a fixed retained word cap before the next head. -/

noncomputable section
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorLoad
open OAI BitProgram StructuredCalls OAI.Algorithms.SubexponentialSAT.SqrtLog
open LeafHeadSetupProgram OAI.Algorithms.SubexponentialSAT.SubexpSetupStorage

section Outputs
variable (s : Native.Inputs) (z : ℕ) (frame : State 40 896)
    (rp : Fin 8 → Bool) (rm : Fin 16 → Bool) (rs : Fin 8 → Bool)
    (raw : List (List LayoutMatrixProgram.Pair)) (shifted : List (List (List Bool)))

theorem result_mask_count_oai :
    HighIncidenceProgram.Restriction.highCount ((result s z frame rp rm rs raw shifted).stacks 670)=
      (selectedHeads s.n s.rows s.low z).length := by
  rw [result_mask_word]
  exact HeadRepresentativeSemantics.headOrder_highCount _ _

end Outputs

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorLoad
end
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorLoad.result_mask_count_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorLoad.result_mask_count_oai
