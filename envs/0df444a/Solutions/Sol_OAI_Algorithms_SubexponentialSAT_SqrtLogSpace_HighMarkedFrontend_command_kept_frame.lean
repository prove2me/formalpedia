-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighMarkedFrontend.command_kept_frame
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T11:11:41.6908+00:00
-- url     : https://prove2.me/submissions/ac76efeb-0c89-4301-9192-f11154fe0980

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S186
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_HighMarkedFrontend_command_eval

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_HighMarkedCleanup
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
/-! Actual lower-workspace reclamation in the shared leaf ABI. Source masters,
collector, count and upper caller words are preserved by the paid cleanup. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighMarkedFrontend
open OAI BitProgram StructuredCalls
open OAI.Algorithms.SubexponentialSAT.SqrtLog

theorem result_upper_frame (a : Data) (b : LeafProgram.Query.Data) (i : Fin 896)
    (hi : (768 : ℕ) ≤ i.val) : (result a b).stacks i=a.stacks i := by
  apply embedState_stack_frame
  rintro ⟨j,hj⟩
  have hv := congrArg Fin.val hj
  change j.val=i.val at hv
  omega

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighMarkedFrontend
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_HighMarkedFrontend
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! The original actual marked-scope/high-mask/parameter frontend is lifted
into the shared leaf ABI. Upper caller words and the marked mass collector
are retained; the lower workspace is reclaimed by an actual cleanup program. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighMarkedFrontend

open OAI BitProgram StructuredCalls
open OAI.Algorithms.SubexponentialSAT.SqrtLog
open LeafParametersProgram

/-- The concrete return collector's retained words survive the actual
frontend result. This includes immutable sources and every caller bank. -/
theorem result_kept_frame (a : Data) (b : LeafProgram.Query.Data)
    (hframe : ∀ i : Fin 768, (i.val < 340 ∨ 680 ≤ i.val) →
      i≠134 → i≠141 → i≠338 → i≠704 → i≠718 → i≠719 → i≠705 → i≠706 → i≠699 →
      (∀ j,Exports.destination j≠i) → b.stacks i=a.stacks (stackMap i)) :
    ∀ i, HashMarkedReturn.kept i=true → (result a b).stacks i=a.stacks i := by
  intro i hk
  by_cases hi : i.val<768
  · let j : Fin 768 := ⟨i.val,hi⟩
    have hij : i=stackMap j := rfl
    have hv : j.val=320 ∨ j.val=322 ∨ j.val=700 ∨ j.val=701 ∨
        j.val=707 ∨ j.val=708 ∨ j.val=709 ∨ 744 ≤ j.val := by
      simp only [HashMarkedReturn.kept,decide_eq_true_eq,Fin.ext_iff,
        Fin.coe_ofNat_eq_mod] at hk
      dsimp [j]
      omega
    rw [hij,result_stack]
    apply hframe j (by omega)
    all_goals try (intro he; have hh := congrArg Fin.val he; norm_num at hh; omega)
    intro x he
    have hh := congrArg Fin.val he
    fin_cases x <;> norm_num [Exports.destination] at hh <;> omega
  · exact result_upper_frame a b i (by omega)

/-- Exact kept-word frame for any actual marked frontend execution, obtained
from its concrete evaluated output by deterministic execution uniqueness. -/
theorem command_kept_frame_oai (q : LeafQueryFrontend.Query) (k : ℕ) (a b : Data)
    (steps : ℕ) (hv : q.Valid) (hc : LeafProgram.Query.CleanWork (project a))
    (hs : LeafProgram.Query.Sources q (project a)) (hm : q.mark.isSome=true)
    (href : a.stacks 321=q.index.reverse) (he : Eval (command k) steps a b) :
    ∀ i, HashMarkedReturn.kept i=true → b.stacks i=a.stacks i := by
  obtain ⟨n,c,tau,l,w,hec,_,_,_,_,_,_,_,_,_,_,_,_,_,hf⟩ :=
    command_eval q k a hv hc hs hm href
  have hb := SubexpPrimeProgram.eval_result_unique he hec 321 338
  rw [hb]
  exact result_kept_frame a c hf

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighMarkedFrontend
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighMarkedFrontend.command_kept_frame_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighMarkedFrontend.command_kept_frame_oai
