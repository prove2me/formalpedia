-- Prove2me | solution 1 for Light.sort_meets_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:27:11.074432+00:00
-- url     : https://prove2.me/submissions/de9da50d-1a64-49b0-9779-9a1079f72a46

import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_Copy
import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_Logs
import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_Merge
import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_MergeSort
import Definitions.Def_WeightedCache3SUM_Alias_d487fa3032c05613
import Theorems.Thm_Light_Meets_of_body
import Theorems.Thm_Light_sameFrame_cons_cons
import Theorems.Thm_Light_sameFrame_cons_nil
import Theorems.Thm_Light_sameFrame_nil
import Theorems.Thm_Light_sameFrame_nil_cons
import Theorems.Thm_Light_toNat_natCast_add_natCast
attribute [local simp] Light.sameFrame_cons_cons
attribute [local simp] Light.sameFrame_cons_nil
attribute [local simp] Light.sameFrame_nil
attribute [local simp] Light.sameFrame_nil_cons
attribute [local simp] Light.toNat_natCast_add_natCast



set_option autoImplicit false
section
open Light
variable {lim : Limits} {P : Program}
open Light.MergeSort
variable {pSort pHalf pMerge pCopy : ℕ}
namespace Light.MergeSort
namespace _root_.Light
theorem _root_.solution (C : Procs P pSort pHalf pMerge pCopy)
    (hw : (lim.space : ℤ) ≤ lim.word) (h1 : (1 : ℤ) ≤ lim.word) {a fr : ℕ} {L : List ℤ} {μ : ℕ → ℤ}
    (hseg : Seg μ a L) (haf : a + L.length ≤ fr) (hfr : fr + L.length ≤ lim.space) :
    ∀ d, d + Nat.clog 2 L.length + 1 ≤ lim.depth →
      Meets lim P pSort d [L.length, a, fr] μ (sortTime L.length) fun _ => Sorted μ a fr L := by
  induction hn : L.length using Nat.strong_induction_on generalizing a L μ with
  | _ n ih =>
    subst hn
    intro d hd
    refine Meets.of_body C.sort (body_ends C hw h1 hseg haf hfr (by omega)
      fun a' L' μ' hn hhalf hseg' haf' =>
        ih L'.length (by omega) hseg' haf' (by omega) rfl (d + 1) ?_)
    -- one level of calls fewer for half the length
    have hclog : Nat.clog 2 L.length = Nat.clog 2 ((L.length + 1) / 2) + 1 := by
      simpa using Nat.clog_of_two_le (b := 2) (by norm_num) hn
    have := Nat.clog_mono_right 2 (by omega : L'.length ≤ (L.length + 1) / 2)
    omega
end _root_.Light
end Light.MergeSort
