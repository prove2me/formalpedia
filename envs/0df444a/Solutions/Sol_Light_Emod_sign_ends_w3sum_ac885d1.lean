-- Prove2me | solution 1 for Light.Emod.sign_ends_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:07:05.318831+00:00
-- url     : https://prove2.me/submissions/df8e8c09-0c86-4642-bd43-3350b8fdd2bf

import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_Seg
import Definitions.Def_Submission_ThreeSumApsp_Lang_Tactics
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Size
import Mathlib.Tactic.NormNum
import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_Emod
import Definitions.Def_WeightedCache3SUM_Alias_f18de37faf5b162f
import Theorems.Thm_Light_Ends_iteLast
import Theorems.Thm_Light_Ends_setTo
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
variable {lim : Limits} {P : Program} {d : ℕ}
open Light.Emod
variable {μ : ℕ → ℤ} {x : ℤ} {Mo V fr a : ℕ}
namespace Light.Emod
theorem _root_.solution (F : Pre lim Mo V fr) (hax : (a : ℤ) = |x|) {μ' : ℕ → ℤ} {t : ℤ} :
    Ends lim P d emodSign ⟨frame [x, Mo, fr, (a % Mo : ℕ), 0, t], μ'⟩ 12 fun σ' =>
      σ'.loc 0 = x % (Mo : ℤ) ∧ σ'.mem = μ' := by
  have hword := F.word
  have hr : a % Mo < Mo := Nat.mod_lt _ F.mod_pos
  generalize hrem : a % Mo = r at hr
  refine Ends.iteLast (fun hneg => ?_) (fun hpos => ?_)
  · have hneg : x < 0 := by simpa using hneg
    have hmod := neg_emod_nat a Mo F.mod_pos
    rw [hrem, show -(a : ℤ) = x by rw [hax, abs_of_neg hneg]; ring] at hmod
    refine Ends.iteLast (fun hz => ?_) (fun hz => ?_)
    · have hz : r = 0 := by simpa using hz
      exact Ends.setTo 0 ⟨by rw [hmod, if_pos hz]; rfl, rfl⟩
    · have hz : ¬ r = 0 := by simpa using hz
      exact Ends.setTo ((Mo : ℤ) - r) ⟨by rw [hmod, if_neg hz]; rfl, rfl⟩
  · have hpos : 0 ≤ x := by simpa using hpos
    refine Ends.setTo (r : ℤ) ⟨?_, rfl⟩
    rw [← abs_of_nonneg hpos, ← hax, ← hrem]
    exact (Int.natCast_mod a Mo)
end Light.Emod
