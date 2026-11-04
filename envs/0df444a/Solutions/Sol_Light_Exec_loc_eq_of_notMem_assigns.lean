-- Prove2me | solution 1 for Light.Exec.loc_eq_of_notMem_assigns
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:26:01.637682+00:00
-- url     : https://prove2.me/submissions/90f6a601-eabf-42bb-8719-acd71fcecfe8

module
public import Definitions.Def_Submission_ThreeSumApsp_Lang_Logic
public import Definitions.Def_Submission_ThreeSumApsp_Lang_Assigns
public import Theorems.Thm_Light_Ends_call
public import Theorems.Thm_Light_Ends_set
public import Theorems.Thm_Light_Ends_skip
public import Theorems.Thm_Light_Ends_store
public import Theorems.Thm_Light_toNat_natCast_add_natCast
attribute [local simp] Light.toNat_natCast_add_natCast



set_option autoImplicit false
public section
open Light
variable {lim : Limits} {P : Program} {d : ℕ}
namespace Light
namespace Exec
theorem _root_.solution {s : Stmt} {σ σ' : State} {c y : ℕ}
    (h : Exec lim P d s σ σ' c) (hy : y ∉ s.assigns) : σ'.loc y = σ.loc y := by
  induction h with
  | skip => rfl
  | set _ => exact Function.update_of_ne (by simpa using hy) _ _
  | store _ _ _ => rfl
  | seq _ _ ih₁ ih₂ =>
    exact (ih₂ fun h => hy (List.mem_append_right _ h)).trans
      (ih₁ fun h => hy (List.mem_append_left _ h))
  | iteTrue _ _ _ ih => exact ih fun h => hy (List.mem_append_left _ h)
  | iteFalse _ _ _ ih => exact ih fun h => hy (List.mem_append_right _ h)
  | whileFalse _ _ => rfl
  | whileTrue _ _ _ _ ih₁ ih₂ => exact (ih₂ hy).trans (ih₁ hy)
  | call _ _ _ _ _ => exact Function.update_of_ne (by simpa using hy) _ _
end Exec
end Light
