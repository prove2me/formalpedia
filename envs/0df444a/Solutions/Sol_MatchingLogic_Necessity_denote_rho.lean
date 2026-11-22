-- Prove2me | solution 1 for MatchingLogic.Necessity.denote_rho
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:34:22.558688+00:00
-- url     : https://prove2.me/submissions/a2eb1653-0f92-4158-980a-bcfdfc8078e3

module
public import Definitions.Def_LeanPool_MatchingLogic_Locality
public import Mathlib.Data.Set.Insert
public import Definitions.Def_LeanPool_MatchingLogic_Necessity
public import Theorems.Thm_MatchingLogic_denote_app
public import Theorems.Thm_MatchingLogic_denote_bot
public import Theorems.Thm_MatchingLogic_denote_ex
public import Theorems.Thm_MatchingLogic_denote_imp
public import Theorems.Thm_MatchingLogic_denote_var
attribute [local simp] MatchingLogic.denote_app
attribute [local simp] MatchingLogic.denote_bot
attribute [local simp] MatchingLogic.denote_ex
attribute [local simp] MatchingLogic.denote_imp
attribute [local simp] MatchingLogic.denote_var



set_option autoImplicit true
@[expose] public section
public section
open MatchingLogic
open MatchingLogic.Necessity
variable {Var : Type} [DecidableEq Var]
namespace MatchingLogic.Necessity
theorem _root_.solution (x : Var) : M.denote (rho (Var := Var)) (psi x) = {0} := by
  ext u
  simp only [psi, denote_app, Model.app, denote_var, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨a, ha, hu⟩
    have h0 : a 0 = 1 := ha 0
    simpa [h0] using hu
  · intro hu
    exact ⟨fun _ => 1, fun _ => rfl, by simpa using hu⟩
end MatchingLogic.Necessity
