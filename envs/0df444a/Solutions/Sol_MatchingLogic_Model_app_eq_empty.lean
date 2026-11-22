-- Prove2me | solution 1 for MatchingLogic.Model.app_eq_empty
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:22:11.986163+00:00
-- url     : https://prove2.me/submissions/51101f81-03da-4825-b808-0d1af228a7a7

module
public import Mathlib.Data.Set.Insert
public import Definitions.Def_LeanPool_MatchingLogic_Core
public import Mathlib.Data.Set.Basic
public import Definitions.Def_LeanPool_MatchingLogic_Sanity
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
open MatchingLogic.Model
variable {S : Signature}
namespace MatchingLogic.Model
theorem _root_.solution (M : Model S) (σ : S.Sym)
    (A : Fin (S.arity σ) → Set M.carrier) (i : Fin (S.arity σ)) (h : A i = ∅) :
    M.app σ A = ∅ := by
  ext u
  simp only [app, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
  rintro ⟨a, ha, -⟩
  have := ha i
  rw [h] at this
  exact this
end MatchingLogic.Model
