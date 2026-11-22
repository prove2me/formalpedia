-- Prove2me | solution 1 for MatchingLogic.Model.app_const
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:36:25.199943+00:00
-- url     : https://prove2.me/submissions/359e1520-ca5b-4943-a2af-3a24d9d72172

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
theorem _root_.solution (M : Model S) (σ : S.Sym) (h : S.arity σ = 0)
    (A : Fin (S.arity σ) → Set M.carrier) :
    M.app σ A = M.interp σ (fun i => absurd i.isLt (by omega)) := by
  ext u
  simp only [app, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨a, -, hu⟩
    have : a = fun i => absurd i.isLt (by omega : ¬ (i.val < S.arity σ)) := by
      funext i; exact absurd i.isLt (by omega)
    rwa [this] at hu
  · intro hu
    exact ⟨_, fun i => absurd i.isLt (by omega), hu⟩
end MatchingLogic.Model
