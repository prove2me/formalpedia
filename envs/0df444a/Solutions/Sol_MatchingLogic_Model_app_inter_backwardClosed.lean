-- Prove2me | solution 1 for MatchingLogic.Model.app_inter_backwardClosed
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:21:31.109667+00:00
-- url     : https://prove2.me/submissions/144ebf49-8aa4-45bc-bd09-e17b90896c4a

module
public import Definitions.Def_LeanPool_MatchingLogic_Core
public import Mathlib.Data.Set.Insert
public import Definitions.Def_LeanPool_MatchingLogic_Locality
public import Theorems.Thm_MatchingLogic_Model_BackwardClosed_mem_of_interp
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
variable {S : Signature} {Var : Type} [DecidableEq Var]
namespace MatchingLogic
namespace Model
theorem _root_.solution {M : Model S} {C : Set M.carrier}
    (hC : M.BackwardClosed C) (σ : S.Sym) (A : Fin (S.arity σ) → Set M.carrier) :
    M.app σ A ∩ C = M.app σ (fun i => A i ∩ C) ∩ C := by
  ext u
  simp only [Model.app, Set.mem_inter_iff, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨⟨a, ha, hu⟩, huC⟩
    exact ⟨⟨a, fun i => ⟨ha i, Model.BackwardClosed.mem_of_interp M hC huC hu i⟩, hu⟩, huC⟩
  · rintro ⟨⟨a, ha, hu⟩, huC⟩
    exact ⟨⟨a, fun i => (ha i).1, hu⟩, huC⟩
end Model
end MatchingLogic
