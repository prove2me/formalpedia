-- Prove2me | solution 1 for MatchingLogic.Pattern.freshTuple_not_mem_component_allVars
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:33:18.397675+00:00
-- url     : https://prove2.me/submissions/4f764218-2ed1-4239-bac4-3348d761ef4f

module
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_CanonicalCore
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_MCSAlpha
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_CanonicalExistence
public import Theorems.Thm_MatchingLogic_CanonicalCarrier_coe_mk
public import Theorems.Thm_MatchingLogic_FV_app
public import Theorems.Thm_MatchingLogic_FV_bot
public import Theorems.Thm_MatchingLogic_FV_box
public import Theorems.Thm_MatchingLogic_FV_boxes
public import Theorems.Thm_MatchingLogic_FV_dia
public import Theorems.Thm_MatchingLogic_FV_ex
public import Theorems.Thm_MatchingLogic_FV_imp
public import Theorems.Thm_MatchingLogic_FV_var
public import Theorems.Thm_MatchingLogic_Model_reachWord_cons
public import Theorems.Thm_MatchingLogic_Model_reachWord_nil
public import Theorems.Thm_MatchingLogic_boxes_cons
public import Theorems.Thm_MatchingLogic_boxes_nil
public import Theorems.Thm_MatchingLogic_canonicalModel_interp
public import Theorems.Thm_MatchingLogic_denote_app
public import Theorems.Thm_MatchingLogic_denote_bot
public import Theorems.Thm_MatchingLogic_denote_ex
public import Theorems.Thm_MatchingLogic_denote_imp
public import Theorems.Thm_MatchingLogic_denote_var
public import Theorems.Thm_MatchingLogic_mem_canonicalInterp
attribute [local simp] MatchingLogic.CanonicalCarrier.coe_mk
attribute [local simp] MatchingLogic.FV_app
attribute [local simp] MatchingLogic.FV_bot
attribute [local simp] MatchingLogic.FV_box
attribute [local simp] MatchingLogic.FV_boxes
attribute [local simp] MatchingLogic.FV_dia
attribute [local simp] MatchingLogic.FV_ex
attribute [local simp] MatchingLogic.FV_imp
attribute [local simp] MatchingLogic.FV_var
attribute [local simp] MatchingLogic.Model.reachWord_cons
attribute [local simp] MatchingLogic.Model.reachWord_nil
attribute [local simp] MatchingLogic.boxes_cons
attribute [local simp] MatchingLogic.boxes_nil
attribute [local simp] MatchingLogic.canonicalModel_interp
attribute [local simp] MatchingLogic.denote_app
attribute [local simp] MatchingLogic.denote_bot
attribute [local simp] MatchingLogic.denote_ex
attribute [local simp] MatchingLogic.denote_imp
attribute [local simp] MatchingLogic.denote_var
attribute [local simp] MatchingLogic.mem_canonicalInterp


section
@[expose] public section
namespace MatchingLogic
open Set
variable {S : Signature}
noncomputable section
namespace Pattern
private theorem le_tupleFreshBase {n : Nat} {p : Pattern S Nat} {Phi : Fin n → Pattern S Nat}
    {z : Nat} (hz : z ∈ tupleAllVars p Phi) : z ≤ tupleFreshBase p Phi := by
  exact Finset.le_max' (insert 0 (tupleAllVars p Phi)) z (Finset.mem_insert_of_mem hz)
end Pattern
namespace NaryStageSystem
variable {sigma : S.Sym} {Gamma : CanonicalCarrier S}
  {phi : Fin (S.arity sigma) → Pattern S Nat} {enum : Nat → Pattern S Nat}
  (T : NaryStageSystem sigma Gamma phi enum)
end NaryStageSystem
end
end MatchingLogic
end
end

set_option autoImplicit true
@[expose] public section
public section
open MatchingLogic
open Set
variable {S : Signature}
noncomputable section
open MatchingLogic.Pattern
namespace MatchingLogic.Pattern
theorem _root_.solution (p : Pattern S Nat)
    (Phi : Fin n → Pattern S Nat) (i j : Fin n) : freshTuple p Phi i ∉ (Phi j).allVars := by
  intro hi
  have hsupport : freshTuple p Phi i ∈ tupleAllVars p Phi := by
    apply Finset.mem_union_right
    exact Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ _, hi⟩
  have hle := le_tupleFreshBase (p := p) (Phi := Phi) hsupport
  dsimp [freshTuple] at hle
  omega
end MatchingLogic.Pattern
