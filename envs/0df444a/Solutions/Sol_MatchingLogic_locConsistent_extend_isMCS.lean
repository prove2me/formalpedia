-- Prove2me | solution 1 for MatchingLogic.locConsistent_extend_isMCS
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:22:59.07256+00:00
-- url     : https://prove2.me/submissions/44f2b3e1-c331-41f2-a729-488c02556586

module
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_LocalTheory
public import Mathlib.Order.Zorn
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_Lindenbaum
public import Theorems.Thm_MatchingLogic_FV_app
public import Theorems.Thm_MatchingLogic_FV_bot
public import Theorems.Thm_MatchingLogic_FV_box
public import Theorems.Thm_MatchingLogic_FV_boxes
public import Theorems.Thm_MatchingLogic_FV_dia
public import Theorems.Thm_MatchingLogic_FV_ex
public import Theorems.Thm_MatchingLogic_FV_imp
public import Theorems.Thm_MatchingLogic_FV_var
public import Theorems.Thm_MatchingLogic_LocProvable_mp
public import Theorems.Thm_MatchingLogic_Model_reachWord_cons
public import Theorems.Thm_MatchingLogic_Model_reachWord_nil
public import Theorems.Thm_MatchingLogic_boxes_cons
public import Theorems.Thm_MatchingLogic_boxes_nil
public import Theorems.Thm_MatchingLogic_denote_app
public import Theorems.Thm_MatchingLogic_denote_bot
public import Theorems.Thm_MatchingLogic_denote_ex
public import Theorems.Thm_MatchingLogic_denote_imp
public import Theorems.Thm_MatchingLogic_denote_var
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
attribute [local simp] MatchingLogic.denote_app
attribute [local simp] MatchingLogic.denote_bot
attribute [local simp] MatchingLogic.denote_ex
attribute [local simp] MatchingLogic.denote_imp
attribute [local simp] MatchingLogic.denote_var


section
@[expose] public section
namespace MatchingLogic
open Set
variable {S : Signature} {Var : Type} [DecidableEq Var]
omit [DecidableEq Var] in
private theorem chain_covers_list
    {c : Set (Set (Pattern S Var))}
    (hc : IsChain (· ⊆ ·) c) (hne : c.Nonempty)
    (l : List (Pattern S Var)) (hl : ∀ phi ∈ l, phi ∈ ⋃₀ c) :
    ∃ Delta ∈ c, ∀ phi ∈ l, phi ∈ Delta := by
  induction l with
  | nil =>
      rcases hne with ⟨Delta, hDelta⟩
      exact ⟨Delta, hDelta, by simp⟩
  | cons phi l ih =>
      obtain ⟨D, hDc, hphiD⟩ := Set.mem_sUnion.mp (hl phi (by simp))
      obtain ⟨E, hEc, hE⟩ := ih (by
        intro psi hpsi
        exact hl psi (by simp [hpsi]))
      rcases hc.total hDc hEc with hDE | hED
      · refine ⟨E, hEc, ?_⟩
        intro psi hpsi
        rcases List.mem_cons.mp hpsi with rfl | hpsi
        · exact hDE hphiD
        · exact hE psi hpsi
      · refine ⟨D, hDc, ?_⟩
        intro psi hpsi
        rcases List.mem_cons.mp hpsi with rfl | hpsi
        · exact hphiD
        · exact hED (hE psi hpsi)
private theorem chain_sUnion_locConsistent
    {Gamma : Set (Pattern S Var)} {c : Set (Set (Pattern S Var))}
    (hcandidates : ∀ Delta ∈ c, Gamma ⊆ Delta ∧ LocConsistent Delta)
    (hchain : IsChain (· ⊆ ·) c) (hne : c.Nonempty) :
    LocConsistent (⋃₀ c) := by
  intro hbot
  rcases hbot with ⟨l, hl, hp⟩
  obtain ⟨Delta, hDelta, hcover⟩ := chain_covers_list hchain hne l hl
  exact (hcandidates Delta hDelta).2 ⟨l, hcover, hp⟩
end MatchingLogic
end
end

set_option autoImplicit true
@[expose] public section
public section
open MatchingLogic
open Set
variable {S : Signature} {Var : Type} [DecidableEq Var]
namespace MatchingLogic
theorem _root_.solution {Gamma : Set (Pattern S Var)}
    (hGamma : LocConsistent Gamma) :
    ∃ Delta : Set (Pattern S Var), Gamma ⊆ Delta ∧ IsMCS Delta := by
  let candidates : Set (Set (Pattern S Var)) :=
    { Delta | Gamma ⊆ Delta ∧ LocConsistent Delta }
  obtain ⟨Delta, hGammaDelta, hmax⟩ := zorn_subset_nonempty candidates (by
    intro c hc hchain hne
    refine ⟨⋃₀ c, ?_, fun D hD => Set.subset_sUnion_of_mem hD⟩
    constructor
    · rcases hne with ⟨D, hDc⟩
      exact (hc hDc).1.trans (Set.subset_sUnion_of_mem hDc)
    · exact chain_sUnion_locConsistent hc hchain hne) Gamma ⟨Set.Subset.rfl, hGamma⟩
  refine ⟨Delta, hGammaDelta, hmax.1.2, ?_⟩
  intro Theta hstrict hTheta
  have hcandidate : Theta ∈ candidates := ⟨hmax.1.1.trans hstrict.1, hTheta⟩
  exact hstrict.2 (hmax.2 hcandidate hstrict.1)
end MatchingLogic
