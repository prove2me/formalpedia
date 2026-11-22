-- Prove2me | solution 1 for MatchingLogic.locality
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:22:11.354964+00:00
-- url     : https://prove2.me/submissions/1c75abd7-0719-4622-9841-34bf7c7dbe38

module
public import Definitions.Def_LeanPool_MatchingLogic_Core
public import Mathlib.Data.Set.Insert
public import Definitions.Def_LeanPool_MatchingLogic_Locality
public import Theorems.Thm_MatchingLogic_Model_app_inter_backwardClosed
public import Theorems.Thm_MatchingLogic_AgreeOn_update
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
theorem _root_.solution (M : Model S) {C : Set M.carrier} (hC : M.BackwardClosed C)
    (ψ : Pattern S Var) (ρ ρ' : Var → M.carrier) (h : AgreeOn C ρ ρ') :
    M.denote ρ ψ ∩ C = M.denote ρ' ψ ∩ C := by
  induction ψ generalizing ρ ρ' with
  | var x =>
    simp only [denote_var]
    rcases h x with ⟨heq, _⟩ | ⟨hxC, hxC'⟩
    · rw [heq]
    · ext u
      simp only [Set.mem_inter_iff, Set.mem_singleton_iff]
      constructor
      · rintro ⟨rfl, hu⟩; exact absurd hu hxC
      · rintro ⟨rfl, hu⟩; exact absurd hu hxC'
  | bot => simp
  | app σ f ih =>
    simp only [denote_app]
    rw [Model.app_inter_backwardClosed hC σ (fun i => M.denote ρ (f i)),
        Model.app_inter_backwardClosed hC σ (fun i => M.denote ρ' (f i))]
    congr 2
    funext i
    exact ih i ρ ρ' h
  | imp φ ψ ihφ ihψ =>
    ext u
    simp only [denote_imp, Set.mem_inter_iff, Set.mem_union, Set.mem_compl_iff]
    constructor
    · rintro ⟨hu, huC⟩
      refine ⟨?_, huC⟩
      rcases hu with hu | hu
      · left
        intro hφ'
        apply hu
        have hmem : u ∈ M.denote ρ' φ ∩ C := ⟨hφ', huC⟩
        rw [← ihφ ρ ρ' h] at hmem
        exact hmem.1
      · right
        have hmem : u ∈ M.denote ρ ψ ∩ C := ⟨hu, huC⟩
        rw [ihψ ρ ρ' h] at hmem
        exact hmem.1
    · rintro ⟨hu, huC⟩
      refine ⟨?_, huC⟩
      rcases hu with hu | hu
      · left
        intro hφ
        apply hu
        have hmem : u ∈ M.denote ρ φ ∩ C := ⟨hφ, huC⟩
        rw [ihφ ρ ρ' h] at hmem
        exact hmem.1
      · right
        have hmem : u ∈ M.denote ρ' ψ ∩ C := ⟨hu, huC⟩
        rw [← ihψ ρ ρ' h] at hmem
        exact hmem.1
  | ex x φ ih =>
    ext u
    simp only [denote_ex, Set.mem_inter_iff, Set.mem_iUnion]
    constructor
    · rintro ⟨⟨a, ha⟩, huC⟩
      refine ⟨⟨a, ?_⟩, huC⟩
      have hmem : u ∈ M.denote (Function.update ρ x a) φ ∩ C := ⟨ha, huC⟩
      rw [ih (Function.update ρ x a) (Function.update ρ' x a) (h.update x a)] at hmem
      exact hmem.1
    · rintro ⟨⟨a, ha⟩, huC⟩
      refine ⟨⟨a, ?_⟩, huC⟩
      have hmem : u ∈ M.denote (Function.update ρ' x a) φ ∩ C := ⟨ha, huC⟩
      rw [← ih (Function.update ρ x a) (Function.update ρ' x a) (h.update x a)] at hmem
      exact hmem.1
end MatchingLogic
