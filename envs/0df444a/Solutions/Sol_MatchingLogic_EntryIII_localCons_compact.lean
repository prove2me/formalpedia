-- Prove2me | solution 1 for MatchingLogic.EntryIII.localCons_compact
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:30:17.930468+00:00
-- url     : https://prove2.me/submissions/19760926-9e04-4a60-8531-b78f92be8ca7

module
public import Definitions.Def_LeanPool_MatchingLogic_Semantics
public import Mathlib.ModelTheory.Satisfiability
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_Compactness
public import Theorems.Thm_MatchingLogic_EntryIII_localCons_iff_not_counterTheory_isSatisfiable
public import Theorems.Thm_MatchingLogic_FV_app
public import Theorems.Thm_MatchingLogic_FV_bot
public import Theorems.Thm_MatchingLogic_FV_ex
public import Theorems.Thm_MatchingLogic_FV_imp
public import Theorems.Thm_MatchingLogic_FV_var
public import Theorems.Thm_MatchingLogic_denote_app
public import Theorems.Thm_MatchingLogic_denote_bot
public import Theorems.Thm_MatchingLogic_denote_ex
public import Theorems.Thm_MatchingLogic_denote_imp
public import Theorems.Thm_MatchingLogic_denote_var
attribute [local simp] MatchingLogic.FV_app
attribute [local simp] MatchingLogic.FV_bot
attribute [local simp] MatchingLogic.FV_ex
attribute [local simp] MatchingLogic.FV_imp
attribute [local simp] MatchingLogic.FV_var
attribute [local simp] MatchingLogic.denote_app
attribute [local simp] MatchingLogic.denote_bot
attribute [local simp] MatchingLogic.denote_ex
attribute [local simp] MatchingLogic.denote_imp
attribute [local simp] MatchingLogic.denote_var



set_option autoImplicit true
@[expose] public section
public section
open MatchingLogic MatchingLogic.EntryIII
open FirstOrder
universe u
variable {S : Signature} {Var : Type} [DecidableEq Var]
namespace MatchingLogic.EntryIII
theorem _root_.solution {Delta : Set (Pattern S Var)} {phi : Pattern S Var}
    (hlocal : LocalCons Delta phi) :
    ∃ l : List (Pattern S Var),
      (∀ delta ∈ l, delta ∈ Delta) ∧
        LocalCons {delta | delta ∈ l} phi := by
  classical
  let Piece : Option {delta // delta ∈ Delta} →
      (relLanguage S)[[Option Var]].Theory
    | none => {(MatchingLogic.EntryIII.Pattern.toFOSentence phi).not}
    | some delta => {MatchingLogic.EntryIII.Pattern.toFOSentence delta.1}
  have hcounter : counterTheory Delta phi = ⋃ i, Piece i := by
    ext theta
    constructor
    · intro htheta
      rcases htheta with htheta | htheta
      · rcases htheta with ⟨delta, hdelta, rfl⟩
        apply Set.mem_iUnion.mpr
        refine ⟨some ⟨delta, hdelta⟩, ?_⟩
        simp [Piece]
      · apply Set.mem_iUnion.mpr
        refine ⟨none, ?_⟩
        simpa [Piece] using htheta
    · intro htheta
      rcases Set.mem_iUnion.mp htheta with ⟨i, hi⟩
      cases i with
      | none =>
          exact Set.mem_union_right _ (by simpa [Piece] using hi)
      | some delta =>
          apply Set.mem_union_left
          have heq : theta = MatchingLogic.EntryIII.Pattern.toFOSentence delta.1 := by
            simpa [Piece] using hi
          exact ⟨delta.1, delta.2, heq.symm⟩
  have hUnionUnsat : ¬ FirstOrder.Language.Theory.IsSatisfiable (⋃ i, Piece i) := by
    rw [← hcounter]
    exact (localCons_iff_not_counterTheory_isSatisfiable.mp hlocal)
  have hNotAll :
      ¬ ∀ s : Finset (Option {delta // delta ∈ Delta}),
        FirstOrder.Language.Theory.IsSatisfiable (⋃ i ∈ s, Piece i) := by
    intro hall
    exact hUnionUnsat
      ((FirstOrder.Language.Theory.isSatisfiable_iUnion_iff_isSatisfiable_iUnion_finset Piece).mpr
        hall)
  push Not at hNotAll
  obtain ⟨s, hs⟩ := hNotAll
  let l : List (Pattern S Var) :=
    s.toList.filterMap (fun
      | none => none
      | some delta => some delta.1)
  refine ⟨l, ?_, ?_⟩
  · intro delta hdelta
    simp only [l, List.mem_filterMap] at hdelta
    obtain ⟨i, hi, himap⟩ := hdelta
    cases i with
    | none => simp at himap
    | some d =>
        simp only [Option.some.injEq] at himap
        subst delta
        exact d.2
  · apply localCons_iff_not_counterTheory_isSatisfiable.mpr
    intro hbig
    apply hs
    apply hbig.mono
    intro theta htheta
    rcases Set.mem_iUnion.mp htheta with ⟨i, htheta⟩
    rcases Set.mem_iUnion.mp htheta with ⟨hi, hpiece⟩
    cases i with
    | none =>
        exact Set.mem_union_right _ (by simpa [Piece] using hpiece)
    | some d =>
        apply Set.mem_union_left
        have hdlist : d.1 ∈ l := by
          simp only [l, List.mem_filterMap]
          exact ⟨some d, by simpa using hi, rfl⟩
        have heq : theta = MatchingLogic.EntryIII.Pattern.toFOSentence d.1 := by
          simpa [Piece] using hpiece
        exact ⟨d.1, hdlist, heq.symm⟩
end MatchingLogic.EntryIII
