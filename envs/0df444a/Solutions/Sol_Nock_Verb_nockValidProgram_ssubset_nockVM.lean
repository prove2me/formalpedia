-- Prove2me | solution 1 for Nock.Verb.nockValidProgram_ssubset_nockVM
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:31:26.237836+00:00
-- url     : https://prove2.me/submissions/e6e8a669-2525-4c9b-bd2d-7054197e9485

module
public import Definitions.Def_LeanPool_PureNock_Verb
public import Batteries.Tactic.Alias
public import Definitions.Def_LeanPool_PureNock_Trace
public import Theorems.Thm_Nock_Verb_finite_of_valid
public import Theorems.Thm_Nock_Verb_finite_leaf

set_option autoImplicit true
@[expose] public section
public section
open Nock
open Nock.Verb
namespace Nock.Verb
theorem _root_.solution {Λ : Nat} (hΛ : 1 ≤ Λ) :
    SSubLang (NockValidProgramΛ Λ) (FiniteΛ Λ) := by
  refine ⟨?_, .leaf 0, ⟨finite_leaf 0, ?_⟩, ?_⟩
  · intro F hF
    exact ⟨finite_of_valid hF.2, hF.1.2⟩
  · show size (.leaf 0) ≤ Λ
    simpa [size, leaves] using hΛ
  · rintro ⟨⟨⟨s, f, hEq, _, _⟩, _⟩, _⟩
    simp at hEq
end Nock.Verb
