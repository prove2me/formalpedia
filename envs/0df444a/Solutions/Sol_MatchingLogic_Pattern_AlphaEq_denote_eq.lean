-- Prove2me | solution 1 for MatchingLogic.Pattern.AlphaEq.denote_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:24:25.361585+00:00
-- url     : https://prove2.me/submissions/cdef0128-bc2b-4e9b-9257-82c37cf26d39

module
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_Fresh
public import Definitions.Def_LeanPool_MatchingLogic_ProofSystem
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_Alpha
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_LocalTheory
public import Definitions.Def_LeanPool_MatchingLogic_Soundness
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_CaptureAvoiding
public import Theorems.Thm_MatchingLogic_soundness


set_option autoImplicit true
@[expose] public section
public section
open MatchingLogic
variable {S : Signature}
open MatchingLogic.Pattern
open scoped BigOperators
open MatchingLogic.Pattern.AlphaEq
namespace MatchingLogic.Pattern.AlphaEq
theorem _root_.solution {p q : Pattern S Nat} (h : AlphaEq p q)
    (M : Model S) (rho : Nat → M.carrier) : M.denote rho p = M.denote rho q := by
  have hf : GlobalCons (∅ : Set (Pattern S Nat)) (.imp p q) :=
    soundness (∅ : Set (Pattern S Nat)) (.imp p q) (h.forward ∅)
  have hb : GlobalCons (∅ : Set (Pattern S Nat)) (.imp q p) :=
    soundness (∅ : Set (Pattern S Nat)) (.imp q p) (h.backward ∅)
  have hempty : M.SatSet (∅ : Set (Pattern S Nat)) := by
    intro gamma hgamma
    exact hgamma.elim
  have hfp := hf M hempty rho
  have hbp := hb M hempty rho
  apply Set.Subset.antisymm
  · intro u hu
    have hui : u ∈ M.denote rho (.imp p q) := by rw [hfp]; trivial
    change u ∈ (M.denote rho p)ᶜ ∪ M.denote rho q at hui
    rcases hui with hnp | hq
    · exact absurd hu hnp
    · exact hq
  · intro u hu
    have hui : u ∈ M.denote rho (.imp q p) := by rw [hbp]; trivial
    change u ∈ (M.denote rho q)ᶜ ∪ M.denote rho p at hui
    rcases hui with hnq | hp
    · exact absurd hu hnq
    · exact hp
end MatchingLogic.Pattern.AlphaEq
