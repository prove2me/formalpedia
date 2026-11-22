-- Prove2me | solution 1 for MatchingLogic.Sorted.no_faithful_translation
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:46:00.679545+00:00
-- url     : https://prove2.me/submissions/ef238c5f-b8f0-40b1-8791-2ab5753b2c83

module
public import Definitions.Def_LeanPool_MatchingLogic_Sorted
public import Definitions.Def_LeanPool_MatchingLogic_ProofSystem
public import Definitions.Def_LeanPool_MatchingLogic_EntryPoints
public import Mathlib.Data.Set.Lattice
public import Mathlib.Data.Set.Lattice
public import Mathlib.Data.Set.Lattice.Image
public import Mathlib.Data.Set.Lattice
public import Mathlib.Data.Set.Lattice
public import Definitions.Def_LeanPool_MatchingLogic_SortedProof
public import Theorems.Thm_P2M_MatchingLogic_Sorted__3_not_derives__3_29a4e105aa74
public import Theorems.Thm_MatchingLogic_global_completeness_of_localCompleteness
public import Theorems.Thm_P2M_MatchingLogic_Sorted__3_entails__3_e3748dae8e29


set_option autoImplicit true
@[expose] public section
public section
open MatchingLogic
open MatchingLogic.Sorted
variable {S : MSignature} {Var : Type} [DecidableEq S.Srt] [DecidableEq Var]
namespace MatchingLogic.Sorted
theorem _root_.solution (hS : MSoundness S3 Var)
    (x y : Var) (hxy : x ≠ y) :
    ¬ ∃ (T : Signature) (tΓ : MPattern S3 Var Srt3.a → Pattern T Var)
        (tφ : MPattern S3 Var Srt3.c → Pattern T Var),
        StrongLocalCompleteness T Var ∧
        (∀ γ ∈ Γ3 (Var := Var) x y, Closed (tΓ γ)) ∧
        Closed (tφ (φ3 (Var := Var) x y)) ∧
        (MGlobalCons (Γ3 (Var := Var) x y) (φ3 (Var := Var) x y) →
          GlobalCons (tΓ '' Γ3 (Var := Var) x y) (tφ (φ3 (Var := Var) x y))) ∧
        (Provable (tΓ '' Γ3 (Var := Var) x y) (tφ (φ3 (Var := Var) x y)) →
          MProvable (Γ3 (Var := Var) x y) (φ3 (Var := Var) x y)) := by
  rintro ⟨T, tΓ, tφ, hL, hclosedΓ, hclosedφ, hpreserve, hreflect⟩
  apply Γ3_not_derives_φ3 hS x y hxy
  apply hreflect
  apply (global_completeness_of_localCompleteness hL ?_ hclosedφ).mp
  · exact hpreserve (Γ3_entails_φ3 x y hxy)
  · intro δ hδ
    rcases hδ with ⟨γ, hγ, rfl⟩
    exact hclosedΓ γ hγ
end MatchingLogic.Sorted
