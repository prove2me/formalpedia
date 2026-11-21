-- Prove2me | solution 1 for LeanModelChecking.LTL.toNNFCore_sound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T22:44:34.026523+00:00
-- url     : https://prove2.me/submissions/2c29dcdd-5ff6-4dc3-af34-5bc9f2a51151

module
public import Definitions.Def_LeanPool_LeanModelChecking_LTLNBWStatement
public import Aesop.BuiltinRules
public import Mathlib.Tactic.Finiteness.Attr
public import Mathlib.Tactic.Push
public import Definitions.Def_LeanPool_LeanModelChecking_LTLNNF
public import Theorems.Thm_LeanModelChecking_not_exists_until_iff_forall

set_option autoImplicit true
@[expose] public section
public section
open LeanModelChecking
open LeanModelChecking.LTL
namespace LeanModelChecking.LTL
theorem _root_.solution {AP} (f : LTL AP) :
    (∀ w, LTL.language f w ↔ NNF.language (toNNF f) w) ∧
      (∀ w, ¬ LTL.language f w ↔ NNF.language (toNNFNeg f) w) := by
  induction f with
  | atom p => simp [toNNF, toNNFNeg, toNNFCore, LTL.language, NNF.language]
  | not f ih =>
    refine ⟨?_, ?_⟩
    · simpa [toNNF, toNNFNeg, toNNFCore, LTL.language] using ih.2
    · simpa [toNNF, toNNFNeg, toNNFCore, LTL.language] using ih.1
  | or f g ihf ihg =>
    refine ⟨?_, ?_⟩
    · simp [toNNF, toNNFCore, LTL.language, NNF.language, ihf.1, ihg.1]
    · simp [toNNFNeg, toNNFCore, LTL.language, NNF.language, ihf.2, ihg.2]
  | next f ih =>
    refine ⟨?_, ?_⟩
    · simp [toNNF, toNNFCore, LTL.language, NNF.language, ih.1]
    · simp [toNNFNeg, toNNFCore, LTL.language, NNF.language, ih.2]
  | «until» f g ihf ihg =>
    refine ⟨?_, ?_⟩
    · simp [toNNF, toNNFCore, LTL.language, NNF.language, ihf.1, ihg.1]
    · intro w
      have hf : ∀ k,
          ¬ LTL.language f (fun j => w (j + k)) ↔
            NNF.language (toNNFNeg f) (fun j => w (j + k)) := by
        intro k
        simpa using ihf.2 (fun j => w (j + k))
      have hg : ∀ k,
          ¬ LTL.language g (fun j => w (j + k)) ↔
            NNF.language (toNNFNeg g) (fun j => w (j + k)) := by
        intro k
        simpa using ihg.2 (fun j => w (j + k))
      have hlogic :=
        not_exists_until_iff_forall
          (P := fun k => LTL.language f (fun j => w (j + k)))
          (Q := fun i => LTL.language g (fun j => w (j + i)))
      simp [toNNFNeg, toNNFCore, LTL.language, NNF.language, hf, hg, hlogic]
end LeanModelChecking.LTL
