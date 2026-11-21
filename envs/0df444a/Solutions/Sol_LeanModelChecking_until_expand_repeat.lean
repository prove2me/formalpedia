-- Prove2me | solution 1 for LeanModelChecking.until_expand_repeat
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T22:46:05.135241+00:00
-- url     : https://prove2.me/submissions/9f558bb3-fc38-4be4-abe7-12a88dc255a7

module
public import Definitions.Def_LeanPool_LeanModelChecking_LTLNNF
public import Definitions.Def_LeanPool_LeanModelChecking_ABW
public import Mathlib.Order.Lattice.Nat
public import Mathlib.Tactic.Continuity
public import Mathlib.Topology.Instances.Discrete
public import Mathlib.Topology.Order.MonotoneConvergence
public import Definitions.Def_LeanPool_LeanModelChecking_NNFABW

set_option autoImplicit true
@[expose] public section
public section
open LeanModelChecking
namespace LeanModelChecking
theorem _root_.solution {AP} (f g : NNF AP) : ∀ w, (f.until g).language w
    ↔ ∃ n, (NNF.repeatAndNext f g n).language w := by
  intros w
  constructor
  · simp only [NNF.language, forall_exists_index, and_imp]
    intros n hg hf
    exists n
    revert w
    induction n
    · simp [NNF.repeatAndNext]
    next n ih =>
      simp only [NNF.repeatAndNext, NNF.language]
      intros w hg hf
      refine ⟨hf 0 (by omega), ?_⟩
      apply ih
      · exact hg
      · intros k hk
        exact hf (k + 1) (by omega)
  · simp only [NNF.language, forall_exists_index]
    intros n h
    exists n
    revert w
    induction n
    · simp [NNF.repeatAndNext]
    next n ih =>
      simp only [NNF.repeatAndNext, NNF.language, and_imp]
      intros w hf0 h
      obtain ⟨hg, hf⟩ := ih (fun j => w (j + 1)) h
      refine ⟨hg, ?_⟩
      intros k hk
      cases k with
      | zero => exact hf0
      | succ k => apply hf k; omega
end LeanModelChecking
