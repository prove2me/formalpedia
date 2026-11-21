-- Prove2me | solution 1 for LeanModelChecking.release_expand
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T22:46:04.607953+00:00
-- url     : https://prove2.me/submissions/1b492dda-75cd-47bf-b0e9-c9847e7f9f0c

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
theorem _root_.solution {AP} (f g : NNF AP) :
    (f.release g).language = (g.and (f.or (f.release g).next)).language := by
  funext w; apply propext
  constructor
  · simp only [NNF.language]
    intros H
    rcases H 0 with lg0|⟨_, _⟩
    · refine ⟨lg0, ?_⟩
      by_cases hf : f.language w
      · left; exact hf
      · right
        intros i
        rcases H (i + 1) with lgi1|⟨k, hk, H⟩
        · left; exact lgi1
        · right
          cases k with
          | zero => contradiction
          | succ k => exists k, (by omega)
    · exfalso; omega
  · simp only [NNF.language, and_imp]
    rintro lg H (_|i)
    · left; assumption
    · rcases H with H|H
      · right; exists 0; grind
      · specialize H i
        rcases H with _|⟨k, _, _⟩
        · left; assumption
        · right; exists k + 1, (by omega)
end LeanModelChecking
