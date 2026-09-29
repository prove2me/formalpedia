-- Prove2me | solution 1 for MarkovMixing.projection_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @allychan327
-- created : 2026-08-22T04:18:09.184543+00:00
-- url     : https://prove2.me/submissions/a4df092f-c8a2-4875-8ff2-bb8bb1005a29

import Definitions.Def_mm_lower
import Mathlib.Tactic.Linarith

open scoped BigOperators
open MarkovMixing

theorem solution {V : Type*} [Fintype V] [DecidableEq V]
    {Λ : Type*} [Fintype Λ] [DecidableEq Λ]
    (μ ν : V → ℝ) (hμ : IsDist μ) (hν : IsDist ν) (f : V → Λ) :
    tvDist (pushforward μ f) (pushforward ν f) ≤ tvDist μ ν := by
  classical
  have hbdd : BddAbove (Set.range fun A : Finset V => |∑ x ∈ A, μ x - ∑ x ∈ A, ν x|) :=
    Set.Finite.bddAbove
      (Set.range fun A : Finset V => |∑ x ∈ A, μ x - ∑ x ∈ A, ν x|).toFinite
  -- the pushforward mass of a set is the mass of its preimage
  have hpre : ∀ (ρ : V → ℝ) (B : Finset Λ),
      ∑ b ∈ B, pushforward ρ f b
        = ∑ a ∈ Finset.univ.filter (fun a : V => f a ∈ B), ρ a := by
    intro ρ B
    have hstep : ∀ b : Λ, pushforward ρ f b = ∑ a, (if f a = b then ρ a else 0) := by
      intro b
      show ∑ a ∈ Finset.univ.filter (fun a : V => f a = b), ρ a = _
      rw [Finset.sum_filter]
    rw [Finset.sum_congr rfl fun b _ => hstep b, Finset.sum_comm]
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun a _ => ?_
    exact Finset.sum_ite_eq B (f a) (fun _ => ρ a)
  refine ciSup_le fun B => ?_
  rw [hpre μ B, hpre ν B]
  exact le_ciSup hbdd (Finset.univ.filter (fun a : V => f a ∈ B))
