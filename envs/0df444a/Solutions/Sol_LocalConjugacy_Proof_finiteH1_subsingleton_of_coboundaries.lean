-- Prove2me | solution 1 for LocalConjugacy.Proof.finiteH1_subsingleton_of_coboundaries
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T17:14:25.40633+00:00
-- url     : https://prove2.me/submissions/feafc333-afab-41ae-a3f4-c71285a4ab45

import Mathlib
import Definitions.Def_LocalConjugacy_Examples
open LocalConjugacy
universe u v

theorem solution {J : Type u} {N : Type v} [Group J] [Group N]
    (a : J →* MulAut N)
    (h : ∀ f : FiniteCocycle a, ∃ n : N, ∀ x : J, f.val x = n⁻¹ * a x n) :
    Subsingleton (FiniteH1 a) := by
  constructor
  intro α β
  induction α using Quotient.inductionOn with
  | h f =>
    induction β using Quotient.inductionOn with
    | h g =>
      apply Quotient.sound
      obtain ⟨n, hn⟩ := h f
      obtain ⟨m, hm⟩ := h g
      change ∃ k : N, ∀ x : J, g.val x = k⁻¹ * f.val x * a x k
      refine ⟨n⁻¹ * m, fun x => ?_⟩
      rw [hn x, hm x, map_mul, map_inv]
      group
