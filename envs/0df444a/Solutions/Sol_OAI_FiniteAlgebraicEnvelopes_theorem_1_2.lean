-- Prove2me | solution 1 for OAI.FiniteAlgebraicEnvelopes.theorem_1_2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-24T19:25:25.955025+00:00
-- url     : https://prove2.me/submissions/6ca1f653-8818-44ea-acd7-e86e2f185ad9

import Mathlib
import Definitions.Def_BooneHigman
import Theorems.Thm_OAI_FiniteAlgebraicEnvelopes_envelope

open OAI.FiniteAlgebraicEnvelopes

universe u

theorem solution {G : Type u} [Group G] (hG : HasDecidableWordProblem G) :
    ∃ (Γ : Type u) (_ : Group Γ), Group.IsFinitelyPresented Γ ∧
      (∃ φ : G →* Γ, Function.Injective φ) ∧
      ∃ (X : Type u) (_ : MulAction Γ X) (_ : FaithfulSMul Γ X),
        MulAction.IsMultiplyPretransitive Γ X 2 ∧ Infinite X ∧ Countable X ∧
        ∀ x : X, Group.FG (MulAction.stabilizer Γ x) := by
  have hfg : Group.FG G := by
    obtain ⟨n, t, hgen, -⟩ := hG
    exact Group.fg_iff.2 ⟨Set.range t, hgen, Set.finite_range t⟩
  obtain ⟨Γ, hΓ, X, hX, hfp, hcount, hinf, hfaith, htwo, hstab, f, hf⟩ :=
    OAI.FiniteAlgebraicEnvelopes.envelope G hG
  exact ⟨Γ, hΓ, hfp, ⟨f, hf⟩, X, hX, hfaith,
    MulAction.is_two_pretransitive_iff.2 (fun h h' => htwo _ _ _ _ h h'),
    hinf, hcount, hstab⟩
