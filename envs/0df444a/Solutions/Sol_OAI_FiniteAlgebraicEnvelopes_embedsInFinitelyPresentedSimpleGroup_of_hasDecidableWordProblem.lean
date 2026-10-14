-- Prove2me | solution 1 for OAI.FiniteAlgebraicEnvelopes.embedsInFinitelyPresentedSimpleGroup_of_hasDecidableWordProblem
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-12T18:40:31.444887+00:00
-- url     : https://prove2.me/submissions/d0f6fb10-617e-4dd5-af18-2e27c9c6b5b5
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_BooneHigman
import Theorems.Thm_OAI_FiniteAlgebraicEnvelopes_theorem_1_2
import Theorems.Thm_theorem_2_3_zaremsky

universe u

open OAI.FiniteAlgebraicEnvelopes in
theorem solution
    (GroupType : Type u) [Group GroupType] [Group.FG GroupType]
    (h : HasDecidableWordProblem GroupType) :
    EmbedsInFinitelyPresentedSimpleGroup GroupType := by
  classical
  obtain ⟨Γ, _, hΓfp, ⟨φ, hφinj⟩, X, _, _, h2trans, hXinf, hXcount, hstabfg⟩ :=
    OAI.FiniteAlgebraicEnvelopes.theorem_1_2 h
  have : Nontrivial X := inferInstance
  obtain ⟨x0, x1, hx01⟩ := exists_pair_ne X
  have horbits : ∃ reps : Finset (Sym2 X), ∀ p : Sym2 X, ¬p.IsDiag →
      ∃ q ∈ reps, ∃ γ : Γ, Sym2.map (fun x => γ • x) q = p := by
    refine ⟨{s(x0, x1)}, ?_⟩
    intro p hp
    induction p using Sym2.ind with
    | _ a b =>
      have hab : a ≠ b := fun hab => hp (Sym2.mk_isDiag_iff.2 hab)
      obtain ⟨γ, hγa, hγb⟩ :=
        (MulAction.is_two_pretransitive_iff.mp h2trans) hx01 hab
      exact ⟨s(x0, x1), Finset.mem_singleton_self _, γ, by rw [Sym2.map_mk, hγa, hγb]⟩
  have hΓembed : EmbedsInFinitelyPresentedSimpleGroup Γ :=
    theorem_2_3_zaremsky hstabfg horbits
  obtain ⟨K, _, hKfp, hKsimple, ι, hιinj⟩ := hΓembed
  exact ⟨K, _, hKfp, hKsimple, ι.comp φ, hιinj.comp hφinj⟩
