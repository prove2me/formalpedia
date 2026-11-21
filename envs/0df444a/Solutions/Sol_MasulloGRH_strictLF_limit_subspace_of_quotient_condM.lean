-- Prove2me | solution 1 for MasulloGRH.strictLF_limit_subspace_of_quotient_condM
-- status  : ACCEPTED   (prove)
-- author  : @marozols
-- created : 2026-11-21T00:06:14.09337+00:00
-- url     : https://prove2.me/submissions/9853de4c-2611-4932-91a6-504ec972bbac

import Theorems.Thm_MasulloGRH_strictLF_limit_subspace_of_bornological
import Theorems.Thm_MasulloGRH_strictLF_subspace_bornological_of_quotient_weakQ

set_option autoImplicit false

open MasulloGRH Topology

theorem solution
    (E : Type*) [AddCommGroup E] [Module ℂ E]
    [TopologicalSpace E] (X : ℕ → Submodule ℂ E) (hmono : Monotone X)
    (hexh : ∀ x : E, ∃ n, x ∈ X n) (hX : ∀ n, IsFrechet (X n) ∧ IsNuclear (X n))
    (htop : ‹TopologicalSpace E› =
      sInf {t | IsLocallyConvexTopology E t ∧ ∀ n, @Continuous (X n) E _ t Subtype.val})
    (V : Submodule ℂ E) (hV : IsClosed (V : Set E))
    (hM : ∀ n : ℕ, ∃ m : ℕ, n ≤ m ∧ ∃ U ∈ nhds (0 : X n), ∀ k : ℕ, m ≤ k →
      ∀ W ∈ nhds (0 : X m), ∃ W' ∈ nhds (0 : X k),
        ∀ x ∈ U, ∀ y ∈ W', ((x : E) - (y : E)) ∈ V → ∃ w ∈ W, ((x : E) - (w : E)) ∈ V) :
    (instTopologicalSpaceSubtype : TopologicalSpace V) =
        sInf {t | IsLocallyConvexTopology V t ∧
          ∀ n, @Continuous ↥(V ⊓ X n) V _ t (Submodule.inclusion inf_le_left)} := by
  apply strictLF_limit_subspace_of_bornological E X hmono hexh hX htop V hV
  apply strictLF_subspace_bornological_of_quotient_weakQ E X hmono hexh hX htop V hV
  intro n
  obtain ⟨m, hnm, U, hU, hstage⟩ := hM n
  refine ⟨m, hnm, U, hU, ?_⟩
  intro k hmk W hW
  obtain ⟨W', hW', hcompare⟩ := hstage k hmk W hW
  refine ⟨W', hW', (1 : ℝ), zero_lt_one, ?_⟩
  intro x hx y hy hxy
  obtain ⟨w, hw, heq⟩ := hcompare x hx y hy hxy
  exact ⟨w, hw, by simpa only [Complex.ofReal_one, one_smul] using heq⟩
