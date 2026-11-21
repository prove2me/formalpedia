-- Prove2me | solution 1 for MasulloGRH.strictLF_quotient_t2Space
-- status  : ACCEPTED   (prove)
-- author  : @Ismael Correa
-- created : 2026-11-21T00:07:56.76395+00:00
-- url     : https://prove2.me/submissions/a7fe370c-ccad-41e4-8c10-a922a5b3562a

import Theorems.Thm_MasulloGRH_strictLF_hlcs_and_closed_steps

set_option autoImplicit false

open MasulloGRH

theorem solution (E : Type*) [AddCommGroup E] [Module ℂ E]
    [TopologicalSpace E] (X : ℕ → Submodule ℂ E) (hmono : Monotone X)
    (hexh : ∀ x : E, ∃ n, x ∈ X n) (hX : ∀ n, IsFrechet (X n))
    (htop : ‹TopologicalSpace E› =
      sInf {t | IsLocallyConvexTopology E t ∧ ∀ n, @Continuous (X n) E _ t Subtype.val})
    (V : Submodule ℂ E) (hV : IsClosed (V : Set E)) :
    T2Space (E ⧸ V) := by
  obtain ⟨⟨⟨ι, _, p, hp⟩, _⟩, _⟩ := strictLF_hlcs_and_closed_steps E X hmono hexh hX htop
  haveI : IsTopologicalAddGroup E := hp.topologicalAddGroup
  haveI : IsClosed (V : Set E) := hV
  infer_instance
