-- Prove2me | solution 1 for MasulloGRH.strictLF_quotient_condM_of_limit_subspace
-- status  : ACCEPTED   (prove)
-- author  : @Ismael Correa
-- created : 2026-11-20T23:56:33.656491+00:00
-- url     : https://prove2.me/submissions/5dc2bc7f-a389-4dcd-9977-954e70e91398

import Definitions.Def_MasulloGRH_LocallyConvex
import Theorems.Thm_MasulloGRH_limit_subspace_hull_condition
import Theorems.Thm_MasulloGRH_strictLF_quotient_condM_of_hull_condition

set_option autoImplicit false

open MasulloGRH

theorem solution (E : Type*) [AddCommGroup E] [Module ℂ E]
    [TopologicalSpace E] (X : ℕ → Submodule ℂ E) (hmono : Monotone X)
    (hexh : ∀ x : E, ∃ n, x ∈ X n) (hX : ∀ n, IsFrechet (X n) ∧ IsNuclear (X n))
    (htop : ‹TopologicalSpace E› =
      sInf {t | IsLocallyConvexTopology E t ∧ ∀ n, @Continuous (X n) E _ t Subtype.val})
    (V : Submodule ℂ E) (hV : IsClosed (V : Set E))
    (hlim : (instTopologicalSpaceSubtype : TopologicalSpace V) =
        sInf {t | IsLocallyConvexTopology V t ∧
          ∀ n, @Continuous ↥(V ⊓ X n) V _ t (Submodule.inclusion inf_le_left)}) :
    ∀ n : ℕ, ∃ m : ℕ, n ≤ m ∧ ∃ U ∈ nhds (0 : X n), ∀ k : ℕ, m ≤ k →
      ∀ W ∈ nhds (0 : X m), ∃ W' ∈ nhds (0 : X k),
        ∀ x ∈ U, ∀ y ∈ W', ((x : E) - (y : E)) ∈ V → ∃ w ∈ W, ((x : E) - (w : E)) ∈ V :=
  strictLF_quotient_condM_of_hull_condition E X hmono hexh hX htop V hV
    (limit_subspace_hull_condition E X hmono hexh hX htop V hV hlim)
