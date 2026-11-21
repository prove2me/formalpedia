-- Prove2me | solution 1 for MasulloGRH.limit_subspace_iff_bounded_lifting
-- status  : ACCEPTED   (prove)
-- author  : @Ismael Correa
-- created : 2026-11-20T23:26:09.061443+00:00
-- url     : https://prove2.me/submissions/410afec4-6e70-4cb4-9af1-6cd09e829d8a

import Definitions.Def_MasulloGRH_LocallyConvex
import Theorems.Thm_MasulloGRH_strictLF_quotient_regular_of_limit_subspace
import Theorems.Thm_MasulloGRH_strictLF_bounded_lifting_of_quotient_regular
import Theorems.Thm_MasulloGRH_limit_subspace_of_bounded_lifting

set_option autoImplicit false

open MasulloGRH

theorem solution (E : Type*) [AddCommGroup E] [Module ℂ E]
    [TopologicalSpace E] (X : ℕ → Submodule ℂ E) (hmono : Monotone X)
    (hexh : ∀ x : E, ∃ n, x ∈ X n) (hX : ∀ n, IsFrechet (X n) ∧ IsNuclear (X n))
    (htop : ‹TopologicalSpace E› =
      sInf {t | IsLocallyConvexTopology E t ∧ ∀ n, @Continuous (X n) E _ t Subtype.val})
    (V : Submodule ℂ E) (hV : IsClosed (V : Set E)) :
    ((instTopologicalSpaceSubtype : TopologicalSpace V) =
        sInf {t | IsLocallyConvexTopology V t ∧
          ∀ n, @Continuous ↥(V ⊓ X n) V _ t (Submodule.inclusion inf_le_left)}) ↔
      LiftsBoundedSets (V.mkQ : E → E ⧸ V) := by
  constructor
  · intro hlim
    exact strictLF_bounded_lifting_of_quotient_regular E X hmono hexh hX htop V hV
      (strictLF_quotient_regular_of_limit_subspace E X hmono hexh hX htop V hV hlim)
  · intro hlift
    exact limit_subspace_of_bounded_lifting E X hmono hexh hX htop V hV hlift
