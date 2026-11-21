-- Prove2me | solution 1 for MasulloGRH.limit_subspace_of_bounded_lifting
-- status  : ACCEPTED   (prove)
-- author  : @Ismael Correa
-- created : 2026-11-20T23:44:38.720245+00:00
-- url     : https://prove2.me/submissions/0b75d44c-38fd-46e1-a2b5-7eaf35ef552b

import Definitions.Def_MasulloGRH_LocallyConvex
import Theorems.Thm_MasulloGRH_strictLF_quotient_regular_of_bounded_lifting
import Theorems.Thm_MasulloGRH_strictLF_subspace_bornological_of_quotient_regular
import Theorems.Thm_MasulloGRH_strictLF_limit_subspace_of_bornological

set_option autoImplicit false

open MasulloGRH

theorem solution (E : Type*) [AddCommGroup E] [Module ℂ E]
    [TopologicalSpace E] (X : ℕ → Submodule ℂ E) (hmono : Monotone X)
    (hexh : ∀ x : E, ∃ n, x ∈ X n) (hX : ∀ n, IsFrechet (X n) ∧ IsNuclear (X n))
    (htop : ‹TopologicalSpace E› =
      sInf {t | IsLocallyConvexTopology E t ∧ ∀ n, @Continuous (X n) E _ t Subtype.val})
    (V : Submodule ℂ E) (hV : IsClosed (V : Set E))
    (hlift : LiftsBoundedSets (V.mkQ : E → E ⧸ V)) :
    (instTopologicalSpaceSubtype : TopologicalSpace V) =
        sInf {t | IsLocallyConvexTopology V t ∧
          ∀ n, @Continuous ↥(V ⊓ X n) V _ t (Submodule.inclusion inf_le_left)} :=
  strictLF_limit_subspace_of_bornological E X hmono hexh hX htop V hV
    (strictLF_subspace_bornological_of_quotient_regular E X hmono hexh hX htop V hV
      (strictLF_quotient_regular_of_bounded_lifting E X hmono hexh hX htop V hV hlift))
