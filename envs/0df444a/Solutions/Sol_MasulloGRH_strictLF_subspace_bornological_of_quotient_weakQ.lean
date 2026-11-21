-- Prove2me | solution 1 for MasulloGRH.strictLF_subspace_bornological_of_quotient_weakQ
-- status  : ACCEPTED   (prove)
-- author  : @Ismael Correa
-- created : 2026-11-21T00:13:42.679425+00:00
-- url     : https://prove2.me/submissions/cde0eebc-1348-4f09-99c2-b1a48a80038d

import Definitions.Def_MasulloGRH_LocallyConvex
import Theorems.Thm_MasulloGRH_strictLF_quotient_condM_of_weakQ
import Theorems.Thm_MasulloGRH_strictLF_limit_subspace_of_quotient_condM
import Theorems.Thm_MasulloGRH_strictLF_closed_subspace_bornological_of_limit_subspace

set_option autoImplicit false

open MasulloGRH

theorem solution
    (E : Type*) [AddCommGroup E] [Module ℂ E]
    [TopologicalSpace E] (X : ℕ → Submodule ℂ E) (hmono : Monotone X)
    (hexh : ∀ x : E, ∃ n, x ∈ X n) (hX : ∀ n, IsFrechet (X n) ∧ IsNuclear (X n))
    (htop : ‹TopologicalSpace E› =
      sInf {t | IsLocallyConvexTopology E t ∧ ∀ n, @Continuous (X n) E _ t Subtype.val})
    (V : Submodule ℂ E) (hV : IsClosed (V : Set E))
    (hwQ : ∀ n : ℕ, ∃ m : ℕ, n ≤ m ∧ ∃ U ∈ nhds (0 : X n), ∀ k : ℕ, m ≤ k →
      ∀ W ∈ nhds (0 : X m), ∃ U' ∈ nhds (0 : X k), ∃ r : ℝ, 0 < r ∧
        ∀ x ∈ U, ∀ y ∈ U', ((x : E) - (y : E)) ∈ V →
          ∃ w ∈ W, ((x : E) - (r : ℂ) • (w : E)) ∈ V) :
    IsBornological V := by
  have hM := strictLF_quotient_condM_of_weakQ E X hmono hexh hX htop V hV hwQ
  have hlim := strictLF_limit_subspace_of_quotient_condM E X hmono hexh hX htop V hV hM
  exact strictLF_closed_subspace_bornological_of_limit_subspace E X hmono hexh
    (fun n => (hX n).1) htop V hV hlim
