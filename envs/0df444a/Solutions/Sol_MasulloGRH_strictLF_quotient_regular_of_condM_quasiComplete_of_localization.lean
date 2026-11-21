-- Prove2me | solution 1 for MasulloGRH.strictLF_quotient_regular_of_condM_quasiComplete_of_localization
-- status  : ACCEPTED   (prove)
-- author  : @Ismael Correa
-- created : 2026-11-21T00:05:18.327193+00:00
-- url     : https://prove2.me/submissions/cd91e551-cd9a-460d-a5d1-b986f67d576a

import Theorems.Thm_MasulloGRH_strictLF_quotient_t2Space
import Theorems.Thm_MasulloGRH_frechet_quotient_isCompleteTVS
import Theorems.Thm_MasulloGRH_strictLF_quotient_bounded_cauchy_converges_of_localization

set_option autoImplicit false

open MasulloGRH

theorem solution (E : Type*) [AddCommGroup E] [Module ℂ E]
    [TopologicalSpace E] (X : ℕ → Submodule ℂ E) (hmono : Monotone X)
    (hexh : ∀ x : E, ∃ n, x ∈ X n) (hX : ∀ n, IsFrechet (X n) ∧ IsNuclear (X n))
    (htop : ‹TopologicalSpace E› =
      sInf {t | IsLocallyConvexTopology E t ∧ ∀ n, @Continuous (X n) E _ t Subtype.val})
    (V : Submodule ℂ E) (hV : IsClosed (V : Set E))
    (hL : ∀ n : ℕ, ∃ m : ℕ, n ≤ m ∧ ∃ U ∈ nhds (0 : X n), ∀ W ∈ nhds (0 : X m),
      ∃ G ∈ nhds (0 : E ⧸ V), ∀ x ∈ U, Submodule.Quotient.mk (x : E) ∈ G →
        ∃ w ∈ W, ((x : E) - (w : E)) ∈ V) :
    IsQuasiComplete (E ⧸ V) := by
  refine ⟨strictLF_quotient_t2Space E X hmono hexh (fun n => (hX n).1) htop V hV, ?_⟩
  refine strictLF_quotient_bounded_cauchy_converges_of_localization E X hmono hexh hX htop V hV hL ?_
  intro m
  exact frechet_quotient_isCompleteTVS (X m) (hX m).1 (V.comap (X m).subtype)
    (hV.preimage continuous_subtype_val)
