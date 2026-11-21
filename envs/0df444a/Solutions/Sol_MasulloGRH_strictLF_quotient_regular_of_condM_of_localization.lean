-- Prove2me | solution 1 for MasulloGRH.strictLF_quotient_regular_of_condM_of_localization
-- status  : ACCEPTED   (prove)
-- author  : @Ismael Correa
-- created : 2026-11-20T23:56:16.597777+00:00
-- url     : https://prove2.me/submissions/67f64f9b-9158-4e1d-8274-6fd0d344af3e

import Theorems.Thm_MasulloGRH_strictLF_quotient_regular_of_condM_quasiComplete_of_localization
import Theorems.Thm_MasulloGRH_strictLF_quotient_regular_of_condM_of_quasiComplete

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
    ∀ B : Set (E ⧸ V), Bornology.IsVonNBounded ℂ B →
      ∃ (n : ℕ) (A : Set (X n ⧸ V.comap (X n).subtype)), Bornology.IsVonNBounded ℂ A ∧
        B ⊆ Submodule.mapQ (V.comap (X n).subtype) V (X n).subtype le_rfl '' A :=
  strictLF_quotient_regular_of_condM_of_quasiComplete E X hmono hexh hX htop V hV
    (strictLF_quotient_regular_of_condM_quasiComplete_of_localization E X hmono hexh hX htop V hV hL)
