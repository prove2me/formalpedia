-- Prove2me | solution 2 for MasulloGRH.strictLF_subspace_bornological_of_quotient_regular
-- status  : ACCEPTED   (prove)
-- author  : @Ismael Correa
-- created : 2026-11-21T00:02:14.162552+00:00
-- url     : https://prove2.me/submissions/e37c0d82-6c7e-4696-9b1c-66035c5a3905

import Theorems.Thm_MasulloGRH_strictLF_quotient_condM_of_quotient_regular
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
    (hreg : ∀ B : Set (E ⧸ V), Bornology.IsVonNBounded ℂ B →
      ∃ (n : ℕ) (A : Set (X n ⧸ V.comap (X n).subtype)), Bornology.IsVonNBounded ℂ A ∧
        B ⊆ Submodule.mapQ (V.comap (X n).subtype) V (X n).subtype le_rfl '' A) :
    IsBornological V := by
  have hM := strictLF_quotient_condM_of_quotient_regular E X hmono hexh hX htop V hV hreg
  have hlim := strictLF_limit_subspace_of_quotient_condM E X hmono hexh hX htop V hV hM
  exact strictLF_closed_subspace_bornological_of_limit_subspace E X hmono hexh
    (fun n => (hX n).1) htop V hV hlim
