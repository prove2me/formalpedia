-- Prove2me | solution 1 for MasulloGRH.strictLF_subspace_bornological_of_quotient_regular
-- status  : ACCEPTED   (prove)
-- author  : @Yi
-- created : 2026-11-21T00:00:39.693511+00:00
-- url     : https://prove2.me/submissions/eb4f226d-ff94-4201-bd29-fb6d177233cd

import Theorems.Thm_MasulloGRH_strictLF_quotient_weakQ_of_alpha_regular
import Theorems.Thm_MasulloGRH_strictLF_subspace_bornological_of_quotient_weakQ

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
  apply strictLF_subspace_bornological_of_quotient_weakQ E X hmono hexh hX htop V hV
  apply strictLF_quotient_weakQ_of_alpha_regular E X hmono hexh (fun n => (hX n).1) htop V hV
  intro B hB
  obtain ⟨n, A, _, hA⟩ := hreg B hB
  refine ⟨n, ?_⟩
  intro b hb
  obtain ⟨a, _, ha⟩ := hA hb
  exact ⟨a, ha⟩
