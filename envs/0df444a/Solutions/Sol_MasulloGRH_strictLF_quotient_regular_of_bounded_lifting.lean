-- Prove2me | solution 1 for MasulloGRH.strictLF_quotient_regular_of_bounded_lifting
-- status  : ACCEPTED   (prove)
-- author  : @Ismael Correa
-- created : 2026-11-20T23:46:37.370103+00:00
-- url     : https://prove2.me/submissions/cebc751e-1102-439f-bcb1-fb18ab20b118

import Definitions.Def_MasulloGRH_LocallyConvex
import Theorems.Thm_MasulloGRH_bounded_in_strict_frechet_stages

set_option autoImplicit false

open MasulloGRH

theorem solution
    (E : Type*) [AddCommGroup E] [Module ℂ E]
    [TopologicalSpace E] (X : ℕ → Submodule ℂ E) (hmono : Monotone X)
    (hexh : ∀ x : E, ∃ n, x ∈ X n) (hX : ∀ n, IsFrechet (X n) ∧ IsNuclear (X n))
    (htop : ‹TopologicalSpace E› =
      sInf {t | IsLocallyConvexTopology E t ∧ ∀ n, @Continuous (X n) E _ t Subtype.val})
    (V : Submodule ℂ E) (hV : IsClosed (V : Set E))
    (hlift : LiftsBoundedSets (V.mkQ : E → E ⧸ V)) :
    ∀ B : Set (E ⧸ V), Bornology.IsVonNBounded ℂ B →
      ∃ (n : ℕ) (A : Set (X n ⧸ V.comap (X n).subtype)), Bornology.IsVonNBounded ℂ A ∧
        B ⊆ Submodule.mapQ (V.comap (X n).subtype) V (X n).subtype le_rfl '' A := by
  intro B hB
  obtain ⟨B', hB', hsub⟩ := hlift B hB
  obtain ⟨-, hloc⟩ := bounded_in_strict_frechet_stages E X hmono hexh (fun n => (hX n).1) htop
  obtain ⟨n, A, hA, rfl⟩ := hloc B' hB'
  refine ⟨n, (V.comap (X n).subtype).mkQ '' A, ?_, ?_⟩
  · have hc : Continuous ((V.comap (X n).subtype).mkQ) := continuous_quot_mk
    exact hA.image (⟨(V.comap (X n).subtype).mkQ, hc⟩ : (X n) →L[ℂ] (X n ⧸ V.comap (X n).subtype))
  · intro y hy
    obtain ⟨_, ⟨a, ha, rfl⟩, rfl⟩ := hsub hy
    exact ⟨_, ⟨a, ha, rfl⟩, rfl⟩
