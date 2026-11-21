-- Prove2me | solution 1 for MasulloGRH.strictLF_quotient_regular_iff_bounded_lifting
-- status  : ACCEPTED   (prove)
-- author  : @Abhishek Anand
-- created : 2026-11-20T23:43:19.079182+00:00
-- url     : https://prove2.me/submissions/e9b6afbc-450d-4658-8f75-6fc9b4e953a4

import Theorems.Thm_MasulloGRH_bounded_in_strict_frechet_stages
import Theorems.Thm_MasulloGRH_strictLF_bounded_lifting_of_quotient_regular

open MasulloGRH

theorem solution (E : Type*) [AddCommGroup E] [Module ℂ E]
    [TopologicalSpace E] (X : ℕ → Submodule ℂ E) (hmono : Monotone X)
    (hexh : ∀ x : E, ∃ n, x ∈ X n) (hX : ∀ n, IsFrechet (X n) ∧ IsNuclear (X n))
    (htop : ‹TopologicalSpace E› =
      sInf {t | IsLocallyConvexTopology E t ∧ ∀ n, @Continuous (X n) E _ t Subtype.val})
    (V : Submodule ℂ E) (hV : IsClosed (V : Set E)) :
    LiftsBoundedSets (V.mkQ : E → E ⧸ V) ↔
    ∀ B : Set (E ⧸ V), Bornology.IsVonNBounded ℂ B →
      ∃ (n : ℕ) (A : Set (X n ⧸ V.comap (X n).subtype)), Bornology.IsVonNBounded ℂ A ∧
        B ⊆ Submodule.mapQ (V.comap (X n).subtype) V (X n).subtype le_rfl '' A := by
  constructor
  · intro hlift B hB
    obtain ⟨S, hS, hBS⟩ := hlift B hB
    obtain ⟨n, A, hA, hSA⟩ := (bounded_in_strict_frechet_stages E X hmono hexh
      (fun n => (hX n).1) htop).2 S hS
    let W := V.comap (X n).subtype
    refine ⟨n, W.mkQL '' A, hA.image W.mkQL, ?_⟩
    intro b hb
    obtain ⟨v, hv, rfl⟩ := hBS hb
    rw [hSA] at hv
    obtain ⟨a, ha, rfl⟩ := hv
    exact ⟨W.mkQ a, ⟨a, ha, rfl⟩, rfl⟩
  · exact strictLF_bounded_lifting_of_quotient_regular E X hmono hexh hX htop V hV
