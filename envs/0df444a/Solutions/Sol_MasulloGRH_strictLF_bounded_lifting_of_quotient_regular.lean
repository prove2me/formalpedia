-- Prove2me | solution 1 for MasulloGRH.strictLF_bounded_lifting_of_quotient_regular
-- status  : ACCEPTED   (prove)
-- author  : @Abhishek Anand
-- created : 2026-11-20T23:29:06.122892+00:00
-- url     : https://prove2.me/submissions/a7a0d9bd-223e-4a75-a9a9-daa8ee3b4275

import Theorems.Thm_MasulloGRH_nuclear_frechet_quotient_lifts_bounded

open MasulloGRH

theorem solution (E : Type*) [AddCommGroup E] [Module ℂ E]
    [TopologicalSpace E] (X : ℕ → Submodule ℂ E) (hmono : Monotone X)
    (hexh : ∀ x : E, ∃ n, x ∈ X n) (hX : ∀ n, IsFrechet (X n) ∧ IsNuclear (X n))
    (htop : ‹TopologicalSpace E› =
      sInf {t | IsLocallyConvexTopology E t ∧ ∀ n, @Continuous (X n) E _ t Subtype.val})
    (V : Submodule ℂ E) (hV : IsClosed (V : Set E))
    (hreg : ∀ B : Set (E ⧸ V), Bornology.IsVonNBounded ℂ B →
      ∃ (n : ℕ) (A : Set (X n ⧸ V.comap (X n).subtype)), Bornology.IsVonNBounded ℂ A ∧
        B ⊆ Submodule.mapQ (V.comap (X n).subtype) V (X n).subtype le_rfl '' A) :
    LiftsBoundedSets (V.mkQ : E → E ⧸ V)  := by
  intro B hB
  obtain ⟨n, A, hA, hBA⟩ := hreg B hB
  let W := V.comap (X n).subtype
  have hW : IsClosed (W : Set (X n)) := hV.preimage continuous_subtype_val
  obtain ⟨S, hS, hAS⟩ :=
    nuclear_frechet_quotient_lifts_bounded (X n) (hX n).1 (hX n).2 W hW A hA
  refine ⟨(X n).subtypeL '' S, hS.image (X n).subtypeL, ?_⟩
  intro b hb
  obtain ⟨a, ha, rfl⟩ := hBA hb
  obtain ⟨v, hv, rfl⟩ := hAS ha
  exact ⟨v.val, ⟨v, hv, rfl⟩, rfl⟩
