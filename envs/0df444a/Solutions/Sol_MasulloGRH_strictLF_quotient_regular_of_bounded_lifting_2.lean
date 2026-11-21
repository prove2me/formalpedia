-- Prove2me | solution 2 for MasulloGRH.strictLF_quotient_regular_of_bounded_lifting
-- status  : ACCEPTED   (prove)
-- author  : @marozols
-- created : 2026-11-20T23:47:33.925299+00:00
-- url     : https://prove2.me/submissions/e11f278a-8ea3-4a67-93e1-3dd249bb8c45

import Theorems.Thm_MasulloGRH_bounded_sets_strict_inductive_limit
import Theorems.Thm_MasulloGRH_strictLF_hlcs_and_closed_steps

set_option autoImplicit false

open MasulloGRH Set

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
  obtain ⟨hHLCS, hcl⟩ :=
    strictLF_hlcs_and_closed_steps E X hmono hexh (fun n => (hX n).1) htop
  obtain ⟨⟨ι, _, p, hp⟩, _⟩ := hHLCS
  have hadd : IsTopologicalAddGroup E := hp.topologicalAddGroup
  have hsmul : ContinuousSMul ℂ E := hp.continuousSMul
  -- lift `B` to a bounded subset of `E`, which lies and is bounded in a step
  obtain ⟨B', hB'b, hBB'⟩ := hlift B hB
  obtain ⟨n, B'', hB''b, rfl⟩ :=
    (bounded_sets_strict_inductive_limit E ⟨⟨ι, inferInstance, p, hp⟩, inferInstance⟩ X hmono
      hexh hcl htop B').1 hB'b
  refine ⟨n, (V.comap (X n).subtype).mkQ '' B'', ?_, ?_⟩
  · exact hB''b.image ((V.comap (X n).subtype).mkQL)
  · intro b hb
    obtain ⟨_, ⟨a, ha, rfl⟩, rfl⟩ := hBB' hb
    exact ⟨(V.comap (X n).subtype).mkQ a, ⟨a, ha, rfl⟩, rfl⟩
