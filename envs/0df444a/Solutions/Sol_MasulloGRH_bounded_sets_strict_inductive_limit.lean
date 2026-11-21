-- Prove2me | solution 1 for MasulloGRH.bounded_sets_strict_inductive_limit
-- status  : ACCEPTED   (prove)
-- author  : @dga471
-- created : 2026-11-20T22:32:14.467401+00:00
-- url     : https://prove2.me/submissions/c9440569-7eaf-443e-9574-6a20fddabfda

import Theorems.Thm_MasulloGRH_escaping_set_seminorm

open MasulloGRH Set

private theorem continuous_into_seminorms {A F I : Type*} [AddCommGroup A] [Module ℂ A]
    [TopologicalSpace A] [IsTopologicalAddGroup A] [AddCommGroup F] [Module ℂ F]
    {τ : TopologicalSpace F} {q : SeminormFamily ℂ F I}
    (hq : WithSeminorms (topology := τ) q) (f : A →ₗ[ℂ] F)
    (h : ∀ i, Continuous ((q i).comp f)) : @Continuous A F _ τ f := by
  letI := τ
  exact hq.continuous_of_continuous_comp f h

theorem solution (E : Type*) [AddCommGroup E] [Module ℂ E]
    [t : TopologicalSpace E] (hE : IsHLCS E) (X : ℕ → Submodule ℂ E) (hmono : Monotone X)
    (hexh : ∀ x : E, ∃ n, x ∈ X n) (hcl : ∀ n, IsClosed (X n : Set E))
    (htop : t = sInf {u | IsLocallyConvexTopology E u ∧
      ∀ n, @Continuous (X n) E _ u Subtype.val}) (B : Set E) :
    Bornology.IsVonNBounded ℂ B ↔ ∃ (n : ℕ) (B' : Set (X n)),
      Bornology.IsVonNBounded ℂ B' ∧ B = Subtype.val '' B' := by
  obtain ⟨ι, _, p, hp⟩ := hE.1
  haveI := hp.topologicalAddGroup
  constructor
  · intro hB
    have hstage : ∃ n, B ⊆ (X n : Set E) := by
      by_contra! he
      have hesc (n : ℕ) : ∃ x ∈ B, x ∉ X n := Set.not_subset.mp (he n)
      obtain ⟨q, hq, hu⟩ := escaping_set_seminorm E hE X hmono hexh hcl B hesc
      let family : SeminormFamily ℂ E E := fun _ => q
      let τ := family.moduleFilterBasis.topology
      have hτ : WithSeminorms (topology := τ) family := ⟨rfl⟩
      have hin (n : ℕ) : @Continuous (X n) E (@instTopologicalSpaceSubtype E _ t) τ Subtype.val :=
        @continuous_into_seminorms (X n) E E _ _ (@instTopologicalSpaceSubtype E _ t) _ _ _
          τ family hτ (X n).subtype (fun _ => hq n)
      have hle : t ≤ τ := by
        exact htop.le.trans (sInf_le ⟨⟨E, inferInstance, family, hτ⟩, hin⟩)
      have hbτ : @Bornology.IsVonNBounded ℂ E _ _ _ τ B :=
        fun _ hV => hB ((nhds_mono hle) hV)
      letI : TopologicalSpace E := τ
      exact hu (hτ.isVonNBounded_iff_seminorm_bddAbove.mp hbτ (0 : E))
    obtain ⟨n, hn⟩ := hstage
    refine ⟨n, Subtype.val ⁻¹' B, ?_, ?_⟩
    · have hind := (X n).subtype.withSeminorms_induced hp
      apply hind.isVonNBounded_iff_seminorm_bounded.mpr
      intro i
      obtain ⟨r, hr, h⟩ := hp.isVonNBounded_iff_seminorm_bounded.mp hB i
      exact ⟨r, hr, fun x hx => h x hx⟩
    · ext x
      exact ⟨fun hx => ⟨⟨x, hn hx⟩, hx, rfl⟩, fun ⟨y, hy, h⟩ => h ▸ hy⟩
  · rintro ⟨n, B', hb, rfl⟩
    exact hb.image (X n).subtypeL
