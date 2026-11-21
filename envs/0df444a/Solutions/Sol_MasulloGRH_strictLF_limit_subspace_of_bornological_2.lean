-- Prove2me | solution 2 for MasulloGRH.strictLF_limit_subspace_of_bornological
-- status  : ACCEPTED   (prove)
-- author  : @Ismael Correa
-- created : 2026-11-20T23:50:33.916352+00:00
-- url     : https://prove2.me/submissions/1e98587c-a384-4374-b62e-e7f42ff6de59

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
    (hborn : IsBornological V) :
    (instTopologicalSpaceSubtype : TopologicalSpace V) =
        sInf {t | IsLocallyConvexTopology V t ∧
          ∀ n, @Continuous ↥(V ⊓ X n) V _ t (Submodule.inclusion inf_le_left)} := by
  obtain ⟨⟨⟨ι, hι, p, hp⟩, -⟩, hloc⟩ :=
    bounded_in_strict_frechet_stages E X hmono hexh (fun n => (hX n).1) htop
  have := hp.topologicalAddGroup
  have hpV : WithSeminorms (p.comp V.subtype) := LinearMap.withSeminorms_induced hp V.subtype
  -- bounded subsets of `V` are bounded subsets of some `V ⊓ X n`
  have hbdd : ∀ B : Set V, Bornology.IsVonNBounded ℂ B → ∃ n, ∃ B'' : Set ↥(V ⊓ X n),
      Bornology.IsVonNBounded ℂ B'' ∧ Submodule.inclusion inf_le_left '' B'' = B := by
    intro B hB
    have hBE : Bornology.IsVonNBounded ℂ ((Subtype.val : V → E) '' B) :=
      (hp.image_isVonNBounded_iff_seminorm_bounded _).2
        ((hpV.isVonNBounded_iff_seminorm_bounded).1 hB)
    obtain ⟨n, A, -, hBA⟩ := hloc _ hBE
    have hBX : ∀ x ∈ B, (x : E) ∈ X n := by
      intro x hx
      have : (x : E) ∈ Subtype.val '' A := hBA ▸ ⟨x, hx, rfl⟩
      obtain ⟨a, -, ha⟩ := this
      exact ha ▸ a.2
    have hpW : WithSeminorms (p.comp (V ⊓ X n).subtype) :=
      LinearMap.withSeminorms_induced hp _
    refine ⟨n, {z | Submodule.inclusion inf_le_left z ∈ B}, ?_, ?_⟩
    · rw [hpW.isVonNBounded_iff_seminorm_bounded]
      intro i
      obtain ⟨r, hr, h⟩ := (hp.isVonNBounded_iff_seminorm_bounded.1 hBE) i
      exact ⟨r, hr, fun z hz => h _ ⟨_, hz, rfl⟩⟩
    · ext x
      constructor
      · rintro ⟨z, hz, rfl⟩
        exact hz
      · intro hx
        exact ⟨⟨x, x.2, hBX x hx⟩, hx, rfl⟩
  apply le_antisymm
  · refine le_sInf ?_
    rintro t ⟨⟨κ, hκ, q, hq⟩, hcont⟩
    rw [← continuous_id_iff_le]
    have key : ∀ k, @Continuous V ℝ instTopologicalSpaceSubtype _ (q k) := by
      intro k
      apply hborn (q k)
      intro B hB
      obtain ⟨n, B'', hB'', rfl⟩ := hbdd B hB
      have hpW : WithSeminorms (p.comp (V ⊓ X n).subtype) :=
        LinearMap.withSeminorms_induced hp _
      have hqk : Continuous ((q k).comp (Submodule.inclusion (inf_le_left : V ⊓ X n ≤ V))) :=
        (hq.continuous_seminorm k).comp (hcont n)
      obtain ⟨s, C, -, hC⟩ := Seminorm.bound_of_continuous hpW _ hqk
      obtain ⟨r, -, hr⟩ := (hpW.isVonNBounded_iff_finset_seminorm_bounded).1 hB'' s
      refine ⟨C * r, ?_⟩
      rintro _ ⟨_, ⟨z, hz, rfl⟩, rfl⟩
      have h1 := hC z
      have h2 := (hr z hz).le
      simp only [Seminorm.comp_apply, Seminorm.smul_apply, NNReal.smul_def, smul_eq_mul] at h1
      calc q k (Submodule.inclusion inf_le_left z) ≤ (C : ℝ) * (s.sup (p.comp (V ⊓ X n).subtype)) z := h1
        _ ≤ C * r := by gcongr
    exact @WithSeminorms.continuous_of_continuous_comp ℂ ℂ V V κ _ _ _ _ _ _ (RingHom.id ℂ) _ q
      instTopologicalSpaceSubtype _ t hq LinearMap.id (fun k => key k)
  · refine sInf_le ⟨⟨ι, hι, p.comp V.subtype, hpV⟩, fun n => ?_⟩
    exact continuous_induced_rng.2 continuous_subtype_val
