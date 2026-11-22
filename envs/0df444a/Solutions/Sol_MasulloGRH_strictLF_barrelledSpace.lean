-- Prove2me | solution 1 for MasulloGRH.strictLF_barrelledSpace
-- status  : ACCEPTED   (prove)
-- author  : @Miikka
-- created : 2026-11-21T10:12:12.638019+00:00
-- url     : https://prove2.me/submissions/21757451-26ac-432f-9c0e-f20056be671b

import Definitions.Def_MasulloGRH_LocallyConvex

set_option autoImplicit false

open MasulloGRH Topology Filter Uniformity

namespace BarAux

universe u

lemma lc_tvs {E : Type u} [AddCommGroup E] [Module ℂ E] [t : TopologicalSpace E]
    (h : IsLocallyConvexTopology E t) : IsTopologicalAddGroup E ∧ ContinuousSMul ℂ E := by
  obtain ⟨ι, _, p, hp⟩ := h
  exact ⟨hp.topologicalAddGroup, hp.continuousSMul⟩

lemma frechet_baire {E : Type u} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    (h : IsFrechet E) : BaireSpace E := by
  obtain ⟨hlc, ⟨hT2, hc⟩, hm⟩ := h
  obtain ⟨h1, h2⟩ := lc_tvs hlc
  letI : UniformSpace E := IsTopologicalAddGroup.rightUniformSpace E
  haveI : IsUniformAddGroup E := isUniformAddGroup_of_addCommGroup
  haveI : (𝓤 E).IsCountablyGenerated := IsUniformAddGroup.uniformity_countably_generated
  haveI : CompleteSpace E := by
    refine ⟨fun {f} hf => ?_⟩
    apply hc f
    refine ⟨hf.1, fun U hU => ?_⟩
    have hs : {p : E × E | p.2 - p.1 ∈ U} ∈ 𝓤 E := by
      rw [uniformity_eq_comap_nhds_zero']
      exact ⟨U, hU, fun p hp => by simpa [sub_eq_add_neg] using hp⟩
    obtain ⟨A, hA, hAA⟩ := mem_prod_same_iff.1 (hf.2 hs)
    exact ⟨A, hA, fun x hx y hy => hAA (Set.mk_mem_prod hy hx)⟩
  infer_instance

/-- the topology of a single seminorm -/
noncomputable def sTop {E : Type u} [AddCommGroup E] [Module ℂ E] (p : Seminorm ℂ E) :
    TopologicalSpace E :=
  (SeminormFamily.moduleFilterBasis (𝕜 := ℂ) (fun _ : PUnit.{u+1} => p)).topology

lemma sTop_ws {E : Type u} [AddCommGroup E] [Module ℂ E] (p : Seminorm ℂ E) :
    @WithSeminorms ℂ E PUnit.{u+1} _ _ _ (fun _ => p) (sTop p) := by
  letI := sTop p
  exact ⟨rfl⟩

lemma sTop_lc {E : Type u} [AddCommGroup E] [Module ℂ E] (p : Seminorm ℂ E) :
    IsLocallyConvexTopology E (sTop p) := ⟨PUnit, inferInstance, _, sTop_ws p⟩

lemma sTop_cont_into {E : Type u} [AddCommGroup E] [Module ℂ E] {F : Type*} [AddCommGroup F]
    [Module ℂ F] [TopologicalSpace F] [IsTopologicalAddGroup F] (f : F →ₗ[ℂ] E)
    (p : Seminorm ℂ E) (hf : Continuous (p.comp f)) : @Continuous F E _ (sTop p) f := by
  letI := sTop p
  exact WithSeminorms.continuous_of_continuous_comp (sTop_ws p) f (fun _ => hf)

lemma sTop_cont {E : Type u} [AddCommGroup E] [Module ℂ E] (p : Seminorm ℂ E) :
    @Continuous E ℝ (sTop p) _ p := by
  letI := sTop p
  exact WithSeminorms.continuous_seminorm (sTop_ws p) PUnit.unit

end BarAux

open BarAux in
theorem solution (E : Type*) [AddCommGroup E] [Module ℂ E]
    [TopologicalSpace E] (hE : IsStrictLF E) : BarrelledSpace ℂ E := by
  obtain ⟨X, hmono, hexh, hX, htop⟩ := hE
  refine ⟨fun p hp => ?_⟩
  have hmem : sTop p ∈ {t | IsLocallyConvexTopology E t ∧
      ∀ n, @Continuous (X n) E _ t Subtype.val} := by
    refine ⟨sTop_lc p, fun n => ?_⟩
    obtain ⟨h1, h2⟩ := lc_tvs (hX n).1
    haveI : BaireSpace (X n) := frechet_baire (hX n)
    have hpn : Continuous (p.comp (X n).subtype) := by
      apply Seminorm.continuous_of_lowerSemicontinuous
      exact hp.comp continuous_subtype_val
    exact sTop_cont_into ((X n).subtype) p hpn
  have hle : ‹TopologicalSpace E› ≤ sTop p := htop ▸ sInf_le hmem
  exact @Continuous.comp _ _ _ _ (sTop p) _ _ _ (sTop_cont p) (continuous_id_of_le hle)
