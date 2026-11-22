-- Prove2me | solution 1 for MasulloGRH.strongDual_isCompleteTVS_of_bornological
-- status  : ACCEPTED   (prove)
-- author  : @Miikka
-- created : 2026-11-21T10:35:26.98184+00:00
-- url     : https://prove2.me/submissions/2ea482ab-e613-4303-b560-0cb21e6aa78b

import Definitions.Def_MasulloGRH_LocallyConvex

set_option autoImplicit false

open MasulloGRH Topology Filter Uniformity Pointwise

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
    [TopologicalSpace E] (hE : IsHLCS E) (hb : IsBornological E) :
    IsCompleteTVS (StrongDual ℂ E) := by
  obtain ⟨h1, h2⟩ := lc_tvs hE.1
  have hbasis := ContinuousLinearMap.hasBasis_nhds_zero (𝕜₁ := ℂ) (σ := RingHom.id ℂ)
    (E := E) (F := ℂ)
  have hnb : ∀ B : Set E, Bornology.IsVonNBounded ℂ B → ∀ ε > 0,
      {h : StrongDual ℂ E | ∀ x ∈ B, ‖h x‖ < ε} ∈ 𝓝 (0 : StrongDual ℂ E) := by
    intro B hB ε hε
    have := hbasis.mem_of_mem (i := (B, Metric.ball 0 ε)) ⟨hB, Metric.ball_mem_nhds 0 hε⟩
    simpa [Metric.mem_ball, dist_zero_right] using this
  refine ⟨inferInstance, fun 𝓕 h𝓕 => ?_⟩
  obtain ⟨hne, hC⟩ := h𝓕
  have hU : ∀ B : Set E, Bornology.IsVonNBounded ℂ B → ∀ ε > 0, ∃ A ∈ 𝓕,
      ∀ f ∈ A, ∀ g ∈ A, ∀ x ∈ B, ‖f x - g x‖ < ε := by
    intro B hB ε hε
    obtain ⟨A, hA, hAA⟩ := hC _ (hnb B hB ε hε)
    exact ⟨A, hA, fun f hf g hg x hx => by simpa using hAA f hf g hg x hx⟩
  have hpt : ∀ x : E, ∃ c : ℂ, Tendsto (fun f : StrongDual ℂ E => f x) 𝓕 (𝓝 c) := by
    intro x
    have hc : Cauchy (map (fun f : StrongDual ℂ E => f x) 𝓕) := by
      rw [Metric.cauchy_iff]
      refine ⟨inferInstance, fun ε hε => ?_⟩
      obtain ⟨A, hA, hAA⟩ := hU {x} (Bornology.isVonNBounded_singleton x) ε hε
      refine ⟨_, image_mem_map hA, ?_⟩
      rintro _ ⟨f, hf, rfl⟩ _ ⟨g, hg, rfl⟩
      rw [dist_eq_norm]; exact hAA f hf g hg x rfl
    exact CompleteSpace.complete hc
  choose T0 hT0 using hpt
  have hadd : ∀ x y, T0 (x + y) = T0 x + T0 y := fun x y =>
    tendsto_nhds_unique (hT0 (x + y)) (by simpa using (hT0 x).add (hT0 y))
  have hsmul : ∀ (c : ℂ) x, T0 (c • x) = c • T0 x := fun c x =>
    tendsto_nhds_unique (hT0 (c • x)) (by simpa using (hT0 x).const_smul c)
  let L : E →ₗ[ℂ] ℂ := { toFun := T0, map_add' := hadd, map_smul' := hsmul }
  have hest : ∀ B : Set E, Bornology.IsVonNBounded ℂ B → ∀ ε > 0, ∃ A ∈ 𝓕,
      ∀ f ∈ A, ∀ x ∈ B, ‖f x - T0 x‖ ≤ ε := by
    intro B hB ε hε
    obtain ⟨A, hA, hAA⟩ := hU B hB ε hε
    refine ⟨A, hA, fun f hf x hx => ?_⟩
    have ht : Tendsto (fun g : StrongDual ℂ E => ‖f x - g x‖) 𝓕 (𝓝 ‖f x - T0 x‖) :=
      (tendsto_const_nhds.sub (hT0 x)).norm
    exact le_of_tendsto ht (Filter.mem_of_superset hA fun g hg => (hAA f hf g hg x hx).le)
  have hLb : ∀ B : Set E, Bornology.IsVonNBounded ℂ B →
      BddAbove (((normSeminorm ℂ ℂ).comp L) '' B) := by
    intro B hB
    obtain ⟨A, hA, hAA⟩ := hest B hB 1 one_pos
    obtain ⟨f, hf⟩ := Filter.nonempty_of_mem hA
    obtain ⟨R, hR⟩ := (NormedSpace.isVonNBounded_iff' (𝕜 := ℂ)).1 (hB.image f)
    refine ⟨R + 1, ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    have e1 := hR _ ⟨x, hx, rfl⟩
    have e2 := hAA f hf x hx
    show ‖T0 x‖ ≤ R + 1
    calc ‖T0 x‖ ≤ ‖f x‖ + ‖f x - T0 x‖ := by
          have := norm_sub_le (f x) (f x - T0 x); simpa using this
      _ ≤ R + 1 := add_le_add e1 e2
  have hpc := hb _ hLb
  have hLc : Continuous L := by
    refine continuous_of_continuousAt_zero L.toAddMonoidHom ?_
    rw [ContinuousAt, map_zero, tendsto_zero_iff_norm_tendsto_zero]
    have := hpc.tendsto 0
    rw [map_zero] at this
    exact this.congr (fun x => rfl)
  let T : StrongDual ℂ E := ⟨L, hLc⟩
  refine ⟨T, ?_⟩
  rw [← map_add_left_nhds_zero T]
  intro W hW
  rw [mem_map] at hW
  obtain ⟨⟨B, V⟩, ⟨hB, hV⟩, hsub⟩ := hbasis.mem_iff.1 hW
  obtain ⟨ε, hε, hεV⟩ := Metric.mem_nhds_iff.1 hV
  obtain ⟨A, hA, hAA⟩ := hest B hB (ε / 2) (by positivity)
  refine Filter.mem_of_superset hA fun f hf => ?_
  have hm : f - T ∈ {h : StrongDual ℂ E | ∀ x ∈ B, h x ∈ V} := fun x hx => hεV (by
    rw [Metric.mem_ball, dist_zero_right]
    have := hAA f hf x hx
    show ‖f x - T0 x‖ < ε
    linarith)
  have := hsub hm
  simpa using this
