-- Prove2me | solution 1 for MasulloGRH.isFrechet_and_isNuclear_of_countable_projective
-- status  : ACCEPTED   (prove)
-- author  : @sflicht
-- created : 2026-11-21T17:58:16.523713+00:00
-- url     : https://prove2.me/submissions/2fff59c3-81f0-479f-8b6d-cacf49ab13a4

import Theorems.Thm_MasulloGRH_nuclear_of_projective_topology

set_option autoImplicit false

universe u

open MasulloGRH Topology Filter

theorem solution (ι : Type u) [Countable ι] [Nonempty ι] (Y : ι → Type u)
    [∀ i, AddCommGroup (Y i)] [∀ i, Module ℂ (Y i)] [∀ i, TopologicalSpace (Y i)]
    (hY : ∀ i, IsFrechet (Y i) ∧ IsNuclear (Y i))
    (E : Type u) [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    (π : ∀ i, E →ₗ[ℂ] Y i)
    (htop : ‹TopologicalSpace E› = ⨅ i, TopologicalSpace.induced (π i) inferInstance)
    (hsep : ∀ x : E, (∀ i, π i x = 0) → x = 0)
    (hclosed : IsClosed (Set.range fun x : E => fun i => π i x)) :
    IsFrechet E ∧ IsNuclear E := by
  refine ⟨?_, nuclear_of_projective_topology ι Y (fun i => (hY i).2) E π htop hsep⟩
  choose κ hκ p hp using fun i => (hY i).1.1
  haveI : ∀ i, T2Space (Y i) := fun i => (hY i).1.2.1.1
  haveI : ∀ i, TopologicalSpace.MetrizableSpace (Y i) := fun i => (hY i).1.2.2
  haveI : ∀ i, IsTopologicalAddGroup (Y i) := fun i => (hp i).topologicalAddGroup
  have hcont : ∀ i, Continuous (π i) := fun i => by
    rw [continuous_iff_le_induced, htop]; exact iInf_le _ i
  set Φ : E → (∀ i, Y i) := fun x i => π i x with hΦ
  have hind : IsInducing Φ := by
    constructor
    rw [htop, Pi.topologicalSpace, induced_iInf]
    simp only [induced_compose]
    rfl
  have hinj : Function.Injective Φ := by
    intro x y hxy
    have := hsep (x - y) fun i => by
      rw [map_sub, sub_eq_zero]; exact congrFun hxy i
    exact sub_eq_zero.1 this
  have hemb : IsEmbedding Φ := ⟨hind, hinj⟩
  haveI : Nonempty (Σ i, κ i) := by
    obtain ⟨i⟩ := ‹Nonempty ι›
    obtain ⟨j⟩ := hκ i
    exact ⟨⟨i, j⟩⟩
  have hws : WithSeminorms (SeminormFamily.sigma (fun i => (p i).comp (π i))) := by
    have h := withSeminorms_iInf (t := fun i => TopologicalSpace.induced (π i) inferInstance)
      (fun i => LinearMap.withSeminorms_induced (hp i) (π i))
    rw [htop]
    exact h
  haveI : T2Space E := hemb.t2Space
  have hmet : TopologicalSpace.MetrizableSpace E := by
    haveI : IsTopologicalAddGroup E := hws.topologicalAddGroup
    letI : UniformSpace E := IsTopologicalAddGroup.rightUniformSpace E
    haveI : IsUniformAddGroup E := isUniformAddGroup_of_addCommGroup
    haveI : (𝓝 (0 : E)).IsCountablyGenerated := by
      rw [hind.nhds_eq_comap]
      infer_instance
    haveI : (uniformity E).IsCountablyGenerated := IsUniformAddGroup.uniformity_countably_generated
    exact UniformSpace.metrizableSpace
  refine ⟨⟨Σ i, κ i, inferInstance, _, hws⟩, ⟨inferInstance, fun f hf => ?_⟩,
    hmet⟩
  obtain ⟨hne, hc⟩ := hf
  have hlim : ∀ i, ∃ y, map (π i) f ≤ 𝓝 y := fun i =>
    (hY i).1.2.1.2 _ ⟨Filter.map_neBot, fun U hU => by
      obtain ⟨A, hA, hAU⟩ := hc _ ((hcont i).tendsto 0 (by rw [map_zero]; exact hU))
      refine ⟨π i '' A, image_mem_map hA, ?_⟩
      rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
      rw [← map_sub]; exact hAU x hx y hy⟩
  choose y hy using hlim
  have hT : Tendsto Φ f (𝓝 y) := tendsto_pi_nhds.2 hy
  have hmem : y ∈ Set.range Φ := hclosed.closure_subset
    (mem_closure_of_tendsto hT (Eventually.of_forall fun x => ⟨x, rfl⟩))
  obtain ⟨x, rfl⟩ := hmem
  exact ⟨x, hind.tendsto_nhds_iff.2 hT⟩
