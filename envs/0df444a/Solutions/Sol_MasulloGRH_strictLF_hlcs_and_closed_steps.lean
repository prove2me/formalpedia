-- Prove2me | solution 1 for MasulloGRH.strictLF_hlcs_and_closed_steps
-- status  : ACCEPTED   (prove)
-- author  : @nlehmann
-- created : 2026-11-20T22:55:59.899205+00:00
-- url     : https://prove2.me/submissions/6dc81bbe-1f67-4d17-9a6f-577c559f35e0

import Definitions.Def_MasulloGRH_LocallyConvex

open Topology Filter

universe u

/-- The indiscrete topology is the seminorm topology of the zero seminorm. -/
theorem MasulloGRH_zero_seminorm_top (E : Type u) [AddCommGroup E] [Module ℂ E] :
    @WithSeminorms ℂ E PUnit.{u+1} _ _ _ (fun _ => 0) ⊤ := by
  letI : TopologicalSpace E := ⊤
  have : IsTopologicalAddGroup E :=
    { continuous_add := continuous_top, continuous_neg := continuous_top }
  rw [SeminormFamily.withSeminorms_iff_topologicalSpace_eq_iInf]
  simp only [ciInf_const]
  symm
  rw [eq_top_iff]
  intro s hs
  rw [TopologicalSpace.isOpen_top_iff]
  rcases s.eq_empty_or_nonempty with h | ⟨x, hx⟩
  · exact Or.inl h
  · right
    letI := (0 : Seminorm ℂ E).toSeminormedAddCommGroup
    rw [Metric.isOpen_iff] at hs
    obtain ⟨ε, hε, hball⟩ := hs x hx
    refine Set.eq_univ_of_forall fun y => hball ?_
    rw [Metric.mem_ball, dist_eq_norm]
    change (0 : Seminorm ℂ E) (y - x) < ε
    simpa using hε

/-- An infimum of locally convex topologies is locally convex. -/
theorem MasulloGRH_lc_sInf {E : Type u} [AddCommGroup E] [Module ℂ E]
    (S : Set (TopologicalSpace E))
    (hS : ∀ t ∈ S, MasulloGRH.IsLocallyConvexTopology E t) :
    MasulloGRH.IsLocallyConvexTopology E (sInf S) := by
  have hS' : ∀ t ∈ insert (⊤ : TopologicalSpace E) S, MasulloGRH.IsLocallyConvexTopology E t := by
    rintro t (rfl | ht)
    · exact ⟨PUnit, inferInstance, fun _ => 0, MasulloGRH_zero_seminorm_top E⟩
    · exact hS t ht
  have heq : sInf S = sInf (insert (⊤ : TopologicalSpace E) S) := by
    rw [sInf_insert, top_inf_eq]
  rw [heq]
  set T := insert (⊤ : TopologicalSpace E) S
  let κ : T → Type u := fun t => (hS' t.1 t.2).choose
  have hκ : ∀ t : T, Nonempty (κ t) := fun t => (hS' t.1 t.2).choose_spec.choose
  let p : (t : T) → SeminormFamily ℂ E (κ t) :=
    fun t => (hS' t.1 t.2).choose_spec.choose_spec.choose
  have hp : ∀ t : T, @WithSeminorms ℂ E (κ t) _ _ _ (p t) t.1 :=
    fun t => (hS' t.1 t.2).choose_spec.choose_spec.choose_spec
  have htop : sInf T = ⨅ t : T, t.1 := sInf_eq_iInf' T
  rw [htop]
  refine ⟨(t : T) × κ t, ?_, SeminormFamily.sigma p, withSeminorms_iInf hp⟩
  obtain ⟨t0⟩ : Nonempty T := ⟨⟨⊤, Set.mem_insert _ _⟩⟩
  obtain ⟨k⟩ := hκ t0
  exact ⟨⟨t0, k⟩⟩

open MasulloGRH

theorem solution (E : Type*) [AddCommGroup E] [Module ℂ E]
    [TopologicalSpace E] (X : ℕ → Submodule ℂ E) (hmono : Monotone X)
    (hexh : ∀ x : E, ∃ n, x ∈ X n) (hX : ∀ n, IsFrechet (X n))
    (htop : ‹TopologicalSpace E› =
      sInf {t | IsLocallyConvexTopology E t ∧ ∀ n, @Continuous (X n) E _ t Subtype.val}) :
    IsHLCS E ∧ ∀ n, IsClosed (X n : Set E) := by
  -- local convexity
  have hlc : IsLocallyConvexTopology E ‹TopologicalSpace E› := by
    rw [htop]
    exact MasulloGRH_lc_sInf _ (fun t ht => ht.1)
  obtain ⟨ι, _, p, hp⟩ := hlc
  have hgrp : IsTopologicalAddGroup E := hp.topologicalAddGroup
  -- Hausdorff
  have hT2 : T2Space E := by
    apply IsTopologicalAddGroup.t2Space_of_zero_sep
    intro x hx
    obtain ⟨n, hn⟩ := hexh x
    have hT2n : T2Space (X n) := (hX n).2.1.1
    have hne : (⟨x, hn⟩ : X n) ≠ 0 := fun h => hx (congrArg Subtype.val h)
    have hU : ({⟨x, hn⟩}ᶜ : Set (X n)) ∈ 𝓝 (0 : X n) :=
      isOpen_compl_singleton.mem_nhds (by simpa [eq_comm] using hne)
    obtain ⟨U, hU0, hUsub⟩ := (mem_nhds_induced Subtype.val (0 : X n) _).1 hU
    refine ⟨U, by simpa using hU0, fun hxU => ?_⟩
    exact hUsub (show (⟨x, hn⟩ : X n) ∈ Subtype.val ⁻¹' U from hxU) rfl
  refine ⟨⟨⟨ι, ‹_›, p, hp⟩, hT2⟩, fun n => ?_⟩
  -- closedness of the steps via completeness
  apply isClosed_of_closure_subset
  intro x hx
  have hNe : (comap (Subtype.val : X n → E) (𝓝 x)).NeBot := mem_closure_iff_comap_neBot.1 hx
  have hcauchy : IsCauchyFilter (comap (Subtype.val : X n → E) (𝓝 x)) := by
    refine ⟨hNe, fun U hU => ?_⟩
    obtain ⟨W, hW0, hWsub⟩ := (mem_nhds_induced Subtype.val (0 : X n) U).1 hU
    have hsub : Tendsto (fun q : E × E => q.1 - q.2) (𝓝 ((0 : E), (0 : E))) (𝓝 0) := by
      simpa using (continuous_sub.tendsto ((0 : E), (0 : E)))
    have hpre := hsub (show W ∈ 𝓝 (0 : E) by simpa using hW0)
    rw [nhds_prod_eq, mem_map, mem_prod_iff] at hpre
    obtain ⟨t1, ht1, t2, ht2, hprod⟩ := hpre
    set W' := t1 ∩ t2
    have hW'x : {z : E | z - x ∈ W'} ∈ 𝓝 x := by
      have hc : ContinuousAt (fun z : E => z - x) x := (continuous_id.sub continuous_const).continuousAt
      have : W' ∈ 𝓝 ((fun z : E => z - x) x) := by
        show W' ∈ 𝓝 (x - x)
        rw [sub_self]; exact inter_mem ht1 ht2
      exact hc.preimage_mem_nhds this
    refine ⟨Subtype.val ⁻¹' {z : E | z - x ∈ W'}, preimage_mem_comap hW'x, ?_⟩
    intro a ha b hb
    apply hWsub
    have hab : ((a : E) - x, (b : E) - x) ∈ t1 ×ˢ t2 := ⟨ha.1, hb.2⟩
    have := hprod hab
    simp only [Set.mem_preimage] at this
    simpa using this
  obtain ⟨y, hy⟩ := (hX n).2.1.2 _ hcauchy
  have h1 : map (Subtype.val : X n → E) (comap Subtype.val (𝓝 x)) ≤ 𝓝 x := map_comap_le
  have h2 : map (Subtype.val : X n → E) (comap Subtype.val (𝓝 x)) ≤ 𝓝 (y : E) :=
    (map_mono hy).trans continuous_subtype_val.continuousAt
  have hxy : x = y := by
    haveI : (map (Subtype.val : X n → E) (comap Subtype.val (𝓝 x))).NeBot := hNe.map _
    exact tendsto_nhds_unique h1 h2
  rw [hxy]
  exact y.2
