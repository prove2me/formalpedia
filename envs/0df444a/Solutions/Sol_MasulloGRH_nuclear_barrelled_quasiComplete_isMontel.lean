-- Prove2me | solution 1 for MasulloGRH.nuclear_barrelled_quasiComplete_isMontel
-- status  : ACCEPTED   (prove)
-- author  : @ghseeli
-- created : 2026-11-21T00:00:01.386796+00:00
-- url     : https://prove2.me/submissions/721764c1-3bb7-40b6-b4b8-56d3fbd31497

import Theorems.Thm_MasulloGRH_nuclear_bounded_precompact
import Theorems.Thm_MasulloGRH_quasiCompleteNuclear_strongBidual_bounded_repr
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MasulloGRH Topology Filter Set

noncomputable section

private theorem seminorm_norming {E : Type*} [AddCommGroup E] [Module ℂ E]
    (p : Seminorm ℂ E) (x : E) :
    ∃ f : E →ₗ[ℂ] ℂ, (∀ y, ‖f y‖ ≤ p y) ∧ ‖f x‖ = p x := by
  let _ : SeminormedAddCommGroup E := p.toSeminormedAddCommGroup
  let _ : NormedSpace ℂ E := { norm_smul_le := fun a b => (map_smul_eq_mul p a b).le }
  obtain ⟨f, hf, hx⟩ := exists_dual_vector'' ℂ x
  refine ⟨f.toLinearMap, fun y => ?_, ?_⟩
  · change ‖f y‖ ≤ ‖y‖
    exact (f.le_opNorm y).trans (by simpa using mul_le_mul_of_nonneg_right hf (norm_nonneg y))
  · change ‖f x‖ = ‖x‖
    rw [hx]
    simp only [RCLike.norm_ofReal, abs_of_nonneg (norm_nonneg x)]

private theorem norming_functional {E : Type*} [AddCommGroup E] [Module ℂ E]
    [TopologicalSpace E] [PolynormableSpace ℂ E]
    (p : Seminorm ℂ E) (hp : Continuous p) (x : E) :
    ∃ f : StrongDual ℂ E, (∀ y, ‖f y‖ ≤ p y) ∧ ‖f x‖ = p x := by
  obtain ⟨f, hf, hx⟩ := seminorm_norming p x
  have hc : Continuous f := (PolynormableSpace.withSeminorms ℂ E).continuous_normedSpace_rng ℂ f
    ⟨{⟨p, hp⟩}, 1, by simpa using (show (normSeminorm ℂ ℂ).comp f ≤ p from hf)⟩
  exact ⟨⟨f, hc⟩, hf, hx⟩

private def evalMap (E : Type*) [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    [ContinuousSMul ℂ E] : E →ₗ[ℂ] StrongDual ℂ (StrongDual ℂ E) where
  toFun x := { toLinearMap := (topDualPairing ℂ E).flip x
               cont := continuous_eval_const x }
  map_add' x y := by ext f; exact f.map_add x y
  map_smul' c x := by ext f; exact f.map_smul c x

private theorem evalMap_continuous (E : Type*) [AddCommGroup E] [Module ℂ E]
    [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℂ E]
    [BarrelledSpace ℂ E] : Continuous (evalMap E) := by
  have : ContinuousAdd (StrongDual ℂ (StrongDual ℂ E)) :=
    (ContinuousLinearMap.topologicalAddGroup (σ := RingHom.id ℂ) (E := StrongDual ℂ E) (F := ℂ)).toContinuousAdd
  apply continuous_of_tendsto_nhds_zero (evalMap E)
  rw [(ContinuousLinearMap.hasBasis_nhds_zero_of_basis
    (σ := RingHom.id ℂ) (E := StrongDual ℂ E) (F := ℂ) Metric.nhds_basis_ball).tendsto_right_iff]
  rintro ⟨B, r⟩ ⟨hB, hr⟩
  let p : B → Seminorm ℂ E := fun f => (normSeminorm ℂ ℂ).comp f.1.toLinearMap
  have hb : BddAbove (Set.range p) := by
    apply Seminorm.bddAbove_range_iff.mpr
    intro x
    let ev : StrongDual ℂ E →L[ℂ] ℂ :=
      ⟨(topDualPairing ℂ E).flip x, continuous_eval_const x⟩
    obtain ⟨R, hR⟩ := (NormedSpace.isVonNBounded_iff' ℂ).mp (hB.image ev)
    refine ⟨R, ?_⟩
    rintro _ ⟨f, rfl⟩
    exact hR _ (Set.mem_image_of_mem ev f.2)
  let q : Seminorm ℂ E := ⨆ f, p f
  have hc : Continuous q := by
    simpa only [q, Seminorm.coe_iSup_eq hb] using
      (Seminorm.continuous_iSup p (fun f => f.1.continuous.norm) hb)
  have hs : ∀ᶠ x in nhds (0 : E), q x < r :=
    (hc.tendsto 0).eventually (eventually_lt_nhds (by simpa using hr))
  filter_upwards [hs] with x hx
  intro f hf
  change dist (f x) 0 < r
  rw [dist_zero_right]
  apply lt_of_le_of_lt _ hx
  change ‖f x‖ ≤ (⨆ f, p f) x
  rw [Seminorm.iSup_apply hb]
  exact le_ciSup (Seminorm.bddAbove_range_iff.mp hb x) ⟨f, hf⟩

private theorem dominated_functionals_bounded {E : Type*} [AddCommGroup E] [Module ℂ E]
    [TopologicalSpace E] [PolynormableSpace ℂ E]
    (p : Seminorm ℂ E) (hp : Continuous p) :
    Bornology.IsVonNBounded ℂ {f : StrongDual ℂ E | ∀ x, ‖f x‖ ≤ p x} := by
  apply ContinuousLinearMap.isVonNBounded_iff.mpr
  intro s hs
  obtain ⟨r, hr, hbound⟩ :=
    (PolynormableSpace.withSeminorms ℂ E).isVonNBounded_iff_seminorm_bounded.mp hs ⟨p, hp⟩
  apply (NormedSpace.isVonNBounded_iff' ℂ).mpr
  refine ⟨r, ?_⟩
  rintro _ ⟨f, hf, x, hx, rfl⟩
  exact (hf x).trans (hbound x hx).le

private theorem evalMap_isInducing {E : Type*} [AddCommGroup E] [Module ℂ E]
    [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℂ E]
    [BarrelledSpace ℂ E] [PolynormableSpace ℂ E] : IsInducing (evalMap E) := by
  rw [IsTopologicalAddGroup.isInducing_iff_nhds_zero]
  apply le_antisymm
  · simpa using ((evalMap_continuous E).continuousAt (x := 0)).tendsto.le_comap
  · let P := PolynormableSpace.withSeminorms ℂ E
    rw [P.hasBasis_zero_ball.ge_iff]
    rintro ⟨s, r⟩ hr
    let p : Seminorm ℂ E := s.sup (fun q : {q : Seminorm ℂ E // Continuous q} => q.1)
    have hp : Continuous p := Seminorm.continuous_finsetSup (fun q _ => q.2)
    let B : Set (StrongDual ℂ E) := {f | ∀ x, ‖f x‖ ≤ p x}
    have hB : Bornology.IsVonNBounded ℂ B := dominated_functionals_bounded p hp
    have hN := ContinuousLinearMap.eventually_nhds_zero_mapsTo (σ := RingHom.id ℂ) hB
      (Metric.ball_mem_nhds (0 : ℂ) hr)
    apply Filter.mem_of_superset (Filter.preimage_mem_comap hN)
    intro x hx
    change p (x - 0) < r
    rw [sub_zero]
    obtain ⟨f, hf, hfx⟩ := norming_functional p hp x
    have hval := hx hf
    change dist (f x) 0 < r at hval
    simpa [dist_zero_right, hfx] using hval

private theorem nuclear_compact_closed_bounded {E : Type*} [AddCommGroup E] [Module ℂ E]
    [TopologicalSpace E] (hE : IsQuasiComplete E) (hN : IsNuclear E)
    (S : Set E) (hc : IsClosed S) (hb : Bornology.IsVonNBounded ℂ S) : IsCompact S := by
  obtain ⟨ι, hι, p, hp⟩ := hN.1.1
  have : IsTopologicalAddGroup E := hp.topologicalAddGroup
  have : ContinuousSMul ℂ E := hp.continuousSMul
  have : T2Space E := hE.1
  let _ : UniformSpace E := IsTopologicalAddGroup.rightUniformSpace E
  have : IsUniformAddGroup E := isUniformAddGroup_of_addCommGroup
  have hcomplete : IsComplete S := by
    intro f hf hfs
    have hSf : S ∈ f := Filter.le_principal_iff.mp hfs
    have hcauchy : IsCauchyFilter f := by
      obtain ⟨hne, ht⟩ := (IsUniformAddGroup.cauchy_iff_tendsto f).mp hf
      refine ⟨hne, ?_⟩
      intro U hU
      obtain ⟨A, hA, B, hB, hAB⟩ := Filter.mem_prod_iff.mp (ht hU)
      exact ⟨A ∩ B, inter_mem hA hB,
        fun x hx y hy => hAB (show (x,y) ∈ A ×ˢ B from ⟨hx.1, hy.2⟩)⟩
    obtain ⟨x, hx⟩ := hE.2 f hcauchy ⟨S, hSf, hb⟩
    have : f.NeBot := hf.1
    exact ⟨x, hc.mem_of_tendsto hx hSf, hx⟩
  apply TotallyBounded.isCompact_of_isComplete (hc := hcomplete)
  rw [totallyBounded_iff_subset_finite_iUnion_nhds_zero]
  intro U hU
  obtain ⟨t, ht⟩ := MasulloGRH.nuclear_bounded_precompact E hN S hb U hU
  refine ⟨t, t.finite_toSet, ?_⟩
  intro x hx
  obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.mp (ht hx)
  apply Set.mem_iUnion₂.mpr ⟨y, hy, ?_⟩
  exact ⟨x - y, hxy, by simp⟩


theorem solution (E : Type*) [AddCommGroup E] [Module ℂ E]
    [TopologicalSpace E] [BarrelledSpace ℂ E] (hE : IsQuasiComplete E) (hN : IsNuclear E) : IsMontel E := by
  obtain ⟨ι, hι, p, hp⟩ := hN.1.1
  have : T2Space E := hE.1
  have : IsTopologicalAddGroup E := hp.topologicalAddGroup
  have : ContinuousSMul ℂ E := hp.continuousSMul
  have : PolynormableSpace ℂ E := hp.toPolynormableSpace
  have hJ : IsInducing (evalMap E) := evalMap_isInducing
  refine ⟨hN.1, fun S hc hb => nuclear_compact_closed_bounded hE hN S hc hb, ?_⟩
  constructor
  · intro F
    let q : Seminorm ℂ (StrongDual ℂ E) := (normSeminorm ℂ ℂ).comp F.toLinearMap
    have hq : Continuous q := F.continuous.norm
    obtain ⟨D, hD, hrepr⟩ := quasiCompleteNuclear_strongBidual_bounded_repr E hE hN q hq
    obtain ⟨y, hy, he⟩ := hrepr F (fun f => le_rfl)
    refine ⟨y, he, ?_⟩
    intro z hz
    apply hJ.injective
    apply ContinuousLinearMap.ext
    intro f
    exact (hz f).symm.trans (he f)
  · have hU := (ContinuousLinearMap.isUniformEmbedding_toUniformOnFun
        (σ := RingHom.id ℂ) (E := StrongDual ℂ E) (F := ℂ)).isEmbedding.isInducing
    exact (hU.comp hJ).eq_induced
