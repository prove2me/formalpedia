-- Prove2me | solution 1 for MasulloGRH.strongDual_isMontel_of_isMontel
-- status  : ACCEPTED   (prove)
-- author  : @Miikka
-- created : 2026-11-21T12:07:14.845801+00:00
-- url     : https://prove2.me/submissions/d4407f5b-cc95-487c-891b-632af76ccbdc

import Definitions.Def_MasulloGRH_LocallyConvex
import Theorems.Thm_MasulloGRH_strongDual_isHLCS
import Theorems.Thm_MasulloGRH_strongDual_barrelledSpace_of_semiReflexive

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MasulloGRH Topology Filter Set

noncomputable section

-- The evaluation-map lemmas below are taken from the accepted platform proof of
-- `MasulloGRH.nuclear_barrelled_quasiComplete_isMontel` (submission 721764c1).


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


private theorem montel_dual_compact {E : Type*} [AddCommGroup E] [Module ℂ E]
    [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℂ E] [T2Space E]
    [BarrelledSpace ℂ E]
    (hMc : ∀ B : Set E, IsClosed B → Bornology.IsVonNBounded ℂ B → IsCompact B)
    (A : Set (StrongDual ℂ E)) (hAc : IsClosed A) (hAb : Bornology.IsVonNBounded ℂ A) :
    IsCompact A := by
  -- Banach–Steinhaus: a continuous seminorm dominating every member of `A`
  let p : A → Seminorm ℂ E := fun f => (normSeminorm ℂ ℂ).comp f.1.toLinearMap
  have hb : BddAbove (Set.range p) := by
    apply Seminorm.bddAbove_range_iff.mpr
    intro x
    let ev : StrongDual ℂ E →L[ℂ] ℂ :=
      ⟨(topDualPairing ℂ E).flip x, continuous_eval_const x⟩
    obtain ⟨R, hR⟩ := (NormedSpace.isVonNBounded_iff' ℂ).mp (hAb.image ev)
    refine ⟨R, ?_⟩
    rintro _ ⟨f, rfl⟩
    exact hR _ (Set.mem_image_of_mem ev f.2)
  let q : Seminorm ℂ E := ⨆ f, p f
  have hqc : Continuous q := by
    simpa only [q, Seminorm.coe_iSup_eq hb] using
      (Seminorm.continuous_iSup p (fun f => f.1.continuous.norm) hb)
  have hq : ∀ f ∈ A, ∀ x, ‖f x‖ ≤ q x := by
    intro f hf x
    change ‖f x‖ ≤ (⨆ f, p f) x
    rw [Seminorm.iSup_apply hb]
    exact le_ciSup (Seminorm.bddAbove_range_iff.mp hb x) ⟨f, hf⟩
  rw [isCompact_iff_ultrafilter_le_nhds]
  intro 𝓤 hA𝓤
  have hAmem : A ∈ (𝓤 : Filter (StrongDual ℂ E)) := le_principal_iff.1 hA𝓤
  -- pointwise limits
  have hpt : ∀ x : E, ∃ c : ℂ, Tendsto (fun f : StrongDual ℂ E => f x) 𝓤 (𝓝 c) := by
    intro x
    obtain ⟨c, -, hc⟩ := (isCompact_closedBall (0 : ℂ) (q x)).ultrafilter_le_nhds
      (Ultrafilter.map (fun f : StrongDual ℂ E => f x) 𝓤) (by
        rw [Ultrafilter.coe_map, le_principal_iff]
        exact Filter.mem_map.2 (Filter.mem_of_superset hAmem
          (fun f hf => mem_closedBall_zero_iff.2 (hq f hf x))))
    rw [Ultrafilter.coe_map] at hc
    exact ⟨c, hc⟩
  choose T0 hT0 using hpt
  have hadd : ∀ x y, T0 (x + y) = T0 x + T0 y := fun x y =>
    tendsto_nhds_unique (hT0 (x + y)) (by simpa using (hT0 x).add (hT0 y))
  have hsmul : ∀ (c : ℂ) x, T0 (c • x) = c • T0 x := fun c x =>
    tendsto_nhds_unique (hT0 (c • x)) (by simpa using (hT0 x).const_smul c)
  let L : E →ₗ[ℂ] ℂ := { toFun := T0, map_add' := hadd, map_smul' := hsmul }
  have hLq : ∀ x, ‖L x‖ ≤ q x := fun x =>
    le_of_tendsto (hT0 x).norm (Filter.mem_of_superset hAmem (fun f hf => hq f hf x))
  have hLc : Continuous L := by
    have hc : Continuous ((normSeminorm ℂ ℂ).comp L) :=
      Seminorm.continuous_of_le hqc (fun x => hLq x)
    refine continuous_of_continuousAt_zero L.toAddMonoidHom ?_
    rw [ContinuousAt, map_zero, tendsto_zero_iff_norm_tendsto_zero]
    have := hc.tendsto 0
    rw [map_zero] at this
    exact this.congr (fun x => rfl)
  let T : StrongDual ℂ E := ⟨L, hLc⟩
  have hTq : ∀ x, ‖T x‖ ≤ q x := hLq
  have hbasis := ContinuousLinearMap.hasBasis_nhds_zero (𝕜₁ := ℂ) (σ := RingHom.id ℂ)
    (E := E) (F := ℂ)
  have hconv : (𝓤 : Filter (StrongDual ℂ E)) ≤ 𝓝 T := by
    rw [← map_add_left_nhds_zero T]
    intro W hW
    rw [mem_map] at hW
    obtain ⟨⟨B, V⟩, ⟨hB, hV⟩, hsub⟩ := hbasis.mem_iff.1 hW
    obtain ⟨ε, hε, hεV⟩ := Metric.mem_nhds_iff.1 hV
    have hK : IsCompact (closure B) := hMc _ isClosed_closure hB.closure
    obtain ⟨t, -, hcov⟩ := hK.elim_nhds_subcover (fun x => {y | q (y - x) < ε / 3}) (by
      intro x _
      have hc : Continuous (fun y => q (y - x)) := hqc.comp (continuous_id.sub continuous_const)
      exact hc.continuousAt.preimage_mem_nhds
        (Iio_mem_nhds (show q (x - x) < ε / 3 by rw [sub_self, map_zero]; positivity)))
    have hev : ∀ᶠ f in (𝓤 : Filter (StrongDual ℂ E)), ∀ i ∈ t, ‖f i - T i‖ < ε / 3 := by
      rw [eventually_all_finset]
      intro i _
      have := (hT0 i).eventually (Metric.ball_mem_nhds (T0 i) (by positivity : 0 < ε / 3))
      filter_upwards [this] with f hf
      rw [dist_eq_norm] at hf
      exact hf
    filter_upwards [hev, hAmem] with f hf hfA
    have hm : f - T ∈ {h : StrongDual ℂ E | ∀ x ∈ B, h x ∈ V} := by
      intro x hx
      obtain ⟨i, hi, hxi⟩ : ∃ i ∈ t, q (x - i) < ε / 3 := by
        simpa using hcov (subset_closure hx)
      apply hεV
      rw [Metric.mem_ball, dist_zero_right]
      have e : (f - T) x = f (x - i) + (f i - T i) - T (x - i) := by
        simp only [ContinuousLinearMap.sub_apply, map_sub]; ring
      rw [e]
      have h1 : ‖f (x - i)‖ < ε / 3 := (hq f hfA _).trans_lt hxi
      have h2 : ‖f i - T i‖ < ε / 3 := hf i hi
      have h3 : ‖T (x - i)‖ < ε / 3 := (hTq _).trans_lt hxi
      calc ‖f (x - i) + (f i - T i) - T (x - i)‖
          ≤ ‖f (x - i) + (f i - T i)‖ + ‖T (x - i)‖ := norm_sub_le _ _
        _ ≤ ‖f (x - i)‖ + ‖f i - T i‖ + ‖T (x - i)‖ := by
          gcongr; exact norm_add_le _ _
        _ < ε := by linarith
    have := hsub hm
    simpa using this
  exact ⟨T, hAc.mem_of_tendsto (tendsto_id'.2 hconv) hAmem, hconv⟩

private theorem barrelled_strongBidualTopology (F : Type*) [AddCommGroup F] [Module ℂ F]
    [TopologicalSpace F] [IsTopologicalAddGroup F] [ContinuousSMul ℂ F]
    [BarrelledSpace ℂ F] [PolynormableSpace ℂ F] :
    ‹TopologicalSpace F› = strongBidualTopology F := by
  have hJ : IsInducing (evalMap F) := evalMap_isInducing
  have hU := (ContinuousLinearMap.isUniformEmbedding_toUniformOnFun
      (σ := RingHom.id ℂ) (E := StrongDual ℂ F) (F := ℂ)).isEmbedding.isInducing
  exact (hU.comp hJ).eq_induced

theorem solution (E : Type*) [AddCommGroup E] [Module ℂ E]
    [TopologicalSpace E] (hb : BarrelledSpace ℂ E) (hM : IsMontel E) :
    IsMontel (StrongDual ℂ E) := by
  obtain ⟨hHL, hMc, hR1, hR2⟩ := hM
  obtain ⟨ι, _, pE, hpE⟩ := hHL.1
  haveI := hHL.2
  haveI := hpE.topologicalAddGroup
  haveI := hpE.continuousSMul
  haveI := hpE.toPolynormableSpace
  have hD := strongDual_isHLCS E hHL
  obtain ⟨κ, _, pD, hpD⟩ := hD.1
  haveI : BarrelledSpace ℂ (StrongDual ℂ E) :=
    strongDual_barrelledSpace_of_semiReflexive E hHL hR1
  haveI := hpD.toPolynormableSpace
  haveI := hpD.continuousSMul
  haveI := hpD.topologicalAddGroup
  refine ⟨hD, fun A hAc hAb => montel_dual_compact hMc A hAc hAb, ?_, ?_⟩
  · intro φ
    let J : E →L[ℂ] StrongDual ℂ (StrongDual ℂ E) := ⟨evalMap E, evalMap_continuous E⟩
    let f : StrongDual ℂ E := φ.comp J
    refine ⟨f, fun Ψ => ?_, fun g hg => ?_⟩
    · obtain ⟨x, hx, -⟩ := hR1 Ψ
      have : Ψ = J x := by ext h; exact hx h
      rw [this]
      rfl
    · ext x
      exact (hg (J x)).symm
  · exact barrelled_strongBidualTopology (StrongDual ℂ E)
