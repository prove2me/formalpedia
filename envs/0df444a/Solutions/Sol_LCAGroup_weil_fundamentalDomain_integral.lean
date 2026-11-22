-- Prove2me | solution 1 for LCAGroup.weil_fundamentalDomain_integral
-- status  : ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-22T15:49:17.056326+00:00
-- url     : https://prove2.me/submissions/8c9f8470-f6b2-4c62-9437-a688259d3ec7

import Mathlib

open MeasureTheory Topology

set_option autoImplicit false

open scoped Pointwise

theorem solution
    (G : Type*) [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
    [MeasurableSpace G] [BorelSpace G]
    (H : Subgroup G) (hH : IsClosed (H : Set G)) [DiscreteTopology H]
    [MeasurableSpace (G ⧸ H)] [BorelSpace (G ⧸ H)]
    (μ : Measure G) [μ.IsHaarMeasure]
    (ν : Measure (G ⧸ H)) [ν.IsHaarMeasure]
    (hν : ∀ φ : G → ℂ, Continuous φ → HasCompactSupport φ →
      ∫ x, φ x ∂μ =
        ∫ q : G ⧸ H, (∫ h : H, φ (q.out * (h : G)) ∂(Measure.count : Measure H)) ∂ν)
    (Δ : Set G) (hΔ : MeasurableSet Δ)
    (hbij : Function.Bijective (fun x : Δ => ((x : G) : G ⧸ H)))
    (f : G ⧸ H → ℂ) :
    (Integrable f ν ↔ IntegrableOn (fun x : G => f (x : G ⧸ H)) Δ μ) ∧
    ∫ q : G ⧸ H, f q ∂ν = ∫ x in Δ, f (x : G ⧸ H) ∂μ := by
  classical
  have : IsClosed (H : Set G) := hH
  have : Countable H := TopologicalSpace.separableSpace_iff_countable.mp inferInstance
  have : PolishSpace G := by
    let : UniformSpace G := IsTopologicalGroup.rightUniformSpace G
    have : IsUniformGroup G := isUniformGroup_of_commGroup (G := G)
    have : CompleteSpace G :=
      IsRightUniformGroup.completeSpace_of_weaklyLocallyCompactSpace (G := G)
    have := IsUniformGroup.uniformity_countably_generated (α := G)
    infer_instance
  let π : G → G ⧸ H := QuotientGroup.mk
  have hπc : Continuous π := QuotientGroup.continuous_mk
  have hπ : Measurable π := hπc.measurable
  have hπmul : ∀ (h : H) (x : G), π (h • x) = π x := by
    intro h x
    change ((((h : G) * x : G)) : G ⧸ H) = (x : G ⧸ H)
    rw [mul_comm]
    exact QuotientGroup.mk_mul_of_mem x h.property
  have hinvU : ∀ U : Set (G ⧸ H), ∀ h : H, (fun x => h • x) ⁻¹' (π ⁻¹' U) = π ⁻¹' U := by
    intro U h
    ext x
    simp only [Set.mem_preimage, hπmul]
  -- `Δ` is a fundamental domain for the action of `H` by translations
  have hfund : IsFundamentalDomain H Δ μ := by
    apply IsFundamentalDomain.mk' hΔ.nullMeasurableSet
    intro x
    obtain ⟨y, hy⟩ := hbij.surjective (π x)
    let h : H := ⟨x⁻¹ * (y : G), QuotientGroup.eq.mp hy.symm⟩
    have hh : h • x = (y : G) := by
      change (x⁻¹ * (y : G)) * x = (y : G)
      rw [mul_comm, mul_inv_cancel_left]
    refine ⟨h, ?_, ?_⟩
    · change h • x ∈ Δ
      rw [hh]
      exact y.property
    · intro k hk
      have hky : (⟨k • x, hk⟩ : Δ) = y := hbij.injective ((hπmul k x).trans hy.symm)
      have h2 : k • x = h • x := (congrArg Subtype.val hky).trans hh.symm
      have h3 : (k : G) * x = (h : G) * x := h2
      exact Subtype.ext (mul_right_cancel h3)
  -- the restricted projection is a measurable embedding
  have hinj : Set.InjOn π Δ := by
    intro a ha b hb hab
    have := hbij.injective (a₁ := ⟨a, ha⟩) (a₂ := ⟨b, hb⟩) hab
    exact congrArg Subtype.val this
  have hemb : MeasurableEmbedding (Δ.domRestrict π) :=
    ContinuousOn.measurableEmbedding hΔ hπc.continuousOn hinj
  let νΔ : Measure (G ⧸ H) := (μ.restrict Δ).map π
  have hmap : νΔ = Measure.map (Δ.domRestrict π) (μ.comap ((↑) : Δ → G)) := by
    have hsub : (μ.comap ((↑) : Δ → G)).map ((↑) : Δ → G) = μ.restrict Δ := by
      rw [(MeasurableEmbedding.subtype_coe hΔ).map_comap, Subtype.range_coe]
    calc
      νΔ = Measure.map π (μ.restrict Δ) := rfl
      _ = Measure.map π (Measure.map ((↑) : Δ → G) (μ.comap ((↑) : Δ → G))) := by rw [hsub]
      _ = Measure.map (π ∘ ((↑) : Δ → G)) (μ.comap ((↑) : Δ → G)) :=
        Measure.map_map hπ continuous_subtype_val.measurable
      _ = Measure.map (Δ.domRestrict π) (μ.comap ((↑) : Δ → G)) := rfl
  -- `νΔ` is left invariant
  haveI : νΔ.IsMulLeftInvariant := by
    refine ⟨fun q => ?_⟩
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
    ext U hU
    have hU' : MeasurableSet ((fun r => (g : G ⧸ H) * r) ⁻¹' U) := measurable_const_mul _ hU
    rw [Measure.map_apply (measurable_const_mul _) hU, Measure.map_apply hπ hU',
      Measure.map_apply hπ hU, Measure.restrict_apply (hπ hU'), Measure.restrict_apply (hπ hU)]
    have hpre : π ⁻¹' ((fun r => (g : G ⧸ H) * r) ⁻¹' U) = (fun x => g * x) ⁻¹' (π ⁻¹' U) := by
      ext x
      simp [π, QuotientGroup.mk_mul]
    have h2 : (fun x => g * x) ⁻¹' (π ⁻¹' U) ∩ Δ =
        (fun x => g * x) ⁻¹' (π ⁻¹' U ∩ g • Δ) := by
      ext x
      simp [Set.mem_smul_set_iff_inv_smul_mem]
    rw [hpre, h2, measure_preimage_mul]
    exact (hfund.smul_of_comm g).measure_set_eq hfund (hπ hU) (hinvU U)
  -- `νΔ` is sigma-finite
  haveI : SigmaFinite νΔ := by
    refine Measure.sigmaFinite_of_countable (S := Set.range (fun n : ℕ => π '' compactCovering G n))
      (Set.countable_range _) ?_ ?_
    · rintro _ ⟨n, rfl⟩
      have hK := isCompact_compactCovering G n
      have hKm : MeasurableSet (π '' compactCovering G n) := (hK.image hπc).measurableSet
      rw [Measure.map_apply hπ hKm, Measure.restrict_apply (hπ hKm)]
      have hsub : π ⁻¹' (π '' compactCovering G n) ∩ Δ ⊆
          ⋃ h : H, (h • compactCovering G n ∩ Δ) := by
        rintro x ⟨⟨k, hk, hkx⟩, hxΔ⟩
        have hmem : k⁻¹ * x ∈ H := QuotientGroup.eq.mp hkx
        refine Set.mem_iUnion.mpr ⟨⟨k⁻¹ * x, hmem⟩, ⟨k, hk, ?_⟩, hxΔ⟩
        change (k⁻¹ * x) * k = x
        rw [mul_comm, mul_inv_cancel_left]
      calc μ (π ⁻¹' (π '' compactCovering G n) ∩ Δ)
          ≤ μ (⋃ h : H, (h • compactCovering G n ∩ Δ)) := measure_mono hsub
        _ ≤ ∑' h : H, μ (h • compactCovering G n ∩ Δ) := measure_iUnion_le _
        _ = μ (compactCovering G n) := (hfund.measure_eq_tsum _).symm
        _ < ⊤ := hK.measure_lt_top
    · rw [Set.sUnion_range, ← Set.image_iUnion, iUnion_compactCovering]
      exact Set.image_univ_of_surjective QuotientGroup.mk_surjective
  -- uniqueness of Haar measure: `νΔ = c • ν`
  obtain ⟨K⟩ : Nonempty (TopologicalSpace.PositiveCompacts (G ⧸ H)) :=
    TopologicalSpace.PositiveCompacts.nonempty'
  have hK0 : ν K ≠ 0 := (Measure.measure_pos_of_nonempty_interior ν K.interior_nonempty).ne'
  have hKtop : ν K ≠ ⊤ := K.isCompact.measure_lt_top.ne
  have hc : νΔ = (νΔ K / ν K) • ν := measure_eq_div_smul νΔ ν hK0 hKtop
  -- a test function
  obtain ⟨φr, hφ1, -, hφc, hφ01⟩ := exists_continuous_one_zero_of_isCompact (X := G)
    isCompact_singleton isClosed_empty (Set.disjoint_empty {(1 : G)})
  let φ : G → ℂ := fun x => (φr x : ℂ)
  have hφcont : Continuous φ := Complex.continuous_ofReal.comp φr.continuous
  have hφsupp : HasCompactSupport φ := hφc.comp_left Complex.ofReal_zero
  have hφint : Integrable φ μ := hφcont.integrable_of_hasCompactSupport hφsupp
  have hIpos : 0 < ∫ x, φr x ∂μ :=
    φr.continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero hφc (fun x => (hφ01 x).1)
      (x := 1) (by rw [hφ1 (Set.mem_singleton 1)]; norm_num)
  have hIne : ∫ x, φ x ∂μ ≠ 0 := by
    have hI : ∫ x, φ x ∂μ = ((∫ x, φr x ∂μ : ℝ) : ℂ) := integral_ofReal
    rw [hI]
    exact_mod_cast hIpos.ne'
  let F : G ⧸ H → ℂ := fun q => ∫ h : H, φ (q.out * (h : G)) ∂(Measure.count : Measure H)
  have hWeil : ∫ x, φ x ∂μ = ∫ q, F q ∂ν := hν φ hφcont hφsupp
  -- the fibre sums are finite
  have hfin : ∀ y : G, (Function.support fun h : H => φ (y * (h : G))).Finite := by
    intro y
    have hce : IsClosedEmbedding (fun h : H => y * (h : G)) :=
      (Homeomorph.mulLeft y).isClosedEmbedding.comp hH.isClosedEmbedding_subtypeVal
    have hS : IsCompact ((fun h : H => y * (h : G)) ⁻¹' tsupport φ) :=
      hce.isCompact_preimage hφsupp
    refine hS.finite_of_discrete.subset ?_
    intro h hh
    exact subset_tsupport _ hh
  have hcount : ∀ y : G, ∫ h : H, φ (y * (h : G)) ∂(Measure.count : Measure H) =
      ∑' h : H, φ (y * (h : G)) := by
    intro y
    have hint : Integrable (fun h : H => φ (y * (h : G))) Measure.count := by
      rw [integrable_count_iff]
      apply summable_of_hasFiniteSupport
      refine (hfin y).subset ?_
      intro h hh
      simpa using hh
    rw [integral_countable hint]
    simp [Measure.real]
  have hFπ : ∀ x : G, F (π x) = ∑' h : H, φ (h • x) := by
    intro x
    obtain ⟨h0, hh0⟩ := QuotientGroup.mk_out_eq_mul H x
    change ∫ h : H, φ ((π x).out * (h : G)) ∂(Measure.count : Measure H) = _
    rw [show (π x).out = x * h0 from hh0, hcount]
    rw [← (Equiv.mulLeft h0).tsum_eq (fun h : H => φ (h • x))]
    congr 1
    ext h
    change φ (x * (h0 : G) * (h : G)) = φ ((h0 : G) * (h : G) * x)
    rw [mul_comm _ x, mul_assoc]
  -- the unfolding identity
  have hunfold : ∫ q, F q ∂νΔ = ∫ x, φ x ∂μ := by
    rw [hmap, hemb.integral_map]
    change ∫ y : Δ, (fun x => F (π x)) (y : G) ∂(μ.comap ((↑) : Δ → G)) = _
    rw [integral_subtype_comap hΔ (fun x => F (π x))]
    simp_rw [hFπ]
    rw [integral_tsum, ← hfund.integral_eq_tsum'' φ hφint]
    · intro h
      exact (hφcont.comp (continuous_const_smul h)).aestronglyMeasurable
    · rw [← hfund.lintegral_eq_tsum'' (fun x => ‖φ x‖ₑ)]
      exact hφint.2.ne
  -- the scalar is one
  have hc1 : νΔ K / ν K = 1 := by
    have h1 : ∫ q, F q ∂νΔ = (νΔ K / ν K).toReal • ∫ q, F q ∂ν := by
      conv_lhs => rw [hc]
      exact integral_smul_measure _ _
    rw [hunfold, ← hWeil, Complex.real_smul] at h1
    have h2 : ((νΔ K / ν K).toReal : ℂ) = 1 := by
      have := mul_right_cancel₀ hIne (h1.symm.trans (one_mul _).symm)
      exact this
    exact (ENNReal.toReal_eq_one_iff _).mp (by exact_mod_cast h2)
  have hνeq : νΔ = ν := by
    calc νΔ = (νΔ K / ν K) • ν := hc
      _ = ν := by rw [hc1, one_smul]
  refine ⟨?_, ?_⟩
  · rw [← hνeq, hmap, hemb.integrable_map_iff, integrableOn_iff_comap_subtypeVal hΔ]
    rfl
  · rw [← hνeq, hmap, hemb.integral_map, ← integral_subtype_comap hΔ]
    rfl
