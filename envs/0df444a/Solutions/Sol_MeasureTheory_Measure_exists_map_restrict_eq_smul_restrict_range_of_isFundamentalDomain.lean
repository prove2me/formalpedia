-- Prove2me | solution 1 for MeasureTheory.Measure.exists_map_restrict_eq_smul_restrict_range_of_isFundamentalDomain
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/411c35cc-9579-582a-982a-08f8d5a6226a

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_MeasureTheory_Measure_exists_map_restrict_eq_smul_restrict_range_of_isFundamentalDomain

set_option autoImplicit false

namespace R2FafNAEngine

open MeasureTheory MeasureTheory.Measure Set Filter Topology
open scoped ENNReal NNReal Pointwise

section Unique

variable {S : Type*} [Group S] [TopologicalSpace S] [IsTopologicalGroup S] [LocallyCompactSpace S]
  [SigmaCompactSpace S] [MeasurableSpace S] [BorelSpace S]

theorem eq_haarScalarFactor_smul (μ' μ : Measure S) [IsHaarMeasure μ] [IsFiniteMeasureOnCompacts μ']
    [IsMulLeftInvariant μ'] : μ' = haarScalarFactor μ' μ • μ := by
  ext s _hs
  have hs_eq : s = ⋃ n, s ∩ compactCovering S n := by
    rw [← inter_iUnion, iUnion_compactCovering, inter_univ]
  have hmono : Monotone fun n => s ∩ compactCovering S n :=
    fun m n hmn => inter_subset_inter_right _ (compactCovering_subset S hmn)
  rw [hs_eq, hmono.measure_iUnion, hmono.measure_iUnion]
  refine iSup_congr fun n => ?_
  rw [Measure.coe_nnreal_smul_apply]
  exact measure_isMulInvariant_eq_smul_of_isCompact_closure μ' μ
    ((isCompact_compactCovering S n).closure_of_subset inter_subset_right)

end Unique

section Main

variable {G H : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [SigmaCompactSpace G] [MeasurableSpace G] [BorelSpace G]
  [CommGroup H] [TopologicalSpace H] [IsTopologicalGroup H] [LocallyCompactSpace H]
  [T2Space H] [MeasurableSpace H] [BorelSpace H]

theorem main (μ : Measure G) [μ.IsHaarMeasure] (ν : Measure H) [ν.IsHaarMeasure]
    (f : G →* H) (hf : Continuous f) (hopen : IsOpen (Set.range f))
    (Γ : Subgroup G) [Countable Γ] (hΓ : Γ ≤ f.ker)
    (hker : ∃ D : Set G, IsCompact D ∧ (f.ker : Set G) ⊆ (Γ : Set G) * D)
    (Θ : Set G) (hΘ : IsFundamentalDomain Γ Θ μ) :
    ∃ κ : ℝ, 0 < κ ∧
      Measure.map f (μ.restrict Θ) = ENNReal.ofReal κ • ν.restrict (Set.range f) := by
  classical

  set S : Subgroup H := f.range with hSdef
  have hScoe : (S : Set H) = Set.range f := MonoidHom.coe_range f
  have hSopen : IsOpen (S : Set H) := by rw [hScoe]; exact hopen
  haveI : LocallyCompactSpace S := hSopen.locallyCompactSpace
  haveI : SigmaCompactSpace S := by
    have h1 : IsSigmaCompact (S : Set H) := by
      rw [hScoe, ← Set.image_univ]
      exact isSigmaCompact_univ.image hf
    exact isSigmaCompact_iff_sigmaCompactSpace.1 h1

  let fS : G →* S := f.rangeRestrict
  have hfS_val : ∀ x, ((fS x : S) : H) = f x := fun x => rfl
  have hfS_cont : Continuous fS := hf.subtype_mk _
  have hfS_surj : Function.Surjective fS := MonoidHom.rangeRestrict_surjective f
  have hfS_open : IsOpenMap fS := MonoidHom.isOpenMap_of_sigmaCompact fS hfS_surj hfS_cont
  have hfS_meas : Measurable fS := hfS_cont.measurable
  have hfS_ker : ∀ γ : Γ, fS (γ : G) = 1 := fun γ => by
    ext
    rw [hfS_val]
    exact hΓ γ.2

  have hemb : Topology.IsOpenEmbedding (S.subtype : S → H) := hSopen.isOpenEmbedding_subtypeVal
  let νS : Measure S := ν.comap S.subtype
  haveI hνS : νS.IsHaarMeasure := IsHaarMeasure.comap (mH := inferInstance) ν hemb

  let ρ : Measure S := Measure.map fS (μ.restrict Θ)
  have hρ_apply : ∀ A : Set S, MeasurableSet A → ρ A = μ (fS ⁻¹' A ∩ Θ) := fun A hA => by
    show Measure.map fS (μ.restrict Θ) A = _
    rw [Measure.map_apply hfS_meas hA, Measure.restrict_apply (hfS_meas hA)]

  have hinv : ∀ (A : Set S) (γ : Γ), (fun x => γ • x) ⁻¹' (fS ⁻¹' A) = fS ⁻¹' A := by
    intro A γ
    ext x
    simp only [Set.mem_preimage, Subgroup.smul_def, smul_eq_mul, map_mul, hfS_ker γ, one_mul]
  haveI : SMulCommClass G Γ G := ⟨fun a γ x => mul_left_comm a (γ : G) x⟩

  haveI hρinv : ρ.IsMulLeftInvariant := by
    refine (forall_measure_preimage_mul_iff ρ).1 fun s0 A hA => ?_
    obtain ⟨a, rfl⟩ := hfS_surj s0
    rw [hρ_apply _ (measurable_const_mul _ hA), hρ_apply A hA]
    have h1 : fS ⁻¹' ((fun y => fS a * y) ⁻¹' A) = (fun x => a * x) ⁻¹' (fS ⁻¹' A) := by
      ext x
      simp only [Set.mem_preimage, map_mul]
    rw [h1]
    have hB : MeasurableSet (fS ⁻¹' A) := hfS_meas hA
    have h2 : (fun x => a * x) ⁻¹' (fS ⁻¹' A) ∩ Θ = (fun x => a * x) ⁻¹' (fS ⁻¹' A ∩ a • Θ) := by
      rw [Set.preimage_inter]
      congr 1
      ext x
      simp only [Set.mem_preimage]
      constructor
      · intro hx
        exact ⟨x, hx, rfl⟩
      · rintro ⟨y, hy, hyx⟩
        have : y = x := mul_left_cancel (a := a) (by simpa [smul_eq_mul] using hyx)
        rw [← this]
        exact hy
    have hΘa : IsFundamentalDomain Γ (a • Θ) μ := hΘ.smul_of_comm a
    rw [h2, measure_preimage_mul, hΘa.measure_set_eq hΘ hB (hinv A)]

  obtain ⟨D, hD, hkerD⟩ := hker
  haveI hρfin : IsFiniteMeasureOnCompacts ρ := by
    refine ⟨fun C hC => ?_⟩

    obtain ⟨D₁, hD₁, hCD₁⟩ : ∃ D₁ : Set G, IsCompact D₁ ∧ C ⊆ fS '' D₁ := by
      have hK : ∀ x : G, ∃ K : Set G, IsCompact K ∧ K ∈ 𝓝 x := fun x => exists_compact_mem_nhds x
      choose K hKc hKn using hK
      have hcover : C ⊆ ⋃ x : G, fS '' interior (K x) := by
        intro c _
        obtain ⟨x, rfl⟩ := hfS_surj c
        exact Set.mem_iUnion.2 ⟨x, Set.mem_image_of_mem _ (mem_interior_iff_mem_nhds.2 (hKn x))⟩
      obtain ⟨t, ht⟩ := hC.elim_finite_subcover (fun x => fS '' interior (K x))
        (fun x => hfS_open _ isOpen_interior) hcover
      refine ⟨⋃ x ∈ t, K x, t.isCompact_biUnion fun x _ => hKc x, ?_⟩
      intro c hc
      obtain ⟨x, hxt, hcx⟩ := Set.mem_iUnion₂.1 (ht hc)
      obtain ⟨y, hy, rfl⟩ := hcx
      exact ⟨y, Set.mem_biUnion hxt (interior_subset hy), rfl⟩
    have hsub : fS ⁻¹' C ⊆ ⋃ γ : Γ, γ • (D₁ * D) := by
      intro y hy
      obtain ⟨d, hd, hdy⟩ := hCD₁ hy
      have hk : d⁻¹ * y ∈ f.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv]
        have : f d = f y := by rw [← hfS_val, ← hfS_val, hdy]
        rw [this, inv_mul_cancel]
      obtain ⟨γ, hγ, e, he, hγe⟩ := hkerD hk
      refine Set.mem_iUnion.2 ⟨⟨γ, hγ⟩, ?_⟩
      refine ⟨d * e, Set.mul_mem_mul hd he, ?_⟩
      show γ * (d * e) = y
      have hγe' : γ * e = d⁻¹ * y := hγe
      rw [mul_left_comm, hγe', mul_inv_cancel_left]
    calc ρ C = μ (fS ⁻¹' C ∩ Θ) := hρ_apply C hC.measurableSet
      _ ≤ μ ((⋃ γ : Γ, γ • (D₁ * D)) ∩ Θ) := measure_mono (Set.inter_subset_inter_left _ hsub)
      _ = μ (⋃ γ : Γ, γ • (D₁ * D) ∩ Θ) := by rw [Set.iUnion_inter]
      _ ≤ ∑' γ : Γ, μ (γ • (D₁ * D) ∩ Θ) := measure_iUnion_le _
      _ = μ (D₁ * D) := (hΘ.measure_eq_tsum (D₁ * D)).symm
      _ < ⊤ := (hD₁.mul hD).measure_lt_top

  have hρeq : ρ = haarScalarFactor ρ νS • νS := eq_haarScalarFactor_smul ρ νS
  set c : ℝ≥0 := haarScalarFactor ρ νS with hcdef
  have hμ0 : μ ≠ 0 := by
    intro h0
    have := isOpen_univ.measure_ne_zero μ Set.univ_nonempty
    rw [h0] at this
    exact this rfl
  have hc : c ≠ 0 := by
    intro hc0
    have hρ0 : ρ = 0 := by rw [hρeq, hc0, zero_smul]
    have h1 : ρ Set.univ = μ Θ := by
      rw [hρ_apply _ MeasurableSet.univ, Set.preimage_univ, Set.univ_inter]
    have h2 : μ Θ = 0 := by rw [← h1, hρ0]; rfl
    exact hΘ.measure_ne_zero hμ0 h2
  refine ⟨(c : ℝ), NNReal.coe_pos.2 (pos_iff_ne_zero.2 hc), ?_⟩

  have hval_meas : Measurable (S.subtype : S → H) := measurable_subtype_coe
  have h1 : Measure.map f (μ.restrict Θ) = Measure.map S.subtype ρ := by
    show _ = Measure.map S.subtype (Measure.map fS (μ.restrict Θ))
    rw [Measure.map_map hval_meas hfS_meas]
    rfl
  have h2 : Measure.map S.subtype νS = ν.restrict (Set.range f) := by
    show Measure.map S.subtype (ν.comap S.subtype) = _
    rw [hemb.measurableEmbedding.map_comap]
    congr 1
    rw [← hScoe]
    ext x
    simp
  have h3 : (c • νS : Measure S) = (c : ℝ≥0∞) • νS := rfl
  rw [h1, hρeq, h3, Measure.map_smul, h2, ENNReal.ofReal_coe_nnreal]

end Main

end R2FafNAEngine

open scoped ENNReal Pointwise in
open R2FafNAEngine MeasureTheory in
theorem solution
    {G H : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [SigmaCompactSpace G] [MeasurableSpace G] [BorelSpace G]
    [CommGroup H] [TopologicalSpace H] [IsTopologicalGroup H] [LocallyCompactSpace H]
    [T2Space H] [MeasurableSpace H] [BorelSpace H]
    (μ : Measure G) [μ.IsHaarMeasure] (ν : Measure H) [ν.IsHaarMeasure]
    (f : G →* H) (hf : Continuous f) (hopen : IsOpen (Set.range f))
    (Γ : Subgroup G) [Countable Γ] (hΓ : Γ ≤ f.ker)
    (hker : ∃ D : Set G, IsCompact D ∧ (f.ker : Set G) ⊆ (Γ : Set G) * D)
    (Θ : Set G) (hΘ : IsFundamentalDomain Γ Θ μ) :
    ∃ κ : ℝ, 0 < κ ∧
      Measure.map f (μ.restrict Θ) = ENNReal.ofReal κ • ν.restrict (Set.range f) :=
  main μ ν f hf hopen Γ hΓ hker Θ hΘ

end S_MeasureTheory_Measure_exists_map_restrict_eq_smul_restrict_range_of_isFundamentalDomain
end P2MW
export P2MW.S_MeasureTheory_Measure_exists_map_restrict_eq_smul_restrict_range_of_isFundamentalDomain (solution)
