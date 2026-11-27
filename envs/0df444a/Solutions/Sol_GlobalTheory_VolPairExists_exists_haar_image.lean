-- Prove2me | solution 1 for GlobalTheory.VolPairExists.exists_haar_image
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T04:36:06.263599+00:00
-- url     : https://prove2.me/submissions/77a8b3cc-81d5-420f-8602-086208b41e1d

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_DataCD
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_HaarUpqIsMulRightInvariant
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_LeftInvOfUnitary

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Topology Matrix Formalism.BasicNotions
open scoped ENNReal
open GlobalTheory GlobalTheory.VolPairExists
namespace GlobalTheory.VolPairExists
theorem _root_.solution {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [MeasurableSpace G] [BorelSpace G] (H : Subgroup G) (hH : IsOpen (H : Set G))
    {R : Type} [Group R] [TopologicalSpace R] [IsTopologicalGroup R]
    [LocallyCompactSpace R] [SecondCountableTopology R] [MeasurableSpace R] [BorelSpace R]
    (ν : Measure R) [ν.IsHaarMeasure] (ψ : G →* R) (hψ : Continuous ψ)
    (hs : ∀ t, ∃ h ∈ H, ψ h = t)
    (hf : ∀ t, ∃ W ∈ 𝓝 t, ∃ K : Set G, IsCompact K ∧ (H : Set G) ∩ ψ ⁻¹' W ⊆ K) :
    ∃ μ : Measure G, μ.IsHaarMeasure ∧ ∀ s, MeasurableSet s → μ (ψ ⁻¹' s ∩ H) = ν s := by
  classical
  have hψm : Measurable ψ := hψ.measurable
  set μ₀ : Measure G := Measure.haar
  set ρ : Measure R := (μ₀.restrict (H : Set G)).map ψ with hρdef
  have hρ : ∀ s, MeasurableSet s → ρ s = μ₀ (ψ ⁻¹' s ∩ H) := by
    intro s hsm
    rw [hρdef, Measure.map_apply hψm hsm, Measure.restrict_apply (hψm hsm)]
  have : ρ.IsMulLeftInvariant := by
    refine ⟨fun r => ?_⟩
    obtain ⟨h, hh, rfl⟩ := hs r
    refine Measure.ext fun s hsm => ?_
    have hpre : ψ ⁻¹' ((fun x => ψ h * x) ⁻¹' s) ∩ H = (fun x => h * x) ⁻¹' (ψ ⁻¹' s ∩ H) := by
      ext x
      simp only [Set.mem_inter_iff, Set.mem_preimage, map_mul, SetLike.mem_coe]
      rw [Subgroup.mul_mem_cancel_left H hh]
    rw [Measure.map_apply (measurable_const_mul _) hsm, hρ _ ((measurable_const_mul _) hsm), hρ _ hsm,
      hpre, measure_preimage_mul]
  have : IsFiniteMeasureOnCompacts ρ := by
    refine ⟨fun C hC => ?_⟩
    choose W hW K hK hWK using hf
    obtain ⟨t, -, ht⟩ := hC.elim_nhds_subcover (fun x => interior (W x))
      (fun x _ => interior_mem_nhds.2 (hW x))
    have hUo : IsOpen (⋃ x ∈ t, interior (W x)) := isOpen_biUnion fun x _ => isOpen_interior
    calc ρ C ≤ ρ (⋃ x ∈ t, interior (W x)) := measure_mono ht
      _ = μ₀ (ψ ⁻¹' (⋃ x ∈ t, interior (W x)) ∩ H) := hρ _ hUo.measurableSet
      _ ≤ μ₀ (⋃ x ∈ t, K x) := by
          apply measure_mono
          rintro y ⟨hy1, hy2⟩
          simp only [Set.mem_preimage, Set.mem_iUnion] at hy1 ⊢
          obtain ⟨x, hx, hyx⟩ := hy1
          exact ⟨x, hx, hWK x ⟨hy2, show ψ y ∈ W x from interior_subset hyx⟩⟩
      _ ≤ ∑ x ∈ t, μ₀ (K x) := measure_biUnion_finset_le t K
      _ < ⊤ := ENNReal.sum_lt_top.2 fun x _ => (hK x).measure_lt_top
  have hρ0 : ρ ≠ 0 := by
    intro h0
    have h1 := hρ Set.univ MeasurableSet.univ
    rw [h0] at h1
    simp only [Measure.coe_zero, Pi.zero_apply, Set.preimage_univ, Set.univ_inter] at h1
    exact (hH.measure_pos μ₀ ⟨1, H.one_mem⟩).ne' h1.symm
  have hc := Measure.isMulLeftInvariant_eq_smul ρ ν
  set c := Measure.haarScalarFactor ρ ν
  have hc0 : c ≠ 0 := by
    intro h0
    apply hρ0
    rw [hc, h0, zero_smul]
  have : (c⁻¹ • μ₀).IsHaarMeasure := Measure.IsHaarMeasure.nnreal_smul _ (inv_ne_zero hc0)
  refine ⟨c⁻¹ • μ₀, inferInstance, fun s hsm => ?_⟩
  have h1 := hρ s hsm
  rw [hc] at h1
  rw [Measure.smul_apply, ← h1, Measure.smul_apply, smul_smul, inv_mul_cancel₀ hc0, one_smul]
end GlobalTheory.VolPairExists
