-- Prove2me | solution 1 for GroundTheory.Automorphic.HaarSK.exists_eq_smul_map_mulMap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:11:27.757105+00:00
-- url     : https://prove2.me/submissions/4f7615a4-dfaf-426c-a8b5-a362357868e5

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HaarSK
import Theorems.Thm_GroundTheory_Automorphic_HaarSK_flat_eq_self
import Theorems.Thm_GroundTheory_Automorphic_HaarSK_funcL_apply
import Theorems.Thm_GroundTheory_Automorphic_HaarSK_integral_rmk
import Theorems.Thm_GroundTheory_Automorphic_HaarSK_isMulLeftInvariant_rmk

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Measure Topology Set Function TopologicalSpace
open scoped ENNReal NNReal
set_option linter.unusedSectionVars false
open GroundTheory GroundTheory.Automorphic
noncomputable section
open GroundTheory.Automorphic.HaarSK
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {S K : Subgroup G}
variable (hSK : Surjective (mulMap S K))
variable {hSK}
namespace GroundTheory.Automorphic.HaarSK
theorem _root_.solution [MeasurableSpace G] [BorelSpace G] [T2Space G]
    [LocallyCompactSpace G] [SecondCountableTopology G]
    (μ : Measure G) [μ.IsHaarMeasure] [μ.IsMulRightInvariant]
    (hS : IsClosed (S : Set G)) (hK : IsCompact (K : Set G)) (hSK : Surjective (mulMap S K))
    (μS : Measure S) [μS.IsHaarMeasure] (μK : Measure K) [μK.IsHaarMeasure] :
    ∃ c : ℝ≥0, μ = c • map (mulMap S K) (μS.prod μK) := by
  have : LocallyCompactSpace S := hS.isClosedEmbedding_subtypeVal.locallyCompactSpace
  have : SecondCountableTopology S := TopologicalSpace.Subtype.secondCountableTopology _
  have : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have hLc : IsCompact ((inter S K : Subgroup S) : Set S) := by
    rw [Subgroup.coe_subgroupOf]
    exact hS.isClosedEmbedding_subtypeVal.isCompact_preimage hK
  have : CompactSpace (inter S K) := isCompact_iff_compactSpace.mp hLc
  set mL : Measure (inter S K) := haarMeasure ⊤ with hmL
  have : IsProbabilityMeasure mL := ⟨by simpa using haarMeasure_self (K₀ := (⊤ : PositiveCompacts (inter S K)))⟩
  have : (rmk mL hS hK hSK μ).IsMulLeftInvariant := isMulLeftInvariant_rmk mL hS hK hSK μ
  set c₀ := haarScalarFactor (rmk mL hS hK hSK μ) μS
  have hc₀ : rmk mL hS hK hSK μ = c₀ • μS := isMulLeftInvariant_eq_smul _ _
  have : IsFiniteMeasure μK := inferInstance
  have hKpos : 0 < (μK univ).toReal :=
    ENNReal.toReal_pos (IsOpenPosMeasure.open_pos univ isOpen_univ univ_nonempty)
      (measure_ne_top _ _)

  have hfin : IsFiniteMeasureOnCompacts (map (mulMap S K) (μS.prod μK)) := ⟨fun C hC => by
    rw [map_apply continuous_mulMap.measurable hC.measurableSet]
    exact (isCompact_preimage_mulMap hS hK hC).measure_lt_top⟩
  have key : ∀ φ : CompactlySupportedContinuousMap G ℝ,
      (μK univ).toReal * ∫ g, φ g ∂μ = (c₀ : ℝ) * ∫ p, φ (mulMap S K p) ∂(μS.prod μK) := by
    intro φ
    set φK : G → ℝ := fun g => ∫ k, φ (g * k) ∂μK with hφK
    have hφKc : Continuous φK := by
      have := continuous_parametric_integral_of_continuous (μ := μK)
        (f := fun (g : G) (k : K) => φ (g * k))
        (φ.continuous.comp (continuous_fst.mul (continuous_subtype_val.comp continuous_snd)))
        isCompact_univ
      simpa using this
    have hφKinv : ∀ g (k : K), φK (g * k) = φK g := by
      intro g k
      simp only [hφK]
      have := integral_mul_left_eq_self (μ := μK) (fun k' : K => φ (g * k')) k
      simpa only [Subgroup.coe_mul, mul_assoc] using this
    have hφKcs : HasCompactSupport φK := by
      refine HasCompactSupport.intro ((IsCompact.prod φ.hasCompactSupport hK).image
        (f := fun q : G × G => q.1 * q.2⁻¹) (by fun_prop)) ?_
      intro g hg
      have h0 : ∀ k : K, φ (g * k) = 0 := fun k => by
        by_contra h
        exact hg ⟨(g * k, k), ⟨subset_tsupport _ h, k.2⟩, by simp⟩
      simp [hφK, h0]

    have hint : ∫ g, φK g ∂μ = (μK univ).toReal * ∫ g, φ g ∂μ := by
      have hF : Integrable (fun q : G × K => φ (q.1 * q.2)) (μ.prod μK) := by
        refine (φ.continuous.comp (continuous_fst.mul (continuous_subtype_val.comp
          continuous_snd))).integrable_of_hasCompactSupport ?_
        refine HasCompactSupport.intro (((IsCompact.prod φ.hasCompactSupport hK).image
          (f := fun q : G × G => q.1 * q.2⁻¹) (by fun_prop)).prod (isCompact_univ (X := K))) ?_
        rintro ⟨g, k⟩ hq
        by_contra h
        exact hq ⟨⟨(g * k, k), ⟨subset_tsupport _ h, k.2⟩, by simp⟩, mem_univ _⟩
      rw [hφK, integral_integral_swap hF]
      simp_rw [integral_mul_right_eq_self (μ := μ) (fun g => φ g)]
      rw [integral_const, smul_eq_mul, measureReal_def]

    have hu : ∀ s, ∀ m ∈ inter S K, (fun s : S => φK s) (s * m) = (fun s : S => φK s) s := by
      intro s m hm
      simpa using hφKinv (s : G) ⟨(m : G), (mem_inter_iff).1 hm⟩
    set uCc : CompactlySupportedContinuousMap S ℝ :=
      { toFun := fun s => φK s
        continuous_toFun := hφKc.comp continuous_subtype_val
        hasCompactSupport' := hφKcs.comp_isClosedEmbedding hS.isClosedEmbedding_subtypeVal }
    have hflat : flat mL uCc = fun s : S => φK (s : G) := flat_eq_self (u := fun s : S => φK (s : G)) hu
    have hlift : lift hSK (flat mL uCc) = φK := by
      rw [hflat]
      funext g
      obtain ⟨p, rfl⟩ := hSK g
      rw [lift_mulMap hu]
      exact (hφKinv _ _).symm
    have h1 := integral_rmk mL hS hK hSK μ uCc
    rw [funcL_apply, hlift, hint, hc₀, integral_smul_nnreal_measure] at h1
    rw [← h1]
    have hFS : Integrable (fun p : S × K => φ (mulMap S K p)) (μS.prod μK) :=
      (φ.continuous.comp continuous_mulMap).integrable_of_hasCompactSupport
        (isCompact_preimage_mulMap hS hK φ.hasCompactSupport |>.of_isClosed_subset
          (isClosed_tsupport _) (by
            intro p hp
            exact (tsupport_comp_subset_preimage φ continuous_mulMap) hp))
    rw [integral_prod _ hFS]
    rfl
  set c : ℝ≥0 := ⟨c₀ / (μK univ).toReal, div_nonneg c₀.2 hKpos.le⟩ with hc
  refine ⟨c, ?_⟩
  have hreg : (map (mulMap S K) (μS.prod μK)).Regular := inferInstance
  have : (c • map (mulMap S K) (μS.prod μK)).Regular := by
    rw [ENNReal.smul_def]
    exact Measure.Regular.smul ENNReal.coe_ne_top
  apply Measure.ext_of_integral_eq_on_compactlySupported
  intro φ
  rw [integral_smul_nnreal_measure, integral_map continuous_mulMap.aemeasurable
    (map_continuous φ).aestronglyMeasurable, NNReal.smul_def, smul_eq_mul]
  show _ = ((c₀ : ℝ) / (μK univ).toReal) * _
  rw [div_mul_eq_mul_div, ← key, mul_div_cancel_left₀ _ hKpos.ne']
end GroundTheory.Automorphic.HaarSK
