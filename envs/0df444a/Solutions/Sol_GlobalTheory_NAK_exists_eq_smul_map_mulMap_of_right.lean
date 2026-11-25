-- Prove2me | solution 1 for GlobalTheory.NAK.exists_eq_smul_map_mulMap_of_right
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T07:51:01.237042+00:00
-- url     : https://prove2.me/submissions/19aa35a5-c150-4324-8fb5-b06cbf4d37b8

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HaarSK
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PSemidirectHaar
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HaarMeasureIwasawaQuotient
import Theorems.Thm_GroundTheory_Automorphic_HaarSK_flat_eq_self
import Theorems.Thm_GroundTheory_Automorphic_HaarSK_funcL_apply
import Theorems.Thm_GroundTheory_Automorphic_HaarSK_integral_rmk
import Theorems.Thm_GroundTheory_Automorphic_HaarSK_isMulLeftInvariant_rmk
import Theorems.Thm_GroundTheory_Automorphic_HermitianForm_equivOfIsometry_apply
import Theorems.Thm_GroundTheory_Automorphic_HermitianForm_restrict_apply
import Theorems.Thm_GroundTheory_Automorphic_conj_conj
import Theorems.Thm_GroundTheory_Automorphic_finiteAdeleUnitaryEquiv_apply
import Theorems.Thm_GroundTheory_Automorphic_matrixCoords_zero
import Theorems.Thm_GroundTheory_Automorphic_unitaryPiEquiv_apply
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_finiteEmbedding
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_finiteProj
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_finiteProj_diagonal
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_infiniteEmbedding
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_infiniteProj
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_infiniteProj_diagonal
import Theorems.Thm_GroundTheory_Global_IdeleGroup_finiteAdeleSingle_apply_self
import Theorems.Thm_GroundTheory_Global_IdeleGroup_finiteProj_finiteEmbedding
import Theorems.Thm_GroundTheory_Global_IdeleGroup_finiteUnitsEquiv_apply
import Theorems.Thm_GroundTheory_Global_IdeleGroup_infiniteProj_infiniteEmbedding
import Theorems.Thm_GroundTheory_Global_IdeleGroup_prodRestrictedEquiv_apply_fst
import Theorems.Thm_GroundTheory_Global_IdeleGroup_prodRestrictedEquiv_apply_snd
import Theorems.Thm_GroundTheory_Global_RestrictedProduct_continuousUnitsEquiv_apply
import Theorems.Thm_GroundTheory_Global_residueFieldEquiv_mk
import Theorems.Thm_GroundTheory_LocalField_coe_normUnits
import Theorems.Thm_GroundTheory_LocalField_ord_zero
import Theorems.Thm_GroundTheory_LocalField_residueAlgEquiv_residue
import Theorems.Thm_GroundTheory_LocalField_unitsEquivResidueProd_fst
import Theorems.Thm_GroundTheory_LocalField_unitsEquivResidueProd_symm_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.HermitianForm.equivOfIsometry_apply
attribute [local simp] GroundTheory.Automorphic.HermitianForm.restrict_apply
attribute [local simp] GroundTheory.Automorphic.conj_conj
attribute [local simp] GroundTheory.Automorphic.finiteAdeleUnitaryEquiv_apply
attribute [local simp] GroundTheory.Automorphic.matrixCoords_zero
attribute [local simp] GroundTheory.Automorphic.unitaryPiEquiv_apply
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_finiteEmbedding
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_finiteProj
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_finiteProj_diagonal
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_infiniteEmbedding
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_infiniteProj
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_infiniteProj_diagonal
attribute [local simp] GroundTheory.Global.IdeleGroup.finiteAdeleSingle_apply_self
attribute [local simp] GroundTheory.Global.IdeleGroup.finiteProj_finiteEmbedding
attribute [local simp] GroundTheory.Global.IdeleGroup.finiteUnitsEquiv_apply
attribute [local simp] GroundTheory.Global.IdeleGroup.infiniteProj_infiniteEmbedding
attribute [local simp] GroundTheory.Global.IdeleGroup.prodRestrictedEquiv_apply_fst
attribute [local simp] GroundTheory.Global.IdeleGroup.prodRestrictedEquiv_apply_snd
attribute [local simp] GroundTheory.Global.RestrictedProduct.continuousUnitsEquiv_apply
attribute [local simp] GroundTheory.Global.residueFieldEquiv_mk
attribute [local simp] GroundTheory.LocalField.coe_normUnits
attribute [local simp] GroundTheory.LocalField.ord_zero
attribute [local simp] GroundTheory.LocalField.residueAlgEquiv_residue
attribute [local simp] GroundTheory.LocalField.unitsEquivResidueProd_fst
attribute [local simp] GroundTheory.LocalField.unitsEquivResidueProd_symm_apply



set_option autoImplicit false
open MeasureTheory Measure Topology Set Function TopologicalSpace GroundTheory.Automorphic.HaarSK
open scoped NNReal ENNReal Pointwise
noncomputable section
open GlobalTheory GlobalTheory.NAK
namespace GlobalTheory.NAK
theorem _root_.solution {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [MeasurableSpace G] [BorelSpace G] [T2Space G]
    [LocallyCompactSpace G] [SecondCountableTopology G] (S K : Subgroup G)
    (μ : Measure G) [μ.IsHaarMeasure] (hright : ∀ k ∈ K, μ.map (· * k) = μ)
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
      have hri : ∀ k : K, ∫ g, φ (g * (k : G)) ∂μ = ∫ g, φ g ∂μ := fun k => by
        conv_rhs => rw [← hright (k : G) k.2]
        rw [integral_map (measurable_mul_const _).aemeasurable (map_continuous φ).aestronglyMeasurable]
      simp_rw [hri]
      rw [integral_const, smul_eq_mul, measureReal_def]

    have hu : ∀ s, ∀ m ∈ inter S K, (fun s : S => φK s) (s * m) = (fun s : S => φK s) s := by
      intro s m hm
      simpa using hφKinv (s : G) ⟨(m : G), (GroundTheory.Automorphic.HaarSK.mem_inter_iff).1 hm⟩
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
end GlobalTheory.NAK
