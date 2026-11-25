-- Prove2me | solution 1 for GlobalTheory.NAK.map_mul_right_eq_of_mem_compact
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T07:45:57.328424+00:00
-- url     : https://prove2.me/submissions/70fc630c-e291-466b-8f71-16125f23f6a5

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HaarSK
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PSemidirectHaar
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HaarMeasureIwasawaQuotient
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
    [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsHaarMeasure] (K : Subgroup G) (hK : IsCompact (K : Set G)) (k : G) (hk : k ∈ K) :
    μ.map (· * k) = μ := by
  obtain ⟨A, hA, hA1⟩ := exists_compact_mem_nhds (1 : G)
  set B : Set G := A * (K : Set G) with hB
  have hBc : IsCompact B := hA.mul hK
  have hAB : A ⊆ B := fun a ha => ⟨a, ha, 1, K.one_mem, mul_one a⟩
  have hpos : μ B ≠ 0 := (measure_pos_of_mem_nhds μ (Filter.mem_of_superset hA1 hAB)).ne'
  have hfin : μ B ≠ ∞ := hBc.measure_lt_top.ne
  have hpre : (fun x => x * k) ⁻¹' B = B := by
    ext x
    simp only [Set.mem_preimage, hB, Set.mem_mul, SetLike.mem_coe]
    constructor
    · rintro ⟨a, ha, k', hk', he⟩
      exact ⟨a, ha, k' * k⁻¹, K.mul_mem hk' (K.inv_mem hk), by rw [← mul_assoc, he, mul_inv_cancel_right]⟩
    · rintro ⟨a, ha, k', hk', he⟩
      exact ⟨a, ha, k' * k, K.mul_mem hk' hk, by rw [← mul_assoc, he]⟩
  have h := map_right_mul_eq_modularCharacterFun_smul μ k
  have h2 := congrArg (fun m : Measure G => m B) h
  simp only [coe_nnreal_smul_apply] at h2
  rw [map_apply (measurable_mul_const k) hBc.measurableSet, hpre] at h2
  have h3 : modularCharacterFun k = 1 := by
    have : (modularCharacterFun k : ℝ≥0∞) * μ B = 1 * μ B := by rw [one_mul]; exact h2.symm
    exact_mod_cast (ENNReal.mul_left_inj hpos hfin).1 this
  rw [h, h3, one_smul]
end GlobalTheory.NAK
