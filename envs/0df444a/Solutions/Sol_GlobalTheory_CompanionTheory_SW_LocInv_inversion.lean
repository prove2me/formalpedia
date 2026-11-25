-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.LocInv.inversion
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T09:53:55.124578+00:00
-- url     : https://prove2.me/submissions/f3adb9f0-4b21-4215-a18d-b7fc64df6dc8

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_GroundTheory_LocalFields_LocalFourier
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_LocalFieldSelfdualMeasureExists
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_LocInv_tendsto_mean
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_LocInv_setIntegral_fourier_mul_char
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_LocInv_iUnion_valBall_sub
import Theorems.Thm_GroundTheory_LocalField_coe_homeomorphOfIsAlgebraic
import Theorems.Thm_GroundTheory_LocalField_measurableSet_valBall
import Theorems.Thm_GroundTheory_LocalField_modulus_eq_zero
import Theorems.Thm_GroundTheory_LocalField_modulus_one
import Theorems.Thm_GroundTheory_LocalField_modulus_zero
import Theorems.Thm_GroundTheory_LocalField_residueAlgEquiv_residue
import Theorems.Thm_GroundTheory_LocalField_selfDual_apply
import Theorems.Thm_GroundTheory_LocalField_unitsEquivResidueProd_fst
import Theorems.Thm_GroundTheory_LocalField_unitsEquivResidueProd_symm_apply
import Theorems.Thm_GroundTheory_LocalField_valBall_antitone
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.LocalField.coe_homeomorphOfIsAlgebraic
attribute [local simp] GroundTheory.LocalField.modulus_eq_zero
attribute [local simp] GroundTheory.LocalField.modulus_one
attribute [local simp] GroundTheory.LocalField.modulus_zero
attribute [local simp] GroundTheory.LocalField.residueAlgEquiv_residue
attribute [local simp] GroundTheory.LocalField.selfDual_apply
attribute [local simp] GroundTheory.LocalField.unitsEquivResidueProd_fst
attribute [local simp] GroundTheory.LocalField.unitsEquivResidueProd_symm_apply



set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.LocInv
open GroundTheory.LocalField ValuativeRel MeasureTheory Topology Filter
open scoped NNReal ENNReal
variable {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [MeasurableSpace K] [BorelSpace K]
namespace GlobalTheory.CompanionTheory.SW.LocInv
theorem _root_.solution {ψ : AddChar K Circle} (hψ : Continuous ψ) (hψ1 : ψ ≠ 1)
    {Φ : K → ℂ} (hΦ : Continuous Φ) (hc : HasCompactSupport Φ)
    (hI : Integrable (fun y => ∫ x, Φ x * (ψ (x * y) : ℂ) ∂(selfDualMeasure ψ))
      (selfDualMeasure ψ)) (z : K) :
    ∫ y, (∫ x, Φ x * (ψ (x * y) : ℂ) ∂(selfDualMeasure ψ)) * (ψ (y * z) : ℂ)
      ∂(selfDualMeasure ψ) = Φ (-z) := by
  have hψc : Continuous fun x => (ψ x : ℂ) := continuous_subtype_val.comp hψ
  have hF : Integrable (fun y => (∫ x, Φ x * (ψ (x * y) : ℂ) ∂(selfDualMeasure ψ)) *
      (ψ (y * z) : ℂ)) (selfDualMeasure ψ) := by
    refine hI.norm.mono' (hI.aestronglyMeasurable.mul
      (hψc.comp (continuous_id.mul continuous_const)).aestronglyMeasurable)
      (Eventually.of_forall fun y => ?_)
    simp [Circle.norm_coe]
  have hmono : Monotone fun k : ℕ => (valBall K (addCharConductor ψ - (k : ℤ)) : Set K) :=
    fun a b hab => valBall_antitone (by omega)
  have hlim := tendsto_setIntegral_of_monotone (μ := selfDualMeasure ψ)
    (fun k : ℕ => measurableSet_valBall (K := K) (addCharConductor ψ - (k : ℤ))) hmono
    hF.integrableOn
  rw [iUnion_valBall_sub, setIntegral_univ] at hlim
  refine tendsto_nhds_unique hlim ?_
  refine (tendsto_mean ψ hΦ z).congr fun k => ?_
  exact (setIntegral_fourier_mul_char hψ hψ1 hΦ hc z (k : ℤ)).symm
end GlobalTheory.CompanionTheory.SW.LocInv
