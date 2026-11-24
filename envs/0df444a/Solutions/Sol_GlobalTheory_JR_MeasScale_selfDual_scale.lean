-- Prove2me | solution 1 for GlobalTheory.JR.MeasScale.selfDual_scale
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T18:21:06.510965+00:00
-- url     : https://prove2.me/submissions/b6139d71-6f42-4ce3-821a-9bb8274c04b8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NonemptyMeasAndReps
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_QuadraticStarStructure
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_DistribHaarCharTransport
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FiniteNormedAlgebraEqModuleTopology
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsSelfDualMeasuresAndAbsKScale
import Theorems.Thm_GlobalTheory_JR_MeasScale_fourB_nnreal_smul
import Theorems.Thm_GlobalTheory_JR_MeasScale_fourB_const_mul
import Theorems.Thm_GlobalTheory_JR_MeasScale_integral_units_smul
import Theorems.Thm_GlobalTheory_JR_MeasScale_kerL_eq
import Theorems.Thm_GlobalTheory_JR_MeasScale_kerL_swap
import Theorems.Thm_GlobalTheory_JR_EtMeas_finite_L
import Theorems.Thm_GlobalTheory_JR_EtMeas_top_facts
import Theorems.Thm_GlobalTheory_JR_Et_quadratic_structure
import Theorems.Thm_GlobalTheory_JR_ModuleNorm_distribHaarChar_eq_norm


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
open scoped Pointwise NNReal ENNReal
noncomputable section
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.MeasScale
variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]
namespace GlobalTheory.JR.MeasScale
theorem _root_.solution [U : Unram F E] (A : Et F E) (ψ : AddChar F ℂ) (x : A.Kˣ) (μ : Measure A.L)
    (h : SelfDual μ (A.kerL ψ ((1 : A.Kˣ) : A.K))) :
    SelfDual (distribHaarChar A.K x • μ) (A.kerL ψ x) := by
  have := U.charZero; have := U.ultraF; have := U.lcF
  have := EtMeas.finite_L A
  obtain ⟨_, _, _, _, -⟩ := EtMeas.top_facts F A.L
  have : IsTopologicalRing A.L := IsModuleTopology.isTopologicalRing F A.L
  have hN : distribHaarChar A.L (unitL A x) = distribHaarChar A.K x ^ 2 := by
    obtain ⟨⟨b⟩, -, -, -, -⟩ := GlobalTheory.JR.Et.quadratic_structure F E A
    obtain ⟨_, _, _, _, -⟩ := EtMeas.top_facts F A.K
    have : ContinuousStar A.L := ⟨IsModuleTopology.continuous_of_linearMap (EtMeas.starF A)⟩
    rw [← map_pow]
    refine GlobalTheory.JR.ModuleNorm.distribHaarChar_eq_norm A.K A.L b.equivFun.symm
        (IsModuleTopology.continuous_of_linearMap (b.equivFun.symm.toLinearMap.restrictScalars F))
        (IsModuleTopology.continuous_of_linearMap (b.equivFun.toLinearMap.restrictScalars F)) _ _ ?_
    simp [unitL, A.star_K, pow_two]
  obtain ⟨hμ, hF⟩ := h
  have hc : distribHaarChar A.K x ≠ 0 := distribHaarChar_pos.ne'
  refine ⟨Measure.IsAddHaarMeasure.nnreal_smul _ hc, fun f hf y => ?_⟩
  set c := distribHaarChar A.K x with hcdef
  set B1 := A.kerL ψ ((1 : A.Kˣ) : A.K)
  have h1 : ∀ g z, fourB (c • μ) (A.kerL ψ x) g z = (c : ℂ) * fourB μ B1 g (unitL A x • z) := by
    intro g z
    rw [fourB_nnreal_smul]
    simp only [fourB, kerL_eq A ψ x, B1]
  have h2 : fourB (c • μ) (A.kerL ψ x) f = fun z => (c : ℂ) * fourB μ B1 f (unitL A x • z) :=
    funext (h1 f)
  rw [h1, h2]
  have h3 : fourB μ B1 (fun z => (c : ℂ) * fourB μ B1 f (unitL A x • z)) (unitL A x • y) =
      (c : ℂ) * ((distribHaarChar A.L (unitL A x) : ℝ≥0) : ℂ)⁻¹ * fourB μ B1 (fourB μ B1 f) y := by
    rw [fourB_const_mul, mul_assoc]
    congr 1
    have e := integral_units_smul μ (unitL A x) (fun z => fourB μ B1 f z * B1 z y)
    refine Eq.trans ?_ e
    show ∫ y', fourB μ B1 f (unitL A x • y') * B1 y' (unitL A x • y) ∂μ = _
    refine integral_congr_ae (Eventually.of_forall fun y' => ?_)
    exact congrArg _ (kerL_swap A ψ x y' y)
  rw [h3, hF f hf y, hN]
  have hc' : (c : ℂ) ≠ 0 := by exact_mod_cast hc
  push_cast
  field_simp
end GlobalTheory.JR.MeasScale
