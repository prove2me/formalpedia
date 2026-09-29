-- Prove2me | solution 1 for LanglandsTunnell.exists_archCasimir_eigenvector_minimalWeight_of_continuous_realization
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/562fd4f4-623c-5fb5-9f34-38f0a31f54ca

import Definitions.Def_AutomorphicForm_ArchDerivCasimir
import Mathlib.Analysis.Complex.UpperHalfPlane.MoebiusAction
import Definitions.Def_AutomorphicForm_IsotypicCuspSpace
import Definitions.Def_LanglandsTunnell_ConverseData
import Definitions.Def_NumberField_TateGlobalZeta
import Theorems.Thm_LanglandsTunnell_Converse_exists_isArchCompAt_of_isReal
import Theorems.Thm_RatIdele_exists_norm_apply_eq_ideleNorm_rpow
import Definitions.Def_AutomorphicForm_AdelicLsXi
import Definitions.Def_AutomorphicForm_SiegelCovering
import Definitions.Def_NumberField_AdelicVolume
import Theorems.Thm_AutomorphicForm_exists_finset_central_slab_covering_of_coversModCentre
import Theorems.Thm_AutomorphicForm_ideleNorm_det_globalPoints
import Theorems.Thm_NumberField_TateGlobal_continuous_ideleNorm_det
import Theorems.Thm_NumberField_TateGlobal_measurableSet_setOf_ideleNorm_det_mem_Icc
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_AutomorphicForm_RightConvolution
import Theorems.Thm_AutomorphicForm_adjoint_rightConv_weightedPairing_of_isLsXiFunction
import Theorems.Thm_AutomorphicForm_continuous_and_hasCompactSupport_of_isFactorizableTestFn
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_AutomorphicForm_ConstantTerm
import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_NumberField_AdelicBox
import Theorems.Thm_NumberField_denseRange_specialLinearGroup_map_finiteAdeleRing
import Mathlib.Data.Int.Basic
import Mathlib.Data.Nat.Find
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Definitions.Def_AutomorphicForm_CuspidalConstituent
import Theorems.Thm_LanglandsTunnell_exists_rightConv_ne_zero_mem_isotypicCuspSubmodule_mem_archCutSubmodule
import Theorems.Thm_AutomorphicForm_isotypicCuspSubmodule_inf_archCutSubmodule_le_iSup_isCuspConstituent
import Theorems.Thm_AutomorphicForm_isFactorizableTestFn_comp_inv_mul_of_isFactorizableTestFn
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Calculus.MeanValue
import Definitions.Def_AutomorphicForm_CarrierPins
import Theorems.Thm_AutomorphicForm_IsCuspidalFn_add
import Theorems.Thm_AutomorphicForm_IsCuspidalFn_smul
import Theorems.Thm_HeckeIntegralSeam_heckeCosetSum_eq_of_isHeckeCosetSystem
import Definitions.Def_AutomorphicForm_SmoothCuspRealization
import Definitions.Def_AutomorphicForm_CentreCutSiegelSet
import Theorems.Thm_AutomorphicForm_finiteDimensional_inf_levelInvariantSubmodule_inf_archCutSubmodule_of_isCuspConstituent
import Mathlib.Topology.Instances.RealVectorSpace
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Topology.Algebra.Constructions
import Mathlib.Topology.Instances.Matrix
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Normed.Module.Multilinear.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.MeasureTheory.Group.Integral
import Definitions.Def_AutomorphicForm_TwistedOrbital
import Theorems.Thm_AutomorphicForm_archDerivAt_rightConv_eq_rightConv_deriv_of_isFactorizableTestFn
import Theorems.Thm_AutomorphicForm_rightConv_apply_mul_eq_rightConv_comp_inv_mul_apply
import Theorems.Thm_AutomorphicForm_exists_isFundamentalDomain_globalPoints_range_restrict_ideleNorm_det_Icc
import Theorems.Thm_AutomorphicForm_archCasimirAt_comp_mul_archRealGLAt
import Theorems.Thm_AutomorphicForm_exists_finTestFactor_isUnitFactorizableAboveOfType_tendsto_rightConv_of_mem_archCutSubmodule
import Theorems.Thm_AutomorphicForm_isIsotypicCuspFormAt_rightConv_of_isFactorizableTestFn_of_support_subset_of_coversModCentre
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

p2m_attr_erase "ext" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.ext"
p2m_attr_erase "ext" "NumberField.InfinitePlace.Completion.ext"
namespace P2MW.S_LanglandsTunnell_exists_archCasimir_eigenvector_minimalWeight_of_continuous_realization
p2m_attr_erase "instance" "instCountableOfNumberField_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions AutomorphicForm.compactSpace_maximalCompactAway AutomorphicForm.compactSpace_adelicMaximalCompact AutomorphicForm.isProbabilityMeasure_maximalCompactHaar AutomorphicForm.isHaarMeasure_maximalCompactHaar AutomorphicForm.compactSpace_maximalCompactAt AutomorphicForm.isProbabilityMeasure_maximalCompactAwayHaar AutomorphicForm.isHaarMeasure_maximalCompactAwayHaar AutomorphicForm.isProbabilityMeasure_maximalCompactAtHaar AutomorphicForm.isHaarMeasure_maximalCompactAtHaar"
p2m_attr_erase "simp" "ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply AutomorphicForm.fnTwist_zero AutomorphicForm.fnTwist_apply"
p2m_attr_erase "simp" "LocalGL2.coe_localRepSome LocalGL2.coe_diagPi LocalGL2.coe_localRepInf LocalGL2.coe_localRepSome_inv LocalGL2.coe_unipotentInt LocalGL2.coe_weylInt LocalGL2.coe_diagPi_inv LocalGL2.transposeGL_val LocalGL2.transposeGL_one LocalGL2.swapUnit_val AdelicDock.coe_finEmbed AdelicDock.splice_apply_self AdelicDock.coe_localEmbed AutomorphicForm.CuspidalSpectrum.fdPins_μ AutomorphicForm.CuspidalSpectrum.fdPins_nS AutomorphicForm.CuspidalSpectrum.fdPins_ν AutomorphicForm.CuspidalSpectrum.fdPins_gen AutomorphicForm.CuspidalSpectrum.fdPins_U AutomorphicForm.CuspidalSpectrum.fdPins_D AutomorphicForm.CuspidalSpectrum.fdPins_Z AutomorphicForm.CuspidalSpectrum.mem_detNormSlab AutomorphicForm.CuspidalSpectrum.fdPins_eq AutomorphicForm.CuspidalSpectrum.fdPins_mS AutomorphicForm.mem_borelSubgroup_iff AutomorphicForm.borelDiagFst_apply_val AutomorphicForm.borelDiagSnd_apply_val AutomorphicForm.iotaZsqrtdNegTwo_apply"

set_option autoImplicit false

noncomputable section

namespace WeightShift

open scoped Real
p2m_open "AutomorphicForm~continuous_unipotentGL2~isIsotypicCuspFormAt_of_mem_isotypicCuspSubmodule Matrix"
open NumberField IsDedekindDomain NumberField.InfinitePlace NumberField.InfinitePlace.Completion

variable {K : Type} [Field K] [NumberField K]

private theorem det_of_symm_one : (Matrix.of (Matrix.of.symm (1 : Matrix (Fin 2) (Fin 2) ℝ))).det ≠ 0 := by
  rw [Equiv.apply_symm_apply, Matrix.det_one]
  exact one_ne_zero

private theorem det_coe_ne_zero (m : GL (Fin 2) ℝ) : ((m : Matrix (Fin 2) (Fin 2) ℝ)).det ≠ 0 :=
  ((Matrix.isUnit_iff_isUnit_det _).1 m.isUnit).ne_zero

private theorem archRealGLAt_eq_archRealLiftAt {w : InfinitePlace K} (hw : w.IsReal) (m : GL (Fin 2) ℝ) :
    archRealGLAt hw m = archRealLiftAt hw (Matrix.of.symm (m : Matrix (Fin 2) (Fin 2) ℝ)) := by
  have h := archRealLiftAt_mul_archRealGLAt hw det_of_symm_one m
  rw [archRealLiftAt_of_symm_one, one_mul, Equiv.apply_symm_apply, one_mul] at h
  exact h

private theorem hasDerivAt_conj_flow (k : GL (Fin 2) ℝ) (d : ArchDir) :
    HasDerivAt
      (fun t : ℝ =>
        (Matrix.of.symm (((k⁻¹ * archFlowMatrix d t * k : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)) :
          Fin 2 → Fin 2 → ℝ))
      (Matrix.of.symm
        (((k⁻¹ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) * archDirMatrix d * (k : Matrix (Fin 2) (Fin 2) ℝ)))
      0 := by
  rw [hasDerivAt_pi]
  intro i
  rw [hasDerivAt_pi]
  intro j
  simp only [Matrix.of_symm_apply, Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two]
  exact ((((hasDerivAt_archFlowMatrix_apply d 0 0).const_mul _).fun_add
      ((hasDerivAt_archFlowMatrix_apply d 1 0).const_mul _)).mul_const _).fun_add
    ((((hasDerivAt_archFlowMatrix_apply d 0 1).const_mul _).fun_add
      ((hasDerivAt_archFlowMatrix_apply d 1 1).const_mul _)).mul_const _)

private theorem archDerivAt_translate_eq_fderiv {w : InfinitePlace K} {hw : w.IsReal}
    {φ : AdelicGL2 (𝓞 K) K → ℂ} (hφ : IsArchSmoothAt hw φ) (k : GL (Fin 2) ℝ) (d : ArchDir)
    (g : AdelicGL2 (𝓞 K) K) :
    archDerivAt hw d (fun x => φ (x * archRealGLAt hw k)) g
      = fderiv ℝ (fun e : Fin 2 → Fin 2 → ℝ => φ (g * archRealGLAt hw k * archRealLiftAt hw e)) (Matrix.of.symm 1)
          (Matrix.of.symm
            (((k⁻¹ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) * archDirMatrix d
              * (k : Matrix (Fin 2) (Fin 2) ℝ))) := by
  have hopen := isOpen_setOf_det_ne_zero
  have hfun : (fun t : ℝ => (fun x => φ (x * archRealGLAt hw k)) (g * archFlowAt hw d t))
      = fun t : ℝ => (fun e : Fin 2 → Fin 2 → ℝ => φ (g * archRealGLAt hw k * archRealLiftAt hw e))
          (Matrix.of.symm (((k⁻¹ * archFlowMatrix d t * k : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ))) := by
    funext t
    show φ (g * archFlowAt hw d t * archRealGLAt hw k) = φ (g * archRealGLAt hw k * archRealLiftAt hw
      (Matrix.of.symm (((k⁻¹ * archFlowMatrix d t * k : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ))))
    rw [← archRealGLAt_eq_archRealLiftAt hw, map_mul, map_mul, map_inv, archFlowAt]
    exact congrArg φ (by group)
  have hdiff : HasFDerivAt (fun e : Fin 2 → Fin 2 → ℝ => φ (g * archRealGLAt hw k * archRealLiftAt hw e))
      (fderiv ℝ (fun e : Fin 2 → Fin 2 → ℝ => φ (g * archRealGLAt hw k * archRealLiftAt hw e)) (Matrix.of.symm 1))
      (Matrix.of.symm (((k⁻¹ * archFlowMatrix d 0 * k : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ))) := by
    rw [archFlowMatrix_zero, mul_one, inv_mul_cancel, Units.val_one]
    exact (((hφ (g * archRealGLAt hw k)).contDiffAt (hopen.mem_nhds det_of_symm_one)).differentiableAt
      (by simp)).hasFDerivAt
  show deriv (fun t : ℝ => (fun x => φ (x * archRealGLAt hw k)) (g * archFlowAt hw d t)) 0 = _
  rw [hfun]
  exact (hdiff.comp_hasDerivAt (0 : ℝ) (hasDerivAt_conj_flow k d)).deriv

private theorem archDerivAt_eq_fderiv {w : InfinitePlace K} {hw : w.IsReal}
    {φ : AdelicGL2 (𝓞 K) K → ℂ} (hφ : IsArchSmoothAt hw φ) (d : ArchDir) (x : AdelicGL2 (𝓞 K) K) :
    archDerivAt hw d φ x
      = fderiv ℝ (fun e : Fin 2 → Fin 2 → ℝ => φ (x * archRealLiftAt hw e)) (Matrix.of.symm 1)
          (Matrix.of.symm (archDirMatrix d)) := by
  have h := archDerivAt_translate_eq_fderiv hφ 1 d x
  simp only [map_one, mul_one, inv_one, Units.val_one, one_mul] at h
  exact h

private def dirEntry (A : Matrix (Fin 2) (Fin 2) ℝ) : ArchDir → ℝ
  | .H => A 0 0
  | .E => A 0 1
  | .Fm => A 1 0

private def adCoeff (k : GL (Fin 2) ℝ) (d : ArchDir) : ArchDir → ℝ :=
  dirEntry (((k⁻¹ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) * archDirMatrix d * (k : Matrix (Fin 2) (Fin 2) ℝ))

private def lin3 (c : ArchDir → ℝ) (v : ArchDir → ℂ) : ℂ :=
  (c .H : ℂ) * v .H + (c .E : ℂ) * v .E + (c .Fm : ℂ) * v .Fm

private theorem trace_conj_archDirMatrix (k : GL (Fin 2) ℝ) (d : ArchDir) :
    (((k⁻¹ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) * archDirMatrix d * (k : Matrix (Fin 2) (Fin 2) ℝ)) 1 1
      = -(((k⁻¹ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) * archDirMatrix d
          * (k : Matrix (Fin 2) (Fin 2) ℝ)) 0 0 := by
  have h0 : Matrix.trace
      (((k⁻¹ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) * archDirMatrix d * (k : Matrix (Fin 2) (Fin 2) ℝ)) = 0 := by
    rw [Matrix.trace_mul_cycle, Units.mul_inv, one_mul]
    cases d <;> simp [archDirMatrix, Matrix.trace_fin_two]
  rw [Matrix.trace_fin_two] at h0
  linarith

private theorem of_symm_conj_eq (k : GL (Fin 2) ℝ) (d : ArchDir) :
    (Matrix.of.symm
        (((k⁻¹ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) * archDirMatrix d * (k : Matrix (Fin 2) (Fin 2) ℝ)) :
      Fin 2 → Fin 2 → ℝ)
      = adCoeff k d .H • (Matrix.of.symm (archDirMatrix .H) : Fin 2 → Fin 2 → ℝ)
        + adCoeff k d .E • (Matrix.of.symm (archDirMatrix .E) : Fin 2 → Fin 2 → ℝ)
        + adCoeff k d .Fm • (Matrix.of.symm (archDirMatrix .Fm) : Fin 2 → Fin 2 → ℝ) := by
  have htr := trace_conj_archDirMatrix k d
  simp only [adCoeff, dirEntry]
  set A : Matrix (Fin 2) (Fin 2) ℝ :=
    ((k⁻¹ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) * archDirMatrix d * (k : Matrix (Fin 2) (Fin 2) ℝ)
  ext i j
  fin_cases i <;> fin_cases j <;> simp [archDirMatrix, htr]

private theorem archDerivAt_translate {w : InfinitePlace K} {hw : w.IsReal}
    {φ : AdelicGL2 (𝓞 K) K → ℂ} (hφ : IsArchSmoothAt hw φ) (k : GL (Fin 2) ℝ) (d : ArchDir)
    (g : AdelicGL2 (𝓞 K) K) :
    archDerivAt hw d (fun x => φ (x * archRealGLAt hw k)) g
      = lin3 (adCoeff k d) (fun d' => archDerivAt hw d' φ (g * archRealGLAt hw k)) := by
  rw [archDerivAt_translate_eq_fderiv hφ k d g, of_symm_conj_eq, map_add, map_add, map_smul, map_smul, map_smul,
    lin3, archDerivAt_eq_fderiv hφ .H, archDerivAt_eq_fderiv hφ .E, archDerivAt_eq_fderiv hφ .Fm,
    Complex.real_smul, Complex.real_smul, Complex.real_smul]

private theorem coe_inv_eq (k : GL (Fin 2) ℝ) :
    (k : Matrix (Fin 2) (Fin 2) ℝ)⁻¹
      = ((k : Matrix (Fin 2) (Fin 2) ℝ).det)⁻¹ •
          !![(k : Matrix (Fin 2) (Fin 2) ℝ) 1 1, -(k : Matrix (Fin 2) (Fin 2) ℝ) 0 1;
             -(k : Matrix (Fin 2) (Fin 2) ℝ) 1 0, (k : Matrix (Fin 2) (Fin 2) ℝ) 0 0] := by
  rw [Matrix.inv_def, Ring.inverse_eq_inv, Matrix.adjugate_fin_two]

private theorem archWeightCharℝ_apply_coe (n : ℤ) (k : rowIsometrySubgroup₀ ℝ) :
    (archWeightCharℝ n k : ℂ) = firstRowℂ (k : GL (Fin 2) ℝ) ^ n := by
  simp only [archWeightCharℝ, MonoidHom.coe_comp, Function.comp_apply, zpowGroupHom_apply,
    Units.val_zpow_eq_zpow_val]
  rfl

omit [NumberField K] in

private theorem symm_mem_rowIsometrySubgroup₀ {w : InfinitePlace K} (hw : w.IsReal) (k : rowIsometrySubgroup₀ ℝ) :
    glEquivOfRingEquiv (ringEquivRealOfIsReal hw).symm (k : GL (Fin 2) ℝ) ∈ rowIsometrySubgroup₀ w.Completion :=
  map_mem_rowIsometrySubgroup₀_of_normPreserving _
    (fun x => by
      rw [← norm_ringEquivRealOfIsReal hw ((ringEquivRealOfIsReal hw).symm x), RingEquiv.apply_symm_apply])
    _ k.2

omit [NumberField K] in

private theorem archWeightCharAt_symm {w : InfinitePlace K} (hw : w.IsReal) (n : ℤ) (k : rowIsometrySubgroup₀ ℝ) :
    archWeightCharAt hw n ⟨_, symm_mem_rowIsometrySubgroup₀ hw k⟩ = archWeightCharℝ n k := by
  have hmap : rowIsometrySubgroup₀Map (ringEquivRealOfIsReal hw) (norm_ringEquivRealOfIsReal hw)
      ⟨_, symm_mem_rowIsometrySubgroup₀ hw k⟩ = k := by
    apply Subtype.ext
    apply Units.ext
    ext i j
    simp [rowIsometrySubgroup₀Map, glEquivOfRingEquiv_apply_entry]
  simp only [archWeightCharAt, archWeightOneAt, archWeightCharℝ, MonoidHom.comp_apply, hmap]

private theorem archRealGLAt_eq_adelicArchGLInclAt {w : InfinitePlace K} (hw : w.IsReal) (m : GL (Fin 2) ℝ) :
    archRealGLAt hw m = adelicArchGLInclAt K w (glEquivOfRingEquiv (ringEquivRealOfIsReal hw).symm m) := rfl

private def HasRealWeight {w : InfinitePlace K} (hw : w.IsReal) (m : ℤ) (ψ : AdelicGL2 (𝓞 K) K → ℂ) : Prop :=
  ∀ (k : rowIsometrySubgroup₀ ℝ) (x : AdelicGL2 (𝓞 K) K),
    ψ (x * archRealGLAt hw (k : GL (Fin 2) ℝ)) = firstRowℂ (k : GL (Fin 2) ℝ) ^ m * ψ x

private theorem hasRealWeight_of_hasArchCharacterAt₀ {w : InfinitePlace K} (hw : w.IsReal) (m : ℤ)
    {ψ : AdelicGL2 (𝓞 K) K → ℂ} (hk : HasArchCharacterAt₀ K w (archWeightCharAt hw m) ψ) : HasRealWeight hw m ψ := by
  intro k x
  have h := hk ⟨_, symm_mem_rowIsometrySubgroup₀ hw k⟩ x
  rw [archWeightCharAt_symm hw m k, archWeightCharℝ_apply_coe] at h
  rw [archRealGLAt_eq_adelicArchGLInclAt]
  exact h

omit [NumberField K] in

private theorem mem_rowIsometrySubgroup₀_real_of_mem {w : InfinitePlace K} (hw : w.IsReal)
    (k : rowIsometrySubgroup₀ w.Completion) :
    glEquivOfRingEquiv (ringEquivRealOfIsReal hw) (k : GL (Fin 2) w.Completion) ∈ rowIsometrySubgroup₀ ℝ :=
  map_mem_rowIsometrySubgroup₀_of_normPreserving _ (norm_ringEquivRealOfIsReal hw) _ k.2

omit [NumberField K] in
private theorem archWeightCharAt_apply_coe {w : InfinitePlace K} (hw : w.IsReal) (m : ℤ)
    (k : rowIsometrySubgroup₀ w.Completion) :
    (archWeightCharAt hw m k : ℂ)
      = firstRowℂ (glEquivOfRingEquiv (ringEquivRealOfIsReal hw) (k : GL (Fin 2) w.Completion)) ^ m := by
  have h := archWeightCharℝ_apply_coe m
    (rowIsometrySubgroup₀Map (ringEquivRealOfIsReal hw) (norm_ringEquivRealOfIsReal hw) k)
  simp only [archWeightCharAt, archWeightOneAt, archWeightCharℝ, MonoidHom.comp_apply] at h ⊢
  exact h

private theorem hasArchCharacterAt₀_of_hasRealWeight {w : InfinitePlace K} (hw : w.IsReal) (m : ℤ)
    {ψ : AdelicGL2 (𝓞 K) K → ℂ} (h : HasRealWeight hw m ψ) : HasArchCharacterAt₀ K w (archWeightCharAt hw m) ψ := by
  intro k x
  have hx := h ⟨_, mem_rowIsometrySubgroup₀_real_of_mem hw k⟩ x
  have hι : archRealGLAt hw (glEquivOfRingEquiv (ringEquivRealOfIsReal hw) (k : GL (Fin 2) w.Completion))
      = adelicArchGLInclAt K w (k : GL (Fin 2) w.Completion) := archRealGLAt_glEquivOfRingEquiv hw _
  rw [archWeightCharAt_apply_coe, ← hι]
  exact hx

private def rotCoeff (a b : ℝ) : ArchDir → ArchDir → ℝ
  | .H, .H => a ^ 2 - b ^ 2
  | .H, .E => 2 * a * b
  | .H, .Fm => 2 * a * b
  | .E, .H => -(a * b)
  | .E, .E => a ^ 2
  | .E, .Fm => -(b ^ 2)
  | .Fm, .H => -(a * b)
  | .Fm, .E => -(b ^ 2)
  | .Fm, .Fm => a ^ 2

private theorem adCoeff_eq_rotCoeff {k : GL (Fin 2) ℝ} (hk : k ∈ rowIsometrySubgroup₀ ℝ) (d d' : ArchDir) :
    adCoeff k d d' = rotCoeff ((k : Matrix (Fin 2) (Fin 2) ℝ) 0 0) ((k : Matrix (Fin 2) (Fin 2) ℝ) 0 1) d d' := by
  obtain ⟨h10, h11, hab⟩ := entries_of_mem_rowIsometrySubgroup₀ hk
  have hdet : (k : Matrix (Fin 2) (Fin 2) ℝ).det = 1 := ((mem_rowIsometrySubgroup₀_iff ℝ).mp hk).1
  cases d <;> cases d' <;>
    simp only [adCoeff, dirEntry, rotCoeff, Matrix.coe_units_inv, coe_inv_eq, hdet, inv_one, one_smul] <;>
    simp [archDirMatrix, Matrix.mul_apply, Fin.sum_univ_two, h10, h11] <;> ring

private theorem rot_row_H (a b : ℝ) :
    (rotCoeff a b .H .H : ℂ) - Complex.I * rotCoeff a b .E .H - Complex.I * rotCoeff a b .Fm .H
      = (⟨a, b⟩ : ℂ) ^ 2 := by
  simp only [rotCoeff]
  apply Complex.ext <;> simp [pow_two]
  ring

private theorem rot_row_E (a b : ℝ) :
    (rotCoeff a b .H .E : ℂ) - Complex.I * rotCoeff a b .E .E - Complex.I * rotCoeff a b .Fm .E
      = -Complex.I * (⟨a, b⟩ : ℂ) ^ 2 := by
  simp only [rotCoeff]
  apply Complex.ext <;> simp [pow_two] <;> ring

private theorem rot_row_Fm (a b : ℝ) :
    (rotCoeff a b .H .Fm : ℂ) - Complex.I * rotCoeff a b .E .Fm - Complex.I * rotCoeff a b .Fm .Fm
      = -Complex.I * (⟨a, b⟩ : ℂ) ^ 2 := by
  simp only [rotCoeff]
  apply Complex.ext <;> simp [pow_two]
  ring

private def _root_.WeightShift.lowerOp {w : InfinitePlace K} (hw : w.IsReal) (φ : AdelicGL2 (𝓞 K) K → ℂ) : AdelicGL2 (𝓞 K) K → ℂ :=
  archDerivAt hw .H φ - Complex.I • (archDerivAt hw .E φ + archDerivAt hw .Fm φ)

p2m_export "WeightShift" "lowerOp"
private theorem zpow_mul_archDerivAt_eq {w : InfinitePlace K} {hw : w.IsReal} {m : ℤ} {ψ : AdelicGL2 (𝓞 K) K → ℂ}
    (hψ : IsArchSmoothAt hw ψ) (hm : HasRealWeight hw m ψ) (k : rowIsometrySubgroup₀ ℝ) (d : ArchDir)
    (x : AdelicGL2 (𝓞 K) K) :
    firstRowℂ (k : GL (Fin 2) ℝ) ^ m * archDerivAt hw d ψ x
      = lin3 (adCoeff (k : GL (Fin 2) ℝ) d)
          (fun d' => archDerivAt hw d' ψ (x * archRealGLAt hw (k : GL (Fin 2) ℝ))) := by
  have hfun : (fun y => ψ (y * archRealGLAt hw (k : GL (Fin 2) ℝ))) = (firstRowℂ (k : GL (Fin 2) ℝ) ^ m) • ψ := by
    funext y
    rw [hm k y]
    rfl
  have h := archDerivAt_translate hψ (k : GL (Fin 2) ℝ) d x
  rw [hfun, archDerivAt_smul] at h
  rw [← h]
  rfl

private theorem hasRealWeight_lowerOp {w : InfinitePlace K} {hw : w.IsReal} {m : ℤ} {ψ : AdelicGL2 (𝓞 K) K → ℂ}
    (hψ : IsArchSmoothAt hw ψ) (hm : HasRealWeight hw m ψ) : HasRealWeight hw (m - 2) (lowerOp hw ψ) := by
  intro k x
  have hH := zpow_mul_archDerivAt_eq hψ hm k .H x
  have hE := zpow_mul_archDerivAt_eq hψ hm k .E x
  have hF := zpow_mul_archDerivAt_eq hψ hm k .Fm x
  simp only [lin3, adCoeff_eq_rotCoeff k.2] at hH hE hF
  set a : ℝ := ((k : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 0 0 with ha
  set b : ℝ := ((k : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 0 1 with hb
  have rH := rot_row_H a b
  have rE := rot_row_E a b
  have rF := rot_row_Fm a b
  have hzab : (⟨a, b⟩ : ℂ) = firstRowℂ (k : GL (Fin 2) ℝ) := rfl
  rw [hzab] at rH rE rF
  set z : ℂ := firstRowℂ (k : GL (Fin 2) ℝ) with hz_def
  have hz : z ≠ 0 := firstRowℂ_ne_zero_of_mem k.2
  have hz2 : z ^ m = z ^ (m - 2) * z ^ 2 := by
    rw [← zpow_natCast, ← zpow_add₀ hz]
    congr 1
    ring

  have hcomb : z ^ 2 * lowerOp hw ψ (x * archRealGLAt hw (k : GL (Fin 2) ℝ)) = z ^ m * lowerOp hw ψ x := by
    simp only [lowerOp, Pi.sub_apply, Pi.smul_apply, Pi.add_apply, smul_eq_mul]
    linear_combination
      (-1 : ℂ) * hH + Complex.I * hE + Complex.I * hF
        - archDerivAt hw .H ψ (x * archRealGLAt hw (k : GL (Fin 2) ℝ)) * rH
        - archDerivAt hw .E ψ (x * archRealGLAt hw (k : GL (Fin 2) ℝ)) * rE
        - archDerivAt hw .Fm ψ (x * archRealGLAt hw (k : GL (Fin 2) ℝ)) * rF
  have h2 : z ^ 2 ≠ 0 := pow_ne_zero 2 hz
  apply mul_left_cancel₀ h2
  rw [hcomb, hz2]
  ring

private def reflectJ {w : InfinitePlace K} (hw : w.IsReal) (φ : AdelicGL2 (𝓞 K) K → ℂ) : AdelicGL2 (𝓞 K) K → ℂ :=
  fun x => φ (x * archRealGLAt hw UpperHalfPlane.J)

private theorem J_mul_J : UpperHalfPlane.J * UpperHalfPlane.J = 1 := by
  rw [← sq, UpperHalfPlane.J_sq]

private theorem reflectJ_apply_mul_J {w : InfinitePlace K} (hw : w.IsReal) (φ : AdelicGL2 (𝓞 K) K → ℂ)
    (x : AdelicGL2 (𝓞 K) K) : reflectJ hw φ (x * archRealGLAt hw UpperHalfPlane.J) = φ x := by
  simp only [reflectJ]
  rw [mul_assoc, ← map_mul, J_mul_J, map_one, mul_one]

private theorem isArchSmoothAt_translate {w : InfinitePlace K} {hw : w.IsReal}
    {φ : AdelicGL2 (𝓞 K) K → ℂ} (hφ : IsArchSmoothAt hw φ) (k : GL (Fin 2) ℝ) :
    IsArchSmoothAt hw (fun x => φ (x * archRealGLAt hw k)) := by
  intro g
  have hmaps : Set.MapsTo
      (fun e : Fin 2 → Fin 2 → ℝ =>
        (Matrix.of.symm (Matrix.of e * (k : Matrix (Fin 2) (Fin 2) ℝ)) : Fin 2 → Fin 2 → ℝ))
      {e | (Matrix.of e).det ≠ 0} {e | (Matrix.of e).det ≠ 0} := by
    intro e he
    show (Matrix.of (Matrix.of.symm (Matrix.of e * (k : Matrix (Fin 2) (Fin 2) ℝ)))).det ≠ 0
    rw [Equiv.apply_symm_apply, Matrix.det_mul]
    exact mul_ne_zero he (det_coe_ne_zero k)
  refine ((hφ g).comp (contDiff_of_symm_mul_const (k : Matrix (Fin 2) (Fin 2) ℝ)).contDiffOn hmaps).congr
    fun e he => ?_
  show φ (g * archRealLiftAt hw e * archRealGLAt hw k)
    = φ (g * archRealLiftAt hw (Matrix.of.symm (Matrix.of e * (k : Matrix (Fin 2) (Fin 2) ℝ))))
  rw [mul_assoc, archRealLiftAt_mul_archRealGLAt hw he]

private theorem isArchSmoothAt_reflectJ {w : InfinitePlace K} {hw : w.IsReal} {φ : AdelicGL2 (𝓞 K) K → ℂ}
    (hφ : IsArchSmoothAt hw φ) : IsArchSmoothAt hw (reflectJ hw φ) :=
  isArchSmoothAt_translate hφ UpperHalfPlane.J

private theorem archCasimirAt_reflectJ {w : InfinitePlace K} {hw : w.IsReal} {φ : AdelicGL2 (𝓞 K) K → ℂ}
    (hAd : ∀ (ψ : AdelicGL2 (𝓞 K) K → ℂ), IsArchSmoothAt hw ψ → ∀ k : GL (Fin 2) ℝ,
      archCasimirAt hw (fun x => ψ (x * archRealGLAt hw k)) = fun x => archCasimirAt hw ψ (x * archRealGLAt hw k))
    (hφ : IsArchSmoothAt hw φ) {lam : ℂ} (hΩ : archCasimirAt hw φ = lam • φ) :
    archCasimirAt hw (reflectJ hw φ) = lam • reflectJ hw φ := by
  have h := hAd φ hφ UpperHalfPlane.J
  rw [hΩ] at h
  exact h

private theorem conjJ_coe {k : GL (Fin 2) ℝ} (hk : k ∈ rowIsometrySubgroup₀ ℝ) :
    ((UpperHalfPlane.J * k * UpperHalfPlane.J : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)
      = !![(k : Matrix (Fin 2) (Fin 2) ℝ) 0 0, -(k : Matrix (Fin 2) (Fin 2) ℝ) 0 1;
           (k : Matrix (Fin 2) (Fin 2) ℝ) 0 1, (k : Matrix (Fin 2) (Fin 2) ℝ) 0 0] := by
  obtain ⟨h10, h11, -⟩ := entries_of_mem_rowIsometrySubgroup₀ hk
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Units.val_mul, UpperHalfPlane.val_J, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two, h10, h11]

private theorem conjJ_mem {k : GL (Fin 2) ℝ} (hk : k ∈ rowIsometrySubgroup₀ ℝ) :
    UpperHalfPlane.J * k * UpperHalfPlane.J ∈ rowIsometrySubgroup₀ ℝ := by
  obtain ⟨-, -, hab⟩ := entries_of_mem_rowIsometrySubgroup₀ hk
  have hdet : ((UpperHalfPlane.J * k * UpperHalfPlane.J : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ).det = 1 := by
    rw [conjJ_coe hk, Matrix.det_fin_two_of]
    nlinarith [hab]
  rw [mem_rowIsometrySubgroup₀_iff]
  refine ⟨hdet, ?_, ?_⟩
  · rw [hdet, norm_one]
  · intro x y
    simp only [conjJ_coe hk, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one, Real.norm_eq_abs, sq_abs]
    nlinarith [hab]

private theorem firstRowℂ_conjJ {k : GL (Fin 2) ℝ} (hk : k ∈ rowIsometrySubgroup₀ ℝ) :
    firstRowℂ (UpperHalfPlane.J * k * UpperHalfPlane.J) = (firstRowℂ k)⁻¹ := by
  have hn := normSq_firstRowℂ_of_mem hk
  apply Complex.ext
  · rw [Complex.inv_re, hn]
    simp [firstRowℂ, conjJ_coe hk]
  · rw [Complex.inv_im, hn]
    simp [firstRowℂ, conjJ_coe hk]

private theorem mul_J_eq_J_mul_conjJ (k : GL (Fin 2) ℝ) :
    k * UpperHalfPlane.J = UpperHalfPlane.J * (UpperHalfPlane.J * k * UpperHalfPlane.J) := by
  rw [← mul_assoc, ← mul_assoc, J_mul_J, one_mul]

private theorem hasRealWeight_reflectJ {w : InfinitePlace K} {hw : w.IsReal} {m : ℤ} {ψ : AdelicGL2 (𝓞 K) K → ℂ}
    (h : HasRealWeight hw m ψ) : HasRealWeight hw (-m) (reflectJ hw ψ) := by
  intro k x
  have hk : ψ (x * archRealGLAt hw UpperHalfPlane.J *
        archRealGLAt hw (UpperHalfPlane.J * (k : GL (Fin 2) ℝ) * UpperHalfPlane.J))
      = firstRowℂ (UpperHalfPlane.J * (k : GL (Fin 2) ℝ) * UpperHalfPlane.J) ^ m *
          ψ (x * archRealGLAt hw UpperHalfPlane.J) :=
    h ⟨_, conjJ_mem k.2⟩ (x * archRealGLAt hw UpperHalfPlane.J)
  simp only [reflectJ]
  rw [mul_assoc, ← map_mul, mul_J_eq_J_mul_conjJ, map_mul, ← mul_assoc, hk, firstRowℂ_conjJ k.2, _root_.inv_zpow']

private theorem exists_reflectJ_eigen {w : InfinitePlace K} {hw : w.IsReal}
    (hAd : ∀ (χ : AdelicGL2 (𝓞 K) K → ℂ), IsArchSmoothAt hw χ → ∀ k : GL (Fin 2) ℝ,
      archCasimirAt hw (fun x => χ (x * archRealGLAt hw k)) = fun x => archCasimirAt hw χ (x * archRealGLAt hw k))
    {ψ : AdelicGL2 (𝓞 K) K → ℂ} (hψ0 : ψ ≠ 0) (hψ : IsArchSmoothAt hw ψ) {lam : ℂ}
    (hΩ : archCasimirAt hw ψ = lam • ψ) :
    ∃ (φ : AdelicGL2 (𝓞 K) K → ℂ) (s : ZMod 2), φ ≠ 0 ∧ (φ = ψ + reflectJ hw ψ ∨ φ = ψ - reflectJ hw ψ) ∧
      IsArchSmoothAt hw φ ∧ archCasimirAt hw φ = lam • φ ∧
        ∀ g : AdelicGL2 (𝓞 K) K, φ (g * archRealGLAt hw UpperHalfPlane.J) = (-1 : ℂ) ^ s.val * φ g := by
  have hR := isArchSmoothAt_reflectJ hψ
  have hΩR := archCasimirAt_reflectJ hAd hψ hΩ
  by_cases hplus : ψ + reflectJ hw ψ = 0
  ·
    refine ⟨ψ - reflectJ hw ψ, 1, ?_, Or.inr rfl, ?_, ?_, ?_⟩
    · intro h0
      apply hψ0
      funext x
      have h1 := congrFun hplus x
      have h2 := congrFun h0 x
      simp only [Pi.add_apply, Pi.sub_apply, Pi.zero_apply] at h1 h2 ⊢
      linear_combination (1 / 2 : ℂ) * h1 + (1 / 2 : ℂ) * h2
    · rw [sub_eq_add_neg, ← neg_one_smul ℂ (reflectJ hw ψ)]
      exact hψ.add (hR.smul _)
    · rw [sub_eq_add_neg, ← neg_one_smul ℂ (reflectJ hw ψ), archCasimirAt_add hψ (hR.smul _), archCasimirAt_smul, hΩ,
        hΩR, smul_add, smul_comm]
    · intro g
      have h1 := congrFun hplus (g * archRealGLAt hw UpperHalfPlane.J)
      have h2 := congrFun hplus g
      simp only [Pi.add_apply, Pi.zero_apply, reflectJ_apply_mul_J] at h1
      simp only [Pi.add_apply, Pi.zero_apply] at h2
      simp only [Pi.sub_apply, reflectJ_apply_mul_J, ZMod.val_one, pow_one]
      linear_combination h1 - h2
  · refine ⟨ψ + reflectJ hw ψ, 0, hplus, Or.inl rfl, hψ.add hR, ?_, ?_⟩
    · rw [archCasimirAt_add hψ hR, hΩ, hΩR, smul_add]
    · intro g
      simp only [Pi.add_apply, reflectJ_apply_mul_J, ZMod.val_zero, pow_zero, one_mul]
      simp only [reflectJ]
      ring

private def _root_.WeightShift.raiseOp {w : InfinitePlace K} (hw : w.IsReal) (φ : AdelicGL2 (𝓞 K) K → ℂ) : AdelicGL2 (𝓞 K) K → ℂ :=
  archDerivAt hw .H φ + Complex.I • (archDerivAt hw .E φ + archDerivAt hw .Fm φ)

p2m_export "WeightShift" "raiseOp"
private theorem rot_row_H' (a b : ℝ) :
    (rotCoeff a b .H .H : ℂ) + Complex.I * rotCoeff a b .E .H + Complex.I * rotCoeff a b .Fm .H
      = (⟨a, -b⟩ : ℂ) ^ 2 := by
  simp only [rotCoeff]
  apply Complex.ext <;> simp [pow_two]
  ring

private theorem rot_row_E' (a b : ℝ) :
    (rotCoeff a b .H .E : ℂ) + Complex.I * rotCoeff a b .E .E + Complex.I * rotCoeff a b .Fm .E
      = Complex.I * (⟨a, -b⟩ : ℂ) ^ 2 := by
  simp only [rotCoeff]
  apply Complex.ext <;> simp [pow_two] <;> ring

private theorem rot_row_Fm' (a b : ℝ) :
    (rotCoeff a b .H .Fm : ℂ) + Complex.I * rotCoeff a b .E .Fm + Complex.I * rotCoeff a b .Fm .Fm
      = Complex.I * (⟨a, -b⟩ : ℂ) ^ 2 := by
  simp only [rotCoeff]
  apply Complex.ext <;> simp [pow_two] <;> ring

private theorem firstRowℂ_mul_conj {k : GL (Fin 2) ℝ} (hk : k ∈ rowIsometrySubgroup₀ ℝ) :
    firstRowℂ k * (⟨(k : Matrix (Fin 2) (Fin 2) ℝ) 0 0, -((k : Matrix (Fin 2) (Fin 2) ℝ) 0 1)⟩ : ℂ) = 1 := by
  have hab : ((k : Matrix (Fin 2) (Fin 2) ℝ) 0 0) ^ 2 + ((k : Matrix (Fin 2) (Fin 2) ℝ) 0 1) ^ 2 = 1 :=
    (entries_of_mem_rowIsometrySubgroup₀ hk).2.2
  have hz : firstRowℂ k = ⟨(k : Matrix (Fin 2) (Fin 2) ℝ) 0 0, (k : Matrix (Fin 2) (Fin 2) ℝ) 0 1⟩ := rfl
  rw [hz]
  refine Complex.ext ?_ ?_
  · simp only [Complex.mul_re, Complex.one_re]
    linear_combination hab
  · simp only [Complex.mul_im, Complex.one_im]
    ring

private theorem hasRealWeight_raiseOp {w : InfinitePlace K} {hw : w.IsReal} {m : ℤ} {ψ : AdelicGL2 (𝓞 K) K → ℂ}
    (hψ : IsArchSmoothAt hw ψ) (hm : HasRealWeight hw m ψ) : HasRealWeight hw (m + 2) (raiseOp hw ψ) := by
  intro k x
  have hH := zpow_mul_archDerivAt_eq hψ hm k .H x
  have hE := zpow_mul_archDerivAt_eq hψ hm k .E x
  have hF := zpow_mul_archDerivAt_eq hψ hm k .Fm x
  simp only [lin3, adCoeff_eq_rotCoeff k.2] at hH hE hF
  have hzzb : firstRowℂ (k : GL (Fin 2) ℝ)
      * (⟨((k : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 0 0,
          -(((k : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 0 1)⟩ : ℂ) = 1 :=
    firstRowℂ_mul_conj k.2
  set a : ℝ := ((k : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 0 0 with ha
  set b : ℝ := ((k : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 0 1 with hb
  have rH := rot_row_H' a b
  have rE := rot_row_E' a b
  have rF := rot_row_Fm' a b
  set zb : ℂ := (⟨a, -b⟩ : ℂ) with hzb_def
  set z : ℂ := firstRowℂ (k : GL (Fin 2) ℝ) with hz_def
  have hz : z ≠ 0 := firstRowℂ_ne_zero_of_mem k.2
  have hz2 : z ^ (m + 2) = z ^ m * z ^ 2 := by
    rw [← zpow_natCast, ← zpow_add₀ hz]
    congr 1

  have hcomb : zb ^ 2 * raiseOp hw ψ (x * archRealGLAt hw (k : GL (Fin 2) ℝ)) = z ^ m * raiseOp hw ψ x := by
    simp only [raiseOp, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    linear_combination
      (-1 : ℂ) * hH - Complex.I * hE - Complex.I * hF
        - archDerivAt hw .H ψ (x * archRealGLAt hw (k : GL (Fin 2) ℝ)) * rH
        - archDerivAt hw .E ψ (x * archRealGLAt hw (k : GL (Fin 2) ℝ)) * rE
        - archDerivAt hw .Fm ψ (x * archRealGLAt hw (k : GL (Fin 2) ℝ)) * rF
  calc raiseOp hw ψ (x * archRealGLAt hw (k : GL (Fin 2) ℝ))
      = (z * zb) ^ 2 * raiseOp hw ψ (x * archRealGLAt hw (k : GL (Fin 2) ℝ)) := by rw [hzzb, one_pow, one_mul]
    _ = z ^ 2 * (zb ^ 2 * raiseOp hw ψ (x * archRealGLAt hw (k : GL (Fin 2) ℝ))) := by ring
    _ = z ^ 2 * (z ^ m * raiseOp hw ψ x) := by rw [hcomb]
    _ = z ^ (m + 2) * raiseOp hw ψ x := by rw [hz2]; ring

end WeightShift

namespace Ladder

open scoped Real
p2m_open "AutomorphicForm~continuous_unipotentGL2~isIsotypicCuspFormAt_of_mem_isotypicCuspSubmodule Matrix"
open NumberField IsDedekindDomain NumberField.InfinitePlace NumberField.InfinitePlace.Completion

variable {K : Type} [Field K] [NumberField K]

private theorem det_of_symm_one : (Matrix.of (Matrix.of.symm (1 : Matrix (Fin 2) (Fin 2) ℝ))).det ≠ 0 := by
  rw [Equiv.apply_symm_apply, Matrix.det_one]
  exact one_ne_zero

private theorem det_coe_ne_zero (m : GL (Fin 2) ℝ) : ((m : Matrix (Fin 2) (Fin 2) ℝ)).det ≠ 0 :=
  ((Matrix.isUnit_iff_isUnit_det _).1 m.isUnit).ne_zero

private theorem archRealGLAt_eq_archRealLiftAt {w : InfinitePlace K} (hw : w.IsReal) (m : GL (Fin 2) ℝ) :
    archRealGLAt hw m = archRealLiftAt hw (Matrix.of.symm (m : Matrix (Fin 2) (Fin 2) ℝ)) := by
  have h := archRealLiftAt_mul_archRealGLAt hw det_of_symm_one m
  rw [archRealLiftAt_of_symm_one, one_mul, Equiv.apply_symm_apply, one_mul] at h
  exact h

private theorem hasDerivAt_conj_flow (k : GL (Fin 2) ℝ) (d : ArchDir) :
    HasDerivAt
      (fun t : ℝ =>
        (Matrix.of.symm (((k⁻¹ * archFlowMatrix d t * k : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)) :
          Fin 2 → Fin 2 → ℝ))
      (Matrix.of.symm
        (((k⁻¹ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) * archDirMatrix d * (k : Matrix (Fin 2) (Fin 2) ℝ)))
      0 := by
  rw [hasDerivAt_pi]
  intro i
  rw [hasDerivAt_pi]
  intro j
  simp only [Matrix.of_symm_apply, Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two]
  exact ((((hasDerivAt_archFlowMatrix_apply d 0 0).const_mul _).fun_add
      ((hasDerivAt_archFlowMatrix_apply d 1 0).const_mul _)).mul_const _).fun_add
    ((((hasDerivAt_archFlowMatrix_apply d 0 1).const_mul _).fun_add
      ((hasDerivAt_archFlowMatrix_apply d 1 1).const_mul _)).mul_const _)

private theorem archDerivAt_translate_eq_fderiv {w : InfinitePlace K} {hw : w.IsReal}
    {φ : AdelicGL2 (𝓞 K) K → ℂ} (hφ : IsArchSmoothAt hw φ) (k : GL (Fin 2) ℝ) (d : ArchDir)
    (g : AdelicGL2 (𝓞 K) K) :
    archDerivAt hw d (fun x => φ (x * archRealGLAt hw k)) g
      = fderiv ℝ (fun e : Fin 2 → Fin 2 → ℝ => φ (g * archRealGLAt hw k * archRealLiftAt hw e)) (Matrix.of.symm 1)
          (Matrix.of.symm
            (((k⁻¹ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) * archDirMatrix d
              * (k : Matrix (Fin 2) (Fin 2) ℝ))) := by
  have hopen := isOpen_setOf_det_ne_zero
  have hfun : (fun t : ℝ => (fun x => φ (x * archRealGLAt hw k)) (g * archFlowAt hw d t))
      = fun t : ℝ => (fun e : Fin 2 → Fin 2 → ℝ => φ (g * archRealGLAt hw k * archRealLiftAt hw e))
          (Matrix.of.symm (((k⁻¹ * archFlowMatrix d t * k : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ))) := by
    funext t
    show φ (g * archFlowAt hw d t * archRealGLAt hw k) = φ (g * archRealGLAt hw k * archRealLiftAt hw
      (Matrix.of.symm (((k⁻¹ * archFlowMatrix d t * k : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ))))
    rw [← archRealGLAt_eq_archRealLiftAt hw, map_mul, map_mul, map_inv, archFlowAt]
    exact congrArg φ (by group)
  have hdiff : HasFDerivAt (fun e : Fin 2 → Fin 2 → ℝ => φ (g * archRealGLAt hw k * archRealLiftAt hw e))
      (fderiv ℝ (fun e : Fin 2 → Fin 2 → ℝ => φ (g * archRealGLAt hw k * archRealLiftAt hw e)) (Matrix.of.symm 1))
      (Matrix.of.symm (((k⁻¹ * archFlowMatrix d 0 * k : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ))) := by
    rw [archFlowMatrix_zero, mul_one, inv_mul_cancel, Units.val_one]
    exact (((hφ (g * archRealGLAt hw k)).contDiffAt (hopen.mem_nhds det_of_symm_one)).differentiableAt
      (by simp)).hasFDerivAt
  show deriv (fun t : ℝ => (fun x => φ (x * archRealGLAt hw k)) (g * archFlowAt hw d t)) 0 = _
  rw [hfun]
  exact (hdiff.comp_hasDerivAt (0 : ℝ) (hasDerivAt_conj_flow k d)).deriv

private theorem archDerivAt_eq_fderiv {w : InfinitePlace K} {hw : w.IsReal}
    {φ : AdelicGL2 (𝓞 K) K → ℂ} (hφ : IsArchSmoothAt hw φ) (d : ArchDir) (x : AdelicGL2 (𝓞 K) K) :
    archDerivAt hw d φ x
      = fderiv ℝ (fun e : Fin 2 → Fin 2 → ℝ => φ (x * archRealLiftAt hw e)) (Matrix.of.symm 1)
          (Matrix.of.symm (archDirMatrix d)) := by
  have h := archDerivAt_translate_eq_fderiv hφ 1 d x
  simp only [map_one, mul_one, inv_one, Units.val_one, one_mul] at h
  exact h

private theorem archDerivAt_mul_archRealGLAt_eq_fderiv {w : InfinitePlace K} {hw : w.IsReal}
    {φ : AdelicGL2 (𝓞 K) K → ℂ} (hφ : IsArchSmoothAt hw φ) (d : ArchDir) (x : AdelicGL2 (𝓞 K) K)
    (m : GL (Fin 2) ℝ) :
    archDerivAt hw d φ (x * archRealGLAt hw m)
      = fderiv ℝ (fun e : Fin 2 → Fin 2 → ℝ => φ (x * archRealLiftAt hw e))
          (Matrix.of.symm (m : Matrix (Fin 2) (Fin 2) ℝ))
          (Matrix.of.symm ((m : Matrix (Fin 2) (Fin 2) ℝ) * archDirMatrix d)) := by
  have hopen := isOpen_setOf_det_ne_zero
  have hdet : (Matrix.of (Matrix.of.symm (m : Matrix (Fin 2) (Fin 2) ℝ))).det ≠ 0 := by
    rw [Equiv.apply_symm_apply]
    exact det_coe_ne_zero m
  have hfun : (fun t : ℝ => φ (x * archRealGLAt hw m * archFlowAt hw d t))
      = fun t : ℝ => (fun e : Fin 2 → Fin 2 → ℝ => φ (x * archRealLiftAt hw e))
          (Matrix.of.symm ((m : Matrix (Fin 2) (Fin 2) ℝ) * (archFlowMatrix d t : Matrix (Fin 2) (Fin 2) ℝ))) := by
    funext t
    show φ (x * archRealGLAt hw m * archFlowAt hw d t) = φ (x * archRealLiftAt hw _)
    rw [← Units.val_mul, ← archRealGLAt_eq_archRealLiftAt hw, map_mul, archFlowAt, mul_assoc]
  have hdiff : HasFDerivAt (fun e : Fin 2 → Fin 2 → ℝ => φ (x * archRealLiftAt hw e))
      (fderiv ℝ (fun e : Fin 2 → Fin 2 → ℝ => φ (x * archRealLiftAt hw e))
        (Matrix.of.symm (m : Matrix (Fin 2) (Fin 2) ℝ)))
      (Matrix.of.symm ((m : Matrix (Fin 2) (Fin 2) ℝ) * (archFlowMatrix d 0 : Matrix (Fin 2) (Fin 2) ℝ))) := by
    rw [archFlowMatrix_zero, Units.val_one, mul_one]
    exact (((hφ x).contDiffAt (hopen.mem_nhds hdet)).differentiableAt (by simp)).hasFDerivAt
  have hc := hasDerivAt_of_symm_mul_archFlowMatrix (Matrix.of.symm (m : Matrix (Fin 2) (Fin 2) ℝ)) d
  rw [Equiv.apply_symm_apply] at hc
  show deriv (fun t : ℝ => φ (x * archRealGLAt hw m * archFlowAt hw d t)) 0 = _
  rw [hfun]
  simpa only [Function.comp_def] using (hdiff.comp_hasDerivAt (0 : ℝ) hc).deriv

private theorem hasDerivAt_of_symm_archFlowMatrix_mul (d : ArchDir) (A : Matrix (Fin 2) (Fin 2) ℝ) :
    HasDerivAt
      (fun t : ℝ => (Matrix.of.symm ((archFlowMatrix d t : Matrix (Fin 2) (Fin 2) ℝ) * A) : Fin 2 → Fin 2 → ℝ))
      (Matrix.of.symm (archDirMatrix d * A)) 0 := by
  rw [hasDerivAt_pi]
  intro i
  rw [hasDerivAt_pi]
  intro j
  simp only [Matrix.of_symm_apply, Matrix.mul_apply, Fin.sum_univ_two]
  exact ((hasDerivAt_archFlowMatrix_apply d i 0).mul_const _).fun_add
    ((hasDerivAt_archFlowMatrix_apply d i 1).mul_const _)

private theorem archDerivAt_archDerivAt_eq {w : InfinitePlace K} {hw : w.IsReal}
    {φ : AdelicGL2 (𝓞 K) K → ℂ} (hφ : IsArchSmoothAt hw φ) (d d' : ArchDir) (x : AdelicGL2 (𝓞 K) K) :
    archDerivAt hw d (archDerivAt hw d' φ) x
      = fderiv ℝ (fderiv ℝ (fun e : Fin 2 → Fin 2 → ℝ => φ (x * archRealLiftAt hw e))) (Matrix.of.symm 1)
            (Matrix.of.symm (archDirMatrix d)) (Matrix.of.symm (archDirMatrix d'))
        + fderiv ℝ (fun e : Fin 2 → Fin 2 → ℝ => φ (x * archRealLiftAt hw e)) (Matrix.of.symm 1)
            (Matrix.of.symm (archDirMatrix d * archDirMatrix d')) := by
  have hopen := isOpen_setOf_det_ne_zero
  set ψ : (Fin 2 → Fin 2 → ℝ) → ℂ := fun e => φ (x * archRealLiftAt hw e)
  have h2 : ContDiffOn ℝ 2 ψ {e | (Matrix.of e).det ≠ 0} := by
    simpa using contDiffOn_infty.mp (hφ x) 2
  have h1 : ContDiffOn ℝ 1 (fderiv ℝ ψ) {e | (Matrix.of e).det ≠ 0} :=
    h2.fderiv_of_isOpen hopen (le_of_eq one_add_one_eq_two)

  have hfun : (fun t : ℝ => archDerivAt hw d' φ (x * archFlowAt hw d t))
      = fun t : ℝ => fderiv ℝ ψ (Matrix.of.symm ((archFlowMatrix d t : Matrix (Fin 2) (Fin 2) ℝ) * 1))
          (Matrix.of.symm ((archFlowMatrix d t : Matrix (Fin 2) (Fin 2) ℝ) * archDirMatrix d')) := by
    funext t
    rw [archFlowAt, archDerivAt_mul_archRealGLAt_eq_fderiv hφ d' x, mul_one]

  have hc : HasDerivAt (fun t : ℝ => fderiv ℝ ψ (Matrix.of.symm ((archFlowMatrix d t : Matrix (Fin 2) (Fin 2) ℝ) * 1)))
      (fderiv ℝ (fderiv ℝ ψ) (Matrix.of.symm 1) (Matrix.of.symm (archDirMatrix d * 1))) 0 := by
    have hd1 : HasFDerivAt (fderiv ℝ ψ) (fderiv ℝ (fderiv ℝ ψ) (Matrix.of.symm 1))
        (Matrix.of.symm ((archFlowMatrix d 0 : Matrix (Fin 2) (Fin 2) ℝ) * 1)) := by
      rw [archFlowMatrix_zero, Units.val_one, mul_one]
      exact ((h1.contDiffAt (hopen.mem_nhds det_of_symm_one)).differentiableAt one_ne_zero).hasFDerivAt
    simpa only [Function.comp_def] using hd1.comp_hasDerivAt (0 : ℝ) (hasDerivAt_of_symm_archFlowMatrix_mul d 1)
  have hu := hasDerivAt_of_symm_archFlowMatrix_mul d (archDirMatrix d')
  have h := (hc.clm_apply hu).deriv
  show deriv (fun t : ℝ => archDerivAt hw d' φ (x * archFlowAt hw d t)) 0 = _
  rw [hfun, h]
  simp only [archFlowMatrix_zero, Units.val_one, mul_one, one_mul]

private theorem of_symm_sub (A B : Matrix (Fin 2) (Fin 2) ℝ) :
    (Matrix.of.symm (A - B) : Fin 2 → Fin 2 → ℝ) = Matrix.of.symm A - Matrix.of.symm B := rfl

private theorem archDirMatrix_E_mul_Fm_sub :
    archDirMatrix .E * archDirMatrix .Fm - archDirMatrix .Fm * archDirMatrix .E = archDirMatrix .H := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [archDirMatrix]

private theorem archDerivAt_comm_E_Fm {w : InfinitePlace K} {hw : w.IsReal}
    {φ : AdelicGL2 (𝓞 K) K → ℂ} (hφ : IsArchSmoothAt hw φ) (x : AdelicGL2 (𝓞 K) K) :
    archDerivAt hw .E (archDerivAt hw .Fm φ) x - archDerivAt hw .Fm (archDerivAt hw .E φ) x
      = archDerivAt hw .H φ x := by
  have hopen := isOpen_setOf_det_ne_zero
  have h2 : ContDiffOn ℝ 2 (fun e : Fin 2 → Fin 2 → ℝ => φ (x * archRealLiftAt hw e)) {e | (Matrix.of e).det ≠ 0} := by
    simpa using contDiffOn_infty.mp (hφ x) 2
  have hsymm := (h2.contDiffAt (hopen.mem_nhds det_of_symm_one)).isSymmSndFDerivAt (by simp)
  rw [archDerivAt_archDerivAt_eq hφ .E .Fm x, archDerivAt_archDerivAt_eq hφ .Fm .E x,
    hsymm (Matrix.of.symm (archDirMatrix .Fm)) (Matrix.of.symm (archDirMatrix .E)), add_sub_add_left_eq_sub,
    ← map_sub, ← of_symm_sub, archDirMatrix_E_mul_Fm_sub, archDerivAt_eq_fderiv hφ .H x]

private def rotK (s : ℝ) : GL (Fin 2) ℝ where
  val := !![(Real.sqrt (1 + s ^ 2))⁻¹, -(s * (Real.sqrt (1 + s ^ 2))⁻¹);
    s * (Real.sqrt (1 + s ^ 2))⁻¹, (Real.sqrt (1 + s ^ 2))⁻¹]
  inv := !![(Real.sqrt (1 + s ^ 2))⁻¹, s * (Real.sqrt (1 + s ^ 2))⁻¹;
    -(s * (Real.sqrt (1 + s ^ 2))⁻¹), (Real.sqrt (1 + s ^ 2))⁻¹]
  val_inv := by
    have hr : Real.sqrt (1 + s ^ 2) ^ 2 = 1 + s ^ 2 := Real.sq_sqrt (by positivity)
    have hr0 : Real.sqrt (1 + s ^ 2) ≠ 0 := (Real.sqrt_pos.mpr (by positivity)).ne'
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;>
      (field_simp; nlinarith [hr])
  inv_val := by
    have hr : Real.sqrt (1 + s ^ 2) ^ 2 = 1 + s ^ 2 := Real.sq_sqrt (by positivity)
    have hr0 : Real.sqrt (1 + s ^ 2) ≠ 0 := (Real.sqrt_pos.mpr (by positivity)).ne'
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;>
      (field_simp; nlinarith [hr])

private theorem rotK_coe (s : ℝ) :
    (rotK s : Matrix (Fin 2) (Fin 2) ℝ)
      = !![(Real.sqrt (1 + s ^ 2))⁻¹, -(s * (Real.sqrt (1 + s ^ 2))⁻¹);
          s * (Real.sqrt (1 + s ^ 2))⁻¹, (Real.sqrt (1 + s ^ 2))⁻¹] :=
  rfl

private theorem rotK_mem (s : ℝ) : rotK s ∈ rowIsometrySubgroup₀ ℝ := by
  have hr : Real.sqrt (1 + s ^ 2) ^ 2 = 1 + s ^ 2 := Real.sq_sqrt (by positivity)
  have hr0 : Real.sqrt (1 + s ^ 2) ≠ 0 := (Real.sqrt_pos.mpr (by positivity)).ne'
  have hdet : (rotK s : Matrix (Fin 2) (Fin 2) ℝ).det = 1 := by
    rw [rotK_coe, Matrix.det_fin_two_of]
    field_simp
    nlinarith [hr]
  rw [mem_rowIsometrySubgroup₀_iff]
  refine ⟨hdet, ?_, ?_⟩
  · rw [hdet, norm_one]
  · intro x y
    simp only [rotK_coe, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one, Real.norm_eq_abs, sq_abs]
    field_simp
    nlinarith [hr]

private theorem firstRowℂ_rotK (s : ℝ) :
    firstRowℂ (rotK s) = ⟨(Real.sqrt (1 + s ^ 2))⁻¹, -(s * (Real.sqrt (1 + s ^ 2))⁻¹)⟩ :=
  rfl

private theorem archWeightCharℝ_apply_coe (n : ℤ) (k : rowIsometrySubgroup₀ ℝ) :
    (archWeightCharℝ n k : ℂ) = firstRowℂ (k : GL (Fin 2) ℝ) ^ n := by
  simp only [archWeightCharℝ, MonoidHom.coe_comp, Function.comp_apply, zpowGroupHom_apply,
    Units.val_zpow_eq_zpow_val]
  rfl

private def rotKℂ (s : ℝ) : ℂ :=
  (((Real.sqrt (1 + s ^ 2))⁻¹ : ℝ) : ℂ) + ((-(s * (Real.sqrt (1 + s ^ 2))⁻¹) : ℝ) : ℂ) * Complex.I

private theorem firstRowℂ_rotK_eq (s : ℝ) : firstRowℂ (rotK s) = rotKℂ s := by
  rw [firstRowℂ_rotK, rotKℂ, Complex.mk_eq_add_mul_I]

private theorem rotKℂ_zero : rotKℂ 0 = 1 := by
  simp [rotKℂ]

private theorem hasDerivAt_one_add_sq_zero : HasDerivAt (fun s : ℝ => 1 + s ^ 2) 0 0 := by
  simpa using ((hasDerivAt_pow 2 (0 : ℝ)).const_add 1)

private theorem hasDerivAt_inv_sqrt_zero : HasDerivAt (fun s : ℝ => (Real.sqrt (1 + s ^ 2))⁻¹) 0 0 := by
  have h1 : HasDerivAt (fun s : ℝ => Real.sqrt (1 + s ^ 2)) (1 / (2 * Real.sqrt (1 + (0 : ℝ) ^ 2)) * 0) 0 :=
    (Real.hasDerivAt_sqrt (x := 1 + (0 : ℝ) ^ 2) (by norm_num)).comp (0 : ℝ) hasDerivAt_one_add_sq_zero
  have h2 := h1.inv (by simp)
  simpa [Pi.inv_def] using h2

private theorem hasDerivAt_rotKℂ_zero : HasDerivAt rotKℂ (-Complex.I) 0 := by
  have hre := hasDerivAt_inv_sqrt_zero.ofReal_comp
  have him := (((hasDerivAt_id (0 : ℝ)).fun_mul hasDerivAt_inv_sqrt_zero).fun_neg).ofReal_comp
  have h := hre.fun_add (him.mul_const Complex.I)
  convert h using 1 <;> first | (with_reducible_and_instances rfl) | rfl | simp

private theorem hasDerivAt_rotKℂ_zpow_zero (k₀ : ℤ) :
    HasDerivAt (fun s : ℝ => rotKℂ s ^ k₀) (-(k₀ : ℂ) * Complex.I) 0 := by
  have hz : HasDerivAt (fun z : ℂ => z ^ k₀) ((k₀ : ℂ) * (1 : ℂ) ^ (k₀ - 1)) (1 : ℂ) :=
    hasDerivAt_zpow k₀ (1 : ℂ) (Or.inl one_ne_zero)
  have h := hz.comp_of_eq (0 : ℝ) hasDerivAt_rotKℂ_zero rotKℂ_zero.symm
  convert h using 1 <;> first | (with_reducible_and_instances rfl) | rfl | skip
  rw [_root_.one_zpow]
  ring

omit [NumberField K] in

private theorem symm_mem_rowIsometrySubgroup₀ {w : InfinitePlace K} (hw : w.IsReal) (k : rowIsometrySubgroup₀ ℝ) :
    glEquivOfRingEquiv (ringEquivRealOfIsReal hw).symm (k : GL (Fin 2) ℝ) ∈ rowIsometrySubgroup₀ w.Completion :=
  map_mem_rowIsometrySubgroup₀_of_normPreserving _
    (fun x => by
      rw [← norm_ringEquivRealOfIsReal hw ((ringEquivRealOfIsReal hw).symm x), RingEquiv.apply_symm_apply])
    _ k.2

omit [NumberField K] in

private theorem archWeightCharAt_symm {w : InfinitePlace K} (hw : w.IsReal) (n : ℤ) (k : rowIsometrySubgroup₀ ℝ) :
    archWeightCharAt hw n ⟨_, symm_mem_rowIsometrySubgroup₀ hw k⟩ = archWeightCharℝ n k := by
  have hmap : rowIsometrySubgroup₀Map (ringEquivRealOfIsReal hw) (norm_ringEquivRealOfIsReal hw)
      ⟨_, symm_mem_rowIsometrySubgroup₀ hw k⟩ = k := by
    apply Subtype.ext
    apply Units.ext
    ext i j
    simp [rowIsometrySubgroup₀Map, glEquivOfRingEquiv_apply_entry]
  simp only [archWeightCharAt, archWeightOneAt, archWeightCharℝ, MonoidHom.comp_apply, hmap]

private theorem archRealGLAt_eq_adelicArchGLInclAt {w : InfinitePlace K} (hw : w.IsReal) (m : GL (Fin 2) ℝ) :
    archRealGLAt hw m = adelicArchGLInclAt K w (glEquivOfRingEquiv (ringEquivRealOfIsReal hw).symm m) := rfl

private theorem hasDerivAt_s_mul_inv_sqrt_zero : HasDerivAt (fun s : ℝ => s * (Real.sqrt (1 + s ^ 2))⁻¹) 1 0 := by
  have h := (hasDerivAt_id (0 : ℝ)).fun_mul hasDerivAt_inv_sqrt_zero
  simpa using h

private theorem archDirMatrix_Fm_sub_E :
    archDirMatrix .Fm - archDirMatrix .E = !![(0 : ℝ), -1; 1, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [archDirMatrix]

private theorem hasDerivAt_of_symm_rotK_zero :
    HasDerivAt (fun s : ℝ => (Matrix.of.symm (rotK s : Matrix (Fin 2) (Fin 2) ℝ) : Fin 2 → Fin 2 → ℝ))
      (Matrix.of.symm (archDirMatrix .Fm - archDirMatrix .E)) 0 := by
  rw [archDirMatrix_Fm_sub_E, hasDerivAt_pi]
  intro i
  rw [hasDerivAt_pi]
  intro j
  fin_cases i <;> fin_cases j <;>
    simp only [rotK_coe, Matrix.of_symm_apply, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one, Fin.zero_eta, Fin.mk_one, Fin.isValue]
  · exact hasDerivAt_inv_sqrt_zero
  · exact hasDerivAt_s_mul_inv_sqrt_zero.neg
  · exact hasDerivAt_s_mul_inv_sqrt_zero
  · exact hasDerivAt_inv_sqrt_zero

private theorem apply_mul_archRealGLAt_of_hasArchCharacterAt₀ {w : InfinitePlace K} (hw : w.IsReal) (n : ℤ)
    {φ : AdelicGL2 (𝓞 K) K → ℂ} (hk : HasArchCharacterAt₀ K w (archWeightCharAt hw n) φ)
    (k : rowIsometrySubgroup₀ ℝ) (x : AdelicGL2 (𝓞 K) K) :
    φ (x * archRealGLAt hw (k : GL (Fin 2) ℝ)) = firstRowℂ (k : GL (Fin 2) ℝ) ^ n * φ x := by
  have h := hk ⟨_, symm_mem_rowIsometrySubgroup₀ hw k⟩ x
  rw [archWeightCharAt_symm hw n k, archWeightCharℝ_apply_coe] at h
  rw [archRealGLAt_eq_adelicArchGLInclAt]
  exact h

private theorem archDerivAt_E_sub_Fm_of_weight {w : InfinitePlace K} {hw : w.IsReal} (n : ℤ)
    {φ : AdelicGL2 (𝓞 K) K → ℂ} (hφ : IsArchSmoothAt hw φ) (hk : HasArchCharacterAt₀ K w (archWeightCharAt hw n) φ)
    (x : AdelicGL2 (𝓞 K) K) :
    archDerivAt hw .E φ x - archDerivAt hw .Fm φ x = Complex.I * n * φ x := by
  have hopen := isOpen_setOf_det_ne_zero
  set ψ : (Fin 2 → Fin 2 → ℝ) → ℂ := fun e => φ (x * archRealLiftAt hw e) with hψ

  have hcurve : (fun s : ℝ => φ (x * archRealGLAt hw (rotK s)))
      = fun s : ℝ => ψ (Matrix.of.symm (rotK s : Matrix (Fin 2) (Fin 2) ℝ)) := by
    funext s
    simp only [hψ, archRealGLAt_eq_archRealLiftAt hw (rotK s)]
  have hchar : (fun s : ℝ => φ (x * archRealGLAt hw (rotK s))) = fun s : ℝ => rotKℂ s ^ n * φ x := by
    funext s
    rw [apply_mul_archRealGLAt_of_hasArchCharacterAt₀ hw n hk ⟨rotK s, rotK_mem s⟩ x]
    simp only [firstRowℂ_rotK_eq]

  have hdiff : HasFDerivAt ψ (fderiv ℝ ψ (Matrix.of.symm 1))
      (Matrix.of.symm (rotK 0 : Matrix (Fin 2) (Fin 2) ℝ)) := by
    have h0 : (rotK 0 : Matrix (Fin 2) (Fin 2) ℝ) = 1 := by
      rw [rotK_coe]
      ext i j
      fin_cases i <;> fin_cases j <;> simp
    rw [h0]
    exact (((hφ x).contDiffAt (hopen.mem_nhds det_of_symm_one)).differentiableAt (by simp)).hasFDerivAt
  have h1 : HasDerivAt (fun s : ℝ => φ (x * archRealGLAt hw (rotK s)))
      (fderiv ℝ ψ (Matrix.of.symm 1) (Matrix.of.symm (archDirMatrix .Fm - archDirMatrix .E))) 0 := by
    rw [hcurve]
    exact hdiff.comp_hasDerivAt (0 : ℝ) hasDerivAt_of_symm_rotK_zero

  have h2 : HasDerivAt (fun s : ℝ => φ (x * archRealGLAt hw (rotK s))) (-(n : ℂ) * Complex.I * φ x) 0 := by
    rw [hchar]
    exact (hasDerivAt_rotKℂ_zpow_zero n).mul_const (φ x)
  have h3 := h1.unique h2
  rw [of_symm_sub, map_sub, ← archDerivAt_eq_fderiv hφ .Fm x, ← archDerivAt_eq_fderiv hφ .E x] at h3
  linear_combination -h3

private theorem archDirMatrix_H_mul_E_sub : archDirMatrix .H * archDirMatrix .E - archDirMatrix .E * archDirMatrix .H
    = (2 : ℝ) • archDirMatrix .E := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [archDirMatrix]
  norm_num

private theorem archDirMatrix_H_mul_Fm_sub :
    archDirMatrix .H * archDirMatrix .Fm - archDirMatrix .Fm * archDirMatrix .H = (-2 : ℝ) • archDirMatrix .Fm := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [archDirMatrix]
  norm_num

private theorem of_symm_smul (c : ℝ) (A : Matrix (Fin 2) (Fin 2) ℝ) :
    (Matrix.of.symm (c • A) : Fin 2 → Fin 2 → ℝ) = c • Matrix.of.symm A := rfl

private theorem archDerivAt_comm_eq {w : InfinitePlace K} {hw : w.IsReal} {φ : AdelicGL2 (𝓞 K) K → ℂ}
    (hφ : IsArchSmoothAt hw φ) (d d' : ArchDir) (x : AdelicGL2 (𝓞 K) K) :
    archDerivAt hw d (archDerivAt hw d' φ) x - archDerivAt hw d' (archDerivAt hw d φ) x
      = fderiv ℝ (fun e : Fin 2 → Fin 2 → ℝ => φ (x * archRealLiftAt hw e)) (Matrix.of.symm 1)
          (Matrix.of.symm (archDirMatrix d * archDirMatrix d' - archDirMatrix d' * archDirMatrix d)) := by
  have hopen := isOpen_setOf_det_ne_zero
  have h2 : ContDiffOn ℝ 2 (fun e : Fin 2 → Fin 2 → ℝ => φ (x * archRealLiftAt hw e)) {e | (Matrix.of e).det ≠ 0} := by
    simpa using contDiffOn_infty.mp (hφ x) 2
  have hsymm := (h2.contDiffAt (hopen.mem_nhds det_of_symm_one)).isSymmSndFDerivAt (by simp)
  rw [archDerivAt_archDerivAt_eq hφ d d' x, archDerivAt_archDerivAt_eq hφ d' d x,
    hsymm (Matrix.of.symm (archDirMatrix d')) (Matrix.of.symm (archDirMatrix d)), add_sub_add_left_eq_sub,
    ← map_sub, ← of_symm_sub]

private theorem archDerivAt_comm_H_E {w : InfinitePlace K} {hw : w.IsReal} {φ : AdelicGL2 (𝓞 K) K → ℂ}
    (hφ : IsArchSmoothAt hw φ) (x : AdelicGL2 (𝓞 K) K) :
    archDerivAt hw .H (archDerivAt hw .E φ) x - archDerivAt hw .E (archDerivAt hw .H φ) x
      = 2 * archDerivAt hw .E φ x := by
  rw [archDerivAt_comm_eq hφ .H .E x, archDirMatrix_H_mul_E_sub, of_symm_smul, map_smul,
    ← archDerivAt_eq_fderiv hφ .E x]
  simp [Complex.real_smul]

private theorem archDerivAt_comm_H_Fm {w : InfinitePlace K} {hw : w.IsReal} {φ : AdelicGL2 (𝓞 K) K → ℂ}
    (hφ : IsArchSmoothAt hw φ) (x : AdelicGL2 (𝓞 K) K) :
    archDerivAt hw .H (archDerivAt hw .Fm φ) x - archDerivAt hw .Fm (archDerivAt hw .H φ) x
      = -2 * archDerivAt hw .Fm φ x := by
  rw [archDerivAt_comm_eq hφ .H .Fm x, archDirMatrix_H_mul_Fm_sub, of_symm_smul, map_smul,
    ← archDerivAt_eq_fderiv hφ .Fm x]
  simp [Complex.real_smul]

private def _root_.Ladder.lowerOp {w : InfinitePlace K} (hw : w.IsReal) (φ : AdelicGL2 (𝓞 K) K → ℂ) : AdelicGL2 (𝓞 K) K → ℂ :=
  archDerivAt hw .H φ - Complex.I • (archDerivAt hw .E φ + archDerivAt hw .Fm φ)

p2m_export "Ladder" "lowerOp"
private def _root_.Ladder.raiseOp {w : InfinitePlace K} (hw : w.IsReal) (φ : AdelicGL2 (𝓞 K) K → ℂ) : AdelicGL2 (𝓞 K) K → ℂ :=
  archDerivAt hw .H φ + Complex.I • (archDerivAt hw .E φ + archDerivAt hw .Fm φ)

p2m_export "Ladder" "raiseOp"
private theorem lowerOp_eq_add {w : InfinitePlace K} (hw : w.IsReal) (φ : AdelicGL2 (𝓞 K) K → ℂ) :
    lowerOp hw φ = archDerivAt hw .H φ + (-Complex.I) • (archDerivAt hw .E φ + archDerivAt hw .Fm φ) := by
  rw [lowerOp, sub_eq_add_neg, neg_smul]

namespace IsArchSmoothAt
private theorem _root_.Ladder.IsArchSmoothAt.lowerOp {w : InfinitePlace K} {hw : w.IsReal} {φ : AdelicGL2 (𝓞 K) K → ℂ}
    (hφ : IsArchSmoothAt hw φ) : IsArchSmoothAt hw (lowerOp hw φ) := by
  rw [lowerOp_eq_add]
  exact (hφ.archDerivAt .H).add (((hφ.archDerivAt .E).add (hφ.archDerivAt .Fm)).smul _)

end IsArchSmoothAt
p2m_export "Ladder" "IsArchSmoothAt.lowerOp"
private theorem archDerivAt_lowerOp_apply {w : InfinitePlace K} {hw : w.IsReal} {φ : AdelicGL2 (𝓞 K) K → ℂ}
    (hφ : IsArchSmoothAt hw φ) (d : ArchDir) (x : AdelicGL2 (𝓞 K) K) :
    archDerivAt hw d (lowerOp hw φ) x
      = archDerivAt hw d (archDerivAt hw .H φ) x
        - Complex.I * (archDerivAt hw d (archDerivAt hw .E φ) x + archDerivAt hw d (archDerivAt hw .Fm φ) x) := by
  rw [lowerOp_eq_add, archDerivAt_add (hφ.archDerivAt .H) (((hφ.archDerivAt .E).add (hφ.archDerivAt .Fm)).smul _) d,
    archDerivAt_smul, archDerivAt_add (hφ.archDerivAt .E) (hφ.archDerivAt .Fm) d]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

private theorem archCasimirAt_eq_raiseOp_lowerOp {w : InfinitePlace K} {hw : w.IsReal} (n : ℤ)
    {φ : AdelicGL2 (𝓞 K) K → ℂ} (hφ : IsArchSmoothAt hw φ)
    (hk : HasArchCharacterAt₀ K w (archWeightCharAt hw n) φ) :
    archCasimirAt hw φ
      = (-(1 / 4 : ℂ)) • raiseOp hw (lowerOp hw φ) + ((1 - ((n : ℂ) - 1) ^ 2) / 4) • φ := by

  have hfun : archDerivAt hw .E φ = archDerivAt hw .Fm φ + (Complex.I * n) • φ := by
    funext y
    have h := archDerivAt_E_sub_Fm_of_weight n hφ hk y
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    linear_combination h
  have hder : ∀ d : ArchDir, ∀ y : AdelicGL2 (𝓞 K) K,
      archDerivAt hw d (archDerivAt hw .E φ) y
        = archDerivAt hw d (archDerivAt hw .Fm φ) y + Complex.I * n * archDerivAt hw d φ y := by
    intro d y
    conv_lhs => rw [hfun]
    rw [archDerivAt_add (hφ.archDerivAt .Fm) (hφ.smul _) d, archDerivAt_smul]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  funext x
  have hHE := archDerivAt_comm_H_E hφ x
  have hHF := archDerivAt_comm_H_Fm hφ x
  have hEF := archDerivAt_comm_E_Fm hφ x
  have hwE := hder .E x
  have hwF := hder .Fm x
  have hw0 := archDerivAt_E_sub_Fm_of_weight n hφ hk x
  simp only [archCasimirAt, raiseOp, Pi.add_apply, Pi.sub_apply, Pi.neg_apply, Pi.smul_apply, smul_eq_mul,
    archDerivAt_lowerOp_apply hφ]
  have hI : Complex.I ^ 2 = -1 := Complex.I_sq
  linear_combination (-Complex.I / 4) * hHE + (-Complex.I / 4) * hHF + (-1 / 2 : ℂ) * hEF + (1 / 4 : ℂ) * hwE
    + (-1 / 4 : ℂ) * hwF + (Complex.I * ((n : ℂ) - 2) / 4) * hw0
    + ((-(archDerivAt hw .E (archDerivAt hw .E φ) x) - archDerivAt hw .E (archDerivAt hw .Fm φ) x
        - archDerivAt hw .Fm (archDerivAt hw .E φ) x - archDerivAt hw .Fm (archDerivAt hw .Fm φ) x
        + (n : ℂ) ^ 2 * φ x - 2 * (n : ℂ) * φ x) / 4) * hI

namespace IsArchSmoothAt
private theorem _root_.Ladder.IsArchSmoothAt.raiseOp {w : InfinitePlace K} {hw : w.IsReal} {φ : AdelicGL2 (𝓞 K) K → ℂ}
    (hφ : IsArchSmoothAt hw φ) : IsArchSmoothAt hw (raiseOp hw φ) :=
  (hφ.archDerivAt .H).add (((hφ.archDerivAt .E).add (hφ.archDerivAt .Fm)).smul _)

end IsArchSmoothAt
p2m_export "Ladder" "IsArchSmoothAt.raiseOp"
private theorem archDerivAt_raiseOp_apply {w : InfinitePlace K} {hw : w.IsReal} {φ : AdelicGL2 (𝓞 K) K → ℂ}
    (hφ : IsArchSmoothAt hw φ) (d : ArchDir) (x : AdelicGL2 (𝓞 K) K) :
    archDerivAt hw d (raiseOp hw φ) x
      = archDerivAt hw d (archDerivAt hw .H φ) x
        + Complex.I * (archDerivAt hw d (archDerivAt hw .E φ) x + archDerivAt hw d (archDerivAt hw .Fm φ) x) := by
  rw [raiseOp, archDerivAt_add (hφ.archDerivAt .H) (((hφ.archDerivAt .E).add (hφ.archDerivAt .Fm)).smul _) d,
    archDerivAt_smul, archDerivAt_add (hφ.archDerivAt .E) (hφ.archDerivAt .Fm) d]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]

private theorem archCasimirAt_eq_lowerOp_raiseOp {w : InfinitePlace K} {hw : w.IsReal} (n : ℤ)
    {φ : AdelicGL2 (𝓞 K) K → ℂ} (hφ : IsArchSmoothAt hw φ)
    (hk : HasArchCharacterAt₀ K w (archWeightCharAt hw n) φ) :
    archCasimirAt hw φ
      = (-(1 / 4 : ℂ)) • lowerOp hw (raiseOp hw φ) + ((1 - ((n : ℂ) + 1) ^ 2) / 4) • φ := by
  have hfun : archDerivAt hw .E φ = archDerivAt hw .Fm φ + (Complex.I * n) • φ := by
    funext y
    have h := archDerivAt_E_sub_Fm_of_weight n hφ hk y
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    linear_combination h
  have hder : ∀ d : ArchDir, ∀ y : AdelicGL2 (𝓞 K) K,
      archDerivAt hw d (archDerivAt hw .E φ) y
        = archDerivAt hw d (archDerivAt hw .Fm φ) y + Complex.I * n * archDerivAt hw d φ y := by
    intro d y
    conv_lhs => rw [hfun]
    rw [archDerivAt_add (hφ.archDerivAt .Fm) (hφ.smul _) d, archDerivAt_smul]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  funext x
  have hHE := archDerivAt_comm_H_E hφ x
  have hHF := archDerivAt_comm_H_Fm hφ x
  have hEF := archDerivAt_comm_E_Fm hφ x
  have hwE := hder .E x
  have hwF := hder .Fm x
  have hw0 := archDerivAt_E_sub_Fm_of_weight n hφ hk x
  simp only [archCasimirAt, lowerOp, Pi.add_apply, Pi.sub_apply, Pi.neg_apply, Pi.smul_apply, smul_eq_mul,
    archDerivAt_raiseOp_apply hφ]
  have hI : Complex.I ^ 2 = -1 := Complex.I_sq
  linear_combination (Complex.I / 4) * hHE + (Complex.I / 4) * hHF + (-1 / 2 : ℂ) * hEF + (1 / 4 : ℂ) * hwE
    + (-1 / 4 : ℂ) * hwF + (Complex.I * ((n : ℂ) + 2) / 4) * hw0
    + ((-(archDerivAt hw .E (archDerivAt hw .E φ) x) - archDerivAt hw .E (archDerivAt hw .Fm φ) x
        - archDerivAt hw .Fm (archDerivAt hw .E φ) x - archDerivAt hw .Fm (archDerivAt hw .Fm φ) x
        + (n : ℂ) ^ 2 * φ x + 2 * (n : ℂ) * φ x) / 4) * hI

private theorem archCasimirAt_eq_of_lowerOp_eq_zero {w : InfinitePlace K} {hw : w.IsReal} (n : ℤ)
    {φ : AdelicGL2 (𝓞 K) K → ℂ} (hφ : IsArchSmoothAt hw φ)
    (hk : HasArchCharacterAt₀ K w (archWeightCharAt hw n) φ) (h0 : lowerOp hw φ = 0) :
    archCasimirAt hw φ = ((1 - ((n : ℂ) - 1) ^ 2) / 4) • φ := by
  rw [archCasimirAt_eq_raiseOp_lowerOp n hφ hk, h0]
  have hz : raiseOp hw (0 : AdelicGL2 (𝓞 K) K → ℂ) = 0 := by
    funext y
    simp only [raiseOp, Pi.add_apply, Pi.smul_apply, Pi.zero_apply, smul_eq_mul]
    have hd : ∀ d : ArchDir, archDerivAt hw d (0 : AdelicGL2 (𝓞 K) K → ℂ) y = 0 := fun d => by
      have h := archDerivAt_const hw d (0 : ℂ)
      exact congrFun h y
    rw [hd .H, hd .E, hd .Fm]
    ring
  rw [hz, smul_zero, zero_add]

private theorem ladder_const_eq_laplaceEigenvalue_discrete (u : ℂ) (m : ℕ) (hm : 1 ≤ m) :
    (1 - (((m : ℤ) + 1 : ℤ) - 1 : ℂ) ^ 2) / 4 = LanglandsTunnell.RealArchParam.laplaceEigenvalue
      (LanglandsTunnell.RealArchParam.discrete u m hm) := by
  rw [LanglandsTunnell.RealArchParam.laplaceEigenvalue_discrete]
  push_cast
  ring

private theorem ladder_const_one_eq_laplaceEigenvalue_principal (u : ℂ) (a b : ZMod 2) :
    (1 - (((1 : ℤ) : ℂ) - 1) ^ 2) / 4 = LanglandsTunnell.RealArchParam.laplaceEigenvalue
      (LanglandsTunnell.RealArchParam.principal u a u b) := by
  rw [LanglandsTunnell.RealArchParam.laplaceEigenvalue_principal]
  push_cast
  ring

end Ladder

namespace CentralData

open IsDedekindDomain NumberField MeasureTheory Matrix
open NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
p2m_open "AutomorphicForm~continuous_unipotentGL2~isIsotypicCuspFormAt_of_mem_isotypicCuspSubmodule AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering"
open LanglandsTunnell LanglandsTunnell.Converse NumberField.TateGlobal

section

variable (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 ℚ) ℚ)) (Ψ : HeckeEigensystem ℚ ℂ)

private abbrev winPins : CarrierPins ℚ :=
  productionPinsOf ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂)
    (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ)

variable {c u d₁ d₂ T Ψ}

private def ideleChar (R : SmoothCuspRealizationAt ℚ (winPins c u d₁ d₂ T) Ψ) : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ :=
  R.centralChar.comp Subgroup.topEquiv.symm.toMonoidHom

private theorem isLsXiFunction_toFun (R : SmoothCuspRealizationAt ℚ (winPins c u d₁ d₂ T) Ψ) :
    IsLsXiFunction (𝓞 ℚ) ℚ ⊤ R.centralChar R.toFun := by
  have hauto : IsAutomorphicFnAt ℚ (winPins c u d₁ d₂ T) R.centralChar R.toFun := R.smoothCusp.1.1
  exact ((@lsXiMemberAt_iff (𝓞 ℚ) ℚ _ _ _ _ _ (glBorel (Fin 2) (𝓞 ℚ) ℚ) (adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ) ⊤ R.centralChar
    (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂) R.toFun).mp hauto).1

private theorem toFun_centralScalar_mul (R : SmoothCuspRealizationAt ℚ (winPins c u d₁ d₂ T) Ψ)
    (z : (AdeleRing (𝓞 ℚ) ℚ)ˣ) (g : AdelicGL2 (𝓞 ℚ) ℚ) :
    R.toFun (centralScalar (𝓞 ℚ) ℚ z * g) = ((ideleChar R z : ℂˣ) : ℂ) * R.toFun g :=
  (isLsXiFunction_toFun R).central_transform ⟨z, Subgroup.mem_top z⟩ g

private theorem continuous_centralScalar : Continuous (centralScalar (𝓞 ℚ) ℚ) := by
  refine Units.continuous_iff.mpr ⟨?_, ?_⟩
  · have h := (continuous_pi fun _ : Fin 2 => (Units.continuous_val (M := AdeleRing (𝓞 ℚ) ℚ))).matrix_diagonal
    convert h using 1 <;> first | (with_reducible_and_instances rfl) | rfl | (funext x; rfl) | skip
  · have h := (continuous_pi fun _ : Fin 2 => (Units.continuous_coe_inv (M := AdeleRing (𝓞 ℚ) ℚ))).matrix_diagonal
    convert h using 1 <;> first | (with_reducible_and_instances rfl) | rfl | (funext x; rfl) | skip

private theorem continuous_ideleChar (R : SmoothCuspRealizationAt ℚ (winPins c u d₁ d₂ T) Ψ)
    (hR : Continuous R.toFun) : Continuous (ideleChar R) := by
  obtain ⟨g₀, hg₀⟩ := R.exists_ne_zero
  have key : ∀ z : (AdeleRing (𝓞 ℚ) ℚ)ˣ,
      ((ideleChar R z : ℂˣ) : ℂ) = R.toFun (centralScalar (𝓞 ℚ) ℚ z * g₀) / R.toFun g₀ := fun z => by
    rw [toFun_centralScalar_mul, mul_div_cancel_right₀ _ hg₀]
  have hval : Continuous fun z : (AdeleRing (𝓞 ℚ) ℚ)ˣ => ((ideleChar R z : ℂˣ) : ℂ) := by
    simp only [key]
    exact (hR.comp (continuous_centralScalar.mul continuous_const)).div_const _
  refine Units.continuous_iff.mpr ⟨hval, ?_⟩
  have hinv : (fun z : (AdeleRing (𝓞 ℚ) ℚ)ˣ => (((ideleChar R z)⁻¹ : ℂˣ) : ℂ))
      = fun z => ((ideleChar R z⁻¹ : ℂˣ) : ℂ) := by
    funext z
    rw [map_inv]
  rw [hinv]
  exact hval.comp continuous_inv

private theorem globalPoints_scalar (q : ℚˣ) :
    globalPoints (𝓞 ℚ) ℚ (Matrix.GeneralLinearGroup.scalar (Fin 2) q)
      = centralScalar (𝓞 ℚ) ℚ (Units.map (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ)) q) := by
  apply Units.ext
  ext i j
  simp only [globalPoints, centralScalar, Matrix.GeneralLinearGroup.map_apply]
  simp [Matrix.GeneralLinearGroup.scalar, Units.coe_map, MonoidHom.coe_coe, Matrix.scalar_apply, Matrix.diagonal_apply,
    apply_ite (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ)), map_zero, Matrix.algebraMap_matrix_apply]

private theorem isIdeleClassChar_ideleChar (R : SmoothCuspRealizationAt ℚ (winPins c u d₁ d₂ T) Ψ) :
    IsIdeleClassChar (𝓞 ℚ) ℚ (ideleChar R) := by
  intro q
  obtain ⟨g₀, hg₀⟩ := R.exists_ne_zero
  have h1 := toFun_centralScalar_mul R (Units.map (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ)) q) g₀
  rw [← globalPoints_scalar, (isLsXiFunction_toFun R).left_invariant] at h1
  exact Units.val_eq_one.mp ((mul_eq_right₀ hg₀).mp h1.symm)

private theorem exists_isArchCompAt (R : SmoothCuspRealizationAt ℚ (winPins c u d₁ d₂ T) Ψ)
    (hR : Continuous R.toFun) (w : InfinitePlace ℚ) (hw : w.IsReal) :
    ∃ (u₀ : ℂ) (a : ZMod 2),
      IsArchCompAt ℚ (R.centralChar.comp Subgroup.topEquiv.symm.toMonoidHom) w u₀ ((a.val : ℕ) : ℤ) :=
  LanglandsTunnell.Converse.exists_isArchCompAt_of_isReal ℚ (ideleChar R) (continuous_ideleChar R hR) w hw

private theorem exists_norm_ideleChar_eq (R : SmoothCuspRealizationAt ℚ (winPins c u d₁ d₂ T) Ψ)
    (hR : Continuous R.toFun) :
    ∃ σ : ℝ, ∀ x : (AdeleRing (𝓞 ℚ) ℚ)ˣ, ‖((ideleChar R x : ℂˣ) : ℂ)‖ = ideleNorm ℚ x ^ σ :=
  RatIdele.exists_norm_apply_eq_ideleNorm_rpow (ideleChar R) (isIdeleClassChar_ideleChar R) (continuous_ideleChar R hR)

end

end CentralData

namespace CentralParity

p2m_open "AutomorphicForm~continuous_unipotentGL2~isIsotypicCuspFormAt_of_mem_isotypicCuspSubmodule AutomorphicForm.SiegelCovering Matrix"
open NumberField IsDedekindDomain NumberField.InfinitePlace NumberField.InfinitePlace.Completion
open NumberField.AdelicLevel NumberField.AdelicVolume
open NumberField.TateGlobal LanglandsTunnell.Converse

section

variable {K : Type} [Field K] [NumberField K]

private theorem archWeightCharℝ_apply_coe (n : ℤ) (k : rowIsometrySubgroup₀ ℝ) :
    (archWeightCharℝ n k : ℂ) = firstRowℂ (k : GL (Fin 2) ℝ) ^ n := by
  simp only [archWeightCharℝ, MonoidHom.coe_comp, Function.comp_apply, zpowGroupHom_apply,
    Units.val_zpow_eq_zpow_val]
  rfl

omit [NumberField K] in

private theorem symm_mem_rowIsometrySubgroup₀ {w : InfinitePlace K} (hw : w.IsReal) (k : rowIsometrySubgroup₀ ℝ) :
    glEquivOfRingEquiv (ringEquivRealOfIsReal hw).symm (k : GL (Fin 2) ℝ) ∈ rowIsometrySubgroup₀ w.Completion :=
  map_mem_rowIsometrySubgroup₀_of_normPreserving _
    (fun x => by
      rw [← norm_ringEquivRealOfIsReal hw ((ringEquivRealOfIsReal hw).symm x), RingEquiv.apply_symm_apply])
    _ k.2

omit [NumberField K] in

private theorem archWeightCharAt_symm {w : InfinitePlace K} (hw : w.IsReal) (n : ℤ) (k : rowIsometrySubgroup₀ ℝ) :
    archWeightCharAt hw n ⟨_, symm_mem_rowIsometrySubgroup₀ hw k⟩ = archWeightCharℝ n k := by
  have hmap : rowIsometrySubgroup₀Map (ringEquivRealOfIsReal hw) (norm_ringEquivRealOfIsReal hw)
      ⟨_, symm_mem_rowIsometrySubgroup₀ hw k⟩ = k := by
    apply Subtype.ext
    apply Units.ext
    ext i j
    simp [rowIsometrySubgroup₀Map, glEquivOfRingEquiv_apply_entry]
  simp only [archWeightCharAt, archWeightOneAt, archWeightCharℝ, MonoidHom.comp_apply, hmap]

private theorem archRealGLAt_eq_adelicArchGLInclAt {w : InfinitePlace K} (hw : w.IsReal) (m : GL (Fin 2) ℝ) :
    archRealGLAt hw m = adelicArchGLInclAt K w (glEquivOfRingEquiv (ringEquivRealOfIsReal hw).symm m) := rfl

private theorem apply_mul_archRealGLAt_of_hasArchCharacterAt₀ {w : InfinitePlace K} (hw : w.IsReal) (n : ℤ)
    {φ : AdelicGL2 (𝓞 K) K → ℂ} (hk : HasArchCharacterAt₀ K w (archWeightCharAt hw n) φ)
    (k : rowIsometrySubgroup₀ ℝ) (x : AdelicGL2 (𝓞 K) K) :
    φ (x * archRealGLAt hw (k : GL (Fin 2) ℝ)) = firstRowℂ (k : GL (Fin 2) ℝ) ^ n * φ x := by
  have h := hk ⟨_, symm_mem_rowIsometrySubgroup₀ hw k⟩ x
  rw [archWeightCharAt_symm hw n k, archWeightCharℝ_apply_coe] at h
  rw [archRealGLAt_eq_adelicArchGLInclAt]
  exact h

end

private theorem negOne_mem : (-1 : GL (Fin 2) ℝ) ∈ rowIsometrySubgroup₀ ℝ := by
  have hdet : ((-1 : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ).det = 1 := by
    rw [Units.val_neg, Units.val_one, Matrix.det_neg, Matrix.det_one, Fintype.card_fin]
    norm_num
  rw [mem_rowIsometrySubgroup₀_iff]
  refine ⟨hdet, ?_, ?_⟩
  · rw [hdet]
    simp
  · intro x y
    simp

private theorem firstRowℂ_negOne : firstRowℂ (-1 : GL (Fin 2) ℝ) = -1 := by
  apply Complex.ext <;> simp [firstRowℂ]

private theorem apply_mul_archRealGLAt_negOne {w : InfinitePlace ℚ} (hw : w.IsReal) (k₀ : ℤ)
    {φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ} (hk : HasArchCharacterAt₀ ℚ w (archWeightCharAt hw k₀) φ) (g : AdelicGL2 (𝓞 ℚ) ℚ) :
    φ (g * archRealGLAt hw (-1)) = (-1 : ℂ) ^ k₀ * φ g := by
  have h := apply_mul_archRealGLAt_of_hasArchCharacterAt₀ hw k₀ hk ⟨-1, negOne_mem⟩ g
  change φ (g * archRealGLAt hw (-1)) = firstRowℂ (-1) ^ k₀ * φ g at h
  rw [h, firstRowℂ_negOne]

local notation "𝔸" => AdeleRing (𝓞 ℚ) ℚ
local notation "𝔸f" => FiniteAdeleRing (𝓞 ℚ) ℚ
local notation "G𝔸" => AdelicGL2 (𝓞 ℚ) ℚ

private theorem glArch_centralScalar_archCentralUnit_negOne {w : InfinitePlace ℚ} (hw : w.IsReal) :
    glArch (𝓞 ℚ) ℚ (centralScalar (𝓞 ℚ) ℚ (archCentralUnit ℚ w (-1)))
      = archGLIncl ℚ w (glEquivOfRingEquiv (ringEquivRealOfIsReal hw).symm (-1)) := by
  apply Units.ext
  ext i j
  funext w'
  obtain rfl : w' = w := Subsingleton.elim w' w
  have hL := archComponent_centralScalar_archCentralUnit_apply w' (-1) i j
  rw [archComponent_apply] at hL
  have hR : ((archGLIncl ℚ w' (glEquivOfRingEquiv (ringEquivRealOfIsReal hw).symm (-1)) :
        GL (Fin 2) (InfiniteAdeleRing ℚ)) : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing ℚ)) i j w'
      = ((glEquivOfRingEquiv (ringEquivRealOfIsReal hw).symm (-1) : GL (Fin 2) w'.Completion) :
          Matrix (Fin 2) (Fin 2) w'.Completion) i j :=
    archMatrixUpdate_apply_self ℚ w' _ i j
  rw [hL, hR, glEquivOfRingEquiv_apply_entry]
  by_cases h : i = j
  · subst h
    simp
  · simp [h, Matrix.one_apply_ne h]

private theorem centralScalar_archCentralUnit_negOne {w : InfinitePlace ℚ} (hw : w.IsReal) :
    centralScalar (𝓞 ℚ) ℚ (archCentralUnit ℚ w (-1)) = archRealGLAt hw (-1) := by
  refine eq_of_glArch_eq_of_glFin_eq ?_ ?_
  · rw [glArch_centralScalar_archCentralUnit_negOne hw, archRealGLAt_eq_adelicArchGLInclAt]
    exact (glArch_adelicArchGLIncl ℚ _).symm
  · rw [glFin_centralScalar_archCentralUnit, archRealGLAt_eq_adelicArchGLInclAt]
    exact (glFin_adelicArchGLIncl ℚ _).symm

private theorem centralChar_negOne_of_isArchCompAt (ξ : (⊤ : Subgroup (AdeleRing (𝓞 ℚ) ℚ)ˣ) →* ℂˣ)
    (w : InfinitePlace ℚ) (u₀ : ℂ) (a : ℤ)
    (hcomp : IsArchCompAt ℚ (ξ.comp Subgroup.topEquiv.symm.toMonoidHom) w u₀ a) :
    ((ξ ⟨archCentralUnit ℚ w (-1), Subgroup.mem_top _⟩ : ℂˣ) : ℂ) = (-1 : ℂ) ^ a := by
  have h := hcomp (-1)
  simp only [Units.val_neg, Units.val_one, norm_neg, norm_one, Complex.ofReal_one, Complex.one_cpow, map_neg,
    map_one, div_one, one_mul] at h
  exact h

private theorem centralChar_negOne_of_weight (ξ : (⊤ : Subgroup (AdeleRing (𝓞 ℚ) ℚ)ˣ) →* ℂˣ) {φ : G𝔸 → ℂ}
    (hξ : IsLsXiFunction (𝓞 ℚ) ℚ ⊤ ξ φ) {w : InfinitePlace ℚ} (hw : w.IsReal) (k₀ : ℤ)
    (hk : HasArchCharacterAt₀ ℚ w (archWeightCharAt hw k₀) φ) {g₀ : G𝔸} (h0 : φ g₀ ≠ 0) :
    ((ξ ⟨archCentralUnit ℚ w (-1), Subgroup.mem_top _⟩ : ℂˣ) : ℂ) = (-1 : ℂ) ^ k₀ := by
  have hcen : φ (centralScalar (𝓞 ℚ) ℚ (archCentralUnit ℚ w (-1)) * g₀)
      = ((ξ ⟨archCentralUnit ℚ w (-1), Subgroup.mem_top _⟩ : ℂˣ) : ℂ) * φ g₀ :=
    hξ.central_transform ⟨archCentralUnit ℚ w (-1), Subgroup.mem_top _⟩ g₀
  rw [← mul_centralScalar_comm, centralScalar_archCentralUnit_negOne hw, apply_mul_archRealGLAt_negOne hw k₀ hk]
    at hcen
  exact (mul_right_cancel₀ h0 hcen).symm

private theorem two_eq_zero_zmod : (2 : ZMod 2) = 0 := by decide

private theorem zmod_two_cases : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide

private theorem val_zero_zmod : (0 : ZMod 2).val = 0 := rfl

private theorem val_one_zmod : (1 : ZMod 2).val = 1 := rfl

private theorem centralSign_eq_weight (ξ : (⊤ : Subgroup (AdeleRing (𝓞 ℚ) ℚ)ˣ) →* ℂˣ) {φ : G𝔸 → ℂ}
    (hξ : IsLsXiFunction (𝓞 ℚ) ℚ ⊤ ξ φ) {w : InfinitePlace ℚ} (hw : w.IsReal) (k₀ : ℤ)
    (hk : HasArchCharacterAt₀ ℚ w (archWeightCharAt hw k₀) φ) {g₀ : G𝔸} (h0 : φ g₀ ≠ 0) (u₀ : ℂ) (a : ZMod 2)
    (hcomp : IsArchCompAt ℚ (ξ.comp Subgroup.topEquiv.symm.toMonoidHom) w u₀ ((a.val : ℕ) : ℤ)) :
    ((k₀ : ℤ) : ZMod 2) = a := by
  have hpow : (-1 : ℂ) ^ ((a.val : ℕ) : ℤ) = (-1 : ℂ) ^ k₀ := by
    rw [← centralChar_negOne_of_isArchCompAt ξ w u₀ _ hcomp, centralChar_negOne_of_weight ξ hξ hw k₀ hk h0]
  have ha := zmod_two_cases a
  rcases Int.even_or_odd k₀ with hk₀ | hk₀
  · rw [hk₀.neg_one_zpow] at hpow
    rcases ha with rfl | rfl
    · obtain ⟨m, rfl⟩ := hk₀
      push_cast
      rw [← two_mul, two_eq_zero_zmod, zero_mul]
    · rw [val_one_zmod] at hpow
      exact absurd hpow (by norm_num)
  · rw [hk₀.neg_one_zpow] at hpow
    rcases ha with rfl | rfl
    · rw [val_zero_zmod] at hpow
      exact absurd hpow (by norm_num)
    · obtain ⟨m, rfl⟩ := hk₀
      push_cast
      rw [two_eq_zero_zmod, zero_mul, zero_add]

end CentralParity

namespace SlabGeometry

open IsDedekindDomain NumberField MeasureTheory
open NumberField.AdelicHaar NumberField.TateGlobal
p2m_open "AutomorphicForm~continuous_unipotentGL2~isIsotypicCuspFormAt_of_mem_isotypicCuspSubmodule AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering"
open scoped ENNReal Pointwise

variable (F : Type) [Field F] [NumberField F]

private def slab (α β : ℝ) : Set (AdelicGL2 (𝓞 F) F) :=
  {g | ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}

private theorem measurableSet_slab (α β : ℝ) :
    letI : MeasurableSpace (AdelicGL2 (𝓞 F) F) := glBorel (Fin 2) (𝓞 F) F
    MeasurableSet (slab F α β) :=
  NumberField.TateGlobal.measurableSet_setOf_ideleNorm_det_mem_Icc F α β

private theorem globalPoints_mul_mem_slab_iff (α β : ℝ) (γ : Matrix.GeneralLinearGroup (Fin 2) F)
    (g : AdelicGL2 (𝓞 F) F) : globalPoints (𝓞 F) F γ * g ∈ slab F α β ↔ g ∈ slab F α β := by
  simp only [slab, Set.mem_setOf_eq, map_mul, ideleNorm_mul, AutomorphicForm.ideleNorm_det_globalPoints, one_mul]

private theorem _root_.SlabGeometry.countable_range [Countable F] : Countable (globalPoints (𝓞 F) F).range := by
  haveI : Countable (Matrix (Fin 2) (Fin 2) F) := inferInstanceAs (Countable (Fin 2 → Fin 2 → F))
  haveI : Countable (Matrix.GeneralLinearGroup (Fin 2) F) := Units.val_injective.countable
  exact (Set.countable_range (globalPoints (𝓞 F) F)).to_subtype

p2m_export "SlabGeometry" "countable_range"
private theorem smulInvariant_slab (α β : ℝ) :
    letI : MeasurableSpace (AdelicGL2 (𝓞 F) F) := glBorel (Fin 2) (𝓞 F) F
    SMulInvariantMeasure (globalPoints (𝓞 F) F).range (AdelicGL2 (𝓞 F) F)
      ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict (slab F α β)) := by
  letI : MeasurableSpace (AdelicGL2 (𝓞 F) F) := glBorel (Fin 2) (𝓞 F) F
  haveI : BorelSpace (AdelicGL2 (𝓞 F) F) := borelSpace_glBorel (Fin 2) (𝓞 F) F
  haveI : (adelicGLHaar (Fin 2) (𝓞 F) F).IsHaarMeasure := isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 F) F
  refine ⟨fun c {s} hs => ?_⟩
  obtain ⟨c', γ, rfl⟩ := c
  have hpre : ((fun x : AdelicGL2 (𝓞 F) F => globalPoints (𝓞 F) F γ * x) ⁻¹' s) ∩ slab F α β
      = (fun x : AdelicGL2 (𝓞 F) F => globalPoints (𝓞 F) F γ * x) ⁻¹' (s ∩ slab F α β) := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_preimage, globalPoints_mul_mem_slab_iff]
  show (adelicGLHaar (Fin 2) (𝓞 F) F).restrict (slab F α β)
      ((fun x : AdelicGL2 (𝓞 F) F => globalPoints (𝓞 F) F γ * x) ⁻¹' s)
    = (adelicGLHaar (Fin 2) (𝓞 F) F).restrict (slab F α β) s
  rw [Measure.restrict_apply (hs.preimage (measurable_const_mul _)), Measure.restrict_apply hs, hpre,
    measure_preimage_mul]

private theorem lintegral_fd_le [Countable F] (α β : ℝ) (Φ₀ S : Set (AdelicGL2 (𝓞 F) F))
    (hFD : letI : MeasurableSpace (AdelicGL2 (𝓞 F) F) := glBorel (Fin 2) (𝓞 F) F
      IsFundamentalDomain (globalPoints (𝓞 F) F).range Φ₀ ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict (slab F α β)))
    (f : AdelicGL2 (𝓞 F) F → ℝ≥0∞)
    (hf : ∀ (γ : Matrix.GeneralLinearGroup (Fin 2) F) (x : AdelicGL2 (𝓞 F) F), f (globalPoints (𝓞 F) F γ * x) = f x)
    (hcover : ∀ x ∈ Φ₀, ∃ γ : Matrix.GeneralLinearGroup (Fin 2) F, globalPoints (𝓞 F) F γ * x ∈ S) :
    letI : MeasurableSpace (AdelicGL2 (𝓞 F) F) := glBorel (Fin 2) (𝓞 F) F
    ∫⁻ x in Φ₀, f x ∂((adelicGLHaar (Fin 2) (𝓞 F) F).restrict (slab F α β))
      ≤ ∫⁻ x in S, f x ∂((adelicGLHaar (Fin 2) (𝓞 F) F).restrict (slab F α β)) := by
  letI : MeasurableSpace (AdelicGL2 (𝓞 F) F) := glBorel (Fin 2) (𝓞 F) F
  haveI : BorelSpace (AdelicGL2 (𝓞 F) F) := borelSpace_glBorel (Fin 2) (𝓞 F) F
  haveI : Countable (globalPoints (𝓞 F) F).range := countable_range F
  haveI := smulInvariant_slab F α β
  set ν := (adelicGLHaar (Fin 2) (𝓞 F) F).restrict (slab F α β) with hν
  have hinv : ∀ (c : (globalPoints (𝓞 F) F).range) (x : AdelicGL2 (𝓞 F) F), f (c⁻¹ • x) = f x := by
    rintro ⟨c, γ, rfl⟩ x
    have h1 : ((⟨globalPoints (𝓞 F) F γ, γ, rfl⟩ : (globalPoints (𝓞 F) F).range)⁻¹ • x)
        = globalPoints (𝓞 F) F γ⁻¹ * x := by
      rw [Subgroup.smul_def]
      simp [map_inv]
    rw [h1, hf]
  have hsub : Φ₀ ⊆ ⋃ c : (globalPoints (𝓞 F) F).range, (c • S ∩ Φ₀) := by
    intro x hx
    obtain ⟨γ, hγ⟩ := hcover x hx
    refine Set.mem_iUnion.mpr ⟨⟨globalPoints (𝓞 F) F γ, γ, rfl⟩⁻¹, ⟨?_, hx⟩⟩
    refine ⟨globalPoints (𝓞 F) F γ * x, hγ, ?_⟩
    show ((⟨globalPoints (𝓞 F) F γ, γ, rfl⟩ : (globalPoints (𝓞 F) F).range)⁻¹ : (globalPoints (𝓞 F) F).range) •
      (globalPoints (𝓞 F) F γ * x) = x
    rw [Subgroup.smul_def]
    simp
  calc ∫⁻ x in Φ₀, f x ∂ν ≤ ∫⁻ x in ⋃ c : (globalPoints (𝓞 F) F).range, (c • S ∩ Φ₀), f x ∂ν :=
        lintegral_mono_set hsub
    _ ≤ ∑' c : (globalPoints (𝓞 F) F).range, ∫⁻ x in c • S ∩ Φ₀, f x ∂ν := lintegral_iUnion_le _ _
    _ = ∑' c : (globalPoints (𝓞 F) F).range, ∫⁻ x in c • S ∩ Φ₀, f (c⁻¹ • x) ∂ν := by
        refine tsum_congr fun c => ?_
        simp only [hinv]
    _ = ∫⁻ x in S, f x ∂ν := (hFD.setLIntegral_eq_tsum' f S).symm

private theorem lintegral_centralScalar_mul_image_lt_top (W : Set (AdelicGL2 (𝓞 F) F))
    (hW : letI : MeasurableSpace (AdelicGL2 (𝓞 F) F) := glBorel (Fin 2) (𝓞 F) F
      MeasurableSet W)
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ) (φ : AdelicGL2 (𝓞 F) F → ℂ)
    (hφ : IsLsXiFunction (𝓞 F) F ⊤ ξ φ)
    (hmass : letI : MeasurableSpace (AdelicGL2 (𝓞 F) F) := glBorel (Fin 2) (𝓞 F) F
      ∫⁻ h in W, ‖φ h‖ₑ ^ 2 ∂(adelicGLHaar (Fin 2) (𝓞 F) F) < ⊤)
    (z : (AdeleRing (𝓞 F) F)ˣ) :
    letI : MeasurableSpace (AdelicGL2 (𝓞 F) F) := glBorel (Fin 2) (𝓞 F) F
    ∫⁻ h in (fun h => centralScalar (𝓞 F) F z * h) '' W, ‖φ h‖ₑ ^ 2 ∂(adelicGLHaar (Fin 2) (𝓞 F) F) < ⊤ := by
  letI : MeasurableSpace (AdelicGL2 (𝓞 F) F) := glBorel (Fin 2) (𝓞 F) F
  haveI : BorelSpace (AdelicGL2 (𝓞 F) F) := borelSpace_glBorel (Fin 2) (𝓞 F) F
  haveI : (adelicGLHaar (Fin 2) (𝓞 F) F).IsHaarMeasure := isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 F) F
  set κ : ℝ≥0∞ := ‖((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)‖ₑ ^ 2 with hκ
  have hκtop : κ ≠ ⊤ := ENNReal.pow_ne_top enorm_ne_top
  have hlaw : ∀ h : AdelicGL2 (𝓞 F) F, ‖φ (centralScalar (𝓞 F) F z * h)‖ₑ ^ 2 = κ * ‖φ h‖ₑ ^ 2 := by
    intro h
    rw [hφ.central_transform ⟨z, Subgroup.mem_top z⟩ h, enorm_mul, mul_pow]
  have himage : (fun h => centralScalar (𝓞 F) F z * h) '' W = (fun h => centralScalar (𝓞 F) F z⁻¹ * h) ⁻¹' W := by
    rw [Set.image_mul_left, map_inv]
  have hWpre : MeasurableSet ((fun h => centralScalar (𝓞 F) F z⁻¹ * h) ⁻¹' W) := hW.preimage (measurable_const_mul _)
  have hind : ∀ h : AdelicGL2 (𝓞 F) F,
      ((fun h => centralScalar (𝓞 F) F z⁻¹ * h) ⁻¹' W).indicator (fun h => ‖φ h‖ₑ ^ 2) h
        = κ * W.indicator (fun h => ‖φ h‖ₑ ^ 2) (centralScalar (𝓞 F) F z⁻¹ * h) := by
    intro h
    by_cases hmem : centralScalar (𝓞 F) F z⁻¹ * h ∈ W
    · have hmem' : h ∈ (fun h => centralScalar (𝓞 F) F z⁻¹ * h) ⁻¹' W := hmem
      simp only [Set.indicator_of_mem hmem, Set.indicator_of_mem hmem']
      have h2 : h = centralScalar (𝓞 F) F z * (centralScalar (𝓞 F) F z⁻¹ * h) := by
        rw [← mul_assoc, ← map_mul, mul_inv_cancel, map_one, one_mul]
      conv_lhs => rw [h2, hlaw]
    · have hmem' : h ∉ (fun h => centralScalar (𝓞 F) F z⁻¹ * h) ⁻¹' W := hmem
      simp only [Set.indicator_of_notMem hmem, Set.indicator_of_notMem hmem', mul_zero]
  rw [himage, ← lintegral_indicator hWpre, lintegral_congr hind, lintegral_const_mul' _ _ hκtop,
    lintegral_mul_left_eq_self (W.indicator fun h => ‖φ h‖ₑ ^ 2) (centralScalar (𝓞 F) F z⁻¹), lintegral_indicator hW]
  exact ENNReal.mul_lt_top hκtop.lt_top hmass

private theorem memLp_fd [Countable F] (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 F) F)) (hd : d₁ < d₂)
    (hcov : CoversModCentre F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂))
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ) (φ : AdelicGL2 (𝓞 F) F → ℂ)
    (hφ : IsLsXiFunction (𝓞 F) F ⊤ ξ φ) (hcont : Continuous φ)
    (hmem : letI : MeasurableSpace (AdelicGL2 (𝓞 F) F) := glBorel (Fin 2) (𝓞 F) F
      MemLp φ 2 ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)))
    (α β : ℝ) (hα : 0 < α) (Φ₀ : Set (AdelicGL2 (𝓞 F) F)) (hΦ₀ : Φ₀ ⊆ slab F α β)
    (hFD : letI : MeasurableSpace (AdelicGL2 (𝓞 F) F) := glBorel (Fin 2) (𝓞 F) F
      IsFundamentalDomain (globalPoints (𝓞 F) F).range Φ₀ ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict (slab F α β))) :
    letI : MeasurableSpace (AdelicGL2 (𝓞 F) F) := glBorel (Fin 2) (𝓞 F) F
    MemLp φ 2 ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict Φ₀) := by
  letI : MeasurableSpace (AdelicGL2 (𝓞 F) F) := glBorel (Fin 2) (𝓞 F) F
  haveI : BorelSpace (AdelicGL2 (𝓞 F) F) := borelSpace_glBorel (Fin 2) (𝓞 F) F
  obtain ⟨N, hN⟩ := AutomorphicForm.exists_finset_central_slab_covering_of_coversModCentre F c u d₁ d₂ T hd hcov α β hα
  set W : Set (AdelicGL2 (𝓞 F) F) := ⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂ with hWdef
  have hWmeas : MeasurableSet W := by
    refine MeasurableSet.biUnion T.countable_toSet fun x _ => ?_
    rw [Set.image_mul_right]
    exact (measurableSet_centreCutSiegelSet c u d₁ d₂).preimage (measurable_mul_const _)
  have hWmass : ∫⁻ h in W, ‖φ h‖ₑ ^ 2 ∂(adelicGLHaar (Fin 2) (𝓞 F) F) < ⊤ := by
    have h2 := (eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top (f := φ)
      (μ := (adelicGLHaar (Fin 2) (𝓞 F) F).restrict W) two_ne_zero ENNReal.ofNat_ne_top).mp hmem.2
    simpa only [ENNReal.toReal_ofNat, ENNReal.rpow_two] using h2

  set S : Set (AdelicGL2 (𝓞 F) F) :=
    ⋃ n : N, (fun h => centralScalar (𝓞 F) F (n : (AdeleRing (𝓞 F) F)ˣ) * h) '' W with hSdef
  have hcover : ∀ x ∈ Φ₀, ∃ γ : Matrix.GeneralLinearGroup (Fin 2) F, globalPoints (𝓞 F) F γ * x ∈ S := by
    intro x hx
    obtain ⟨γ, n, hn, t, ht, s, hs, hsx⟩ := hN x (hΦ₀ hx)
    refine ⟨γ, Set.mem_iUnion.mpr ⟨⟨n, hn⟩, s * t, Set.mem_iUnion₂.mpr ⟨t, ht, ⟨s, hs, rfl⟩⟩, ?_⟩⟩
    have hsx' : s * (centralScalar (𝓞 F) F n * t) = globalPoints (𝓞 F) F γ * x := hsx
    show centralScalar (𝓞 F) F n * (s * t) = globalPoints (𝓞 F) F γ * x
    rw [← hsx', ← mul_assoc, ← mul_centralScalar_comm, mul_assoc]
  have hSmass : ∫⁻ h in S, ‖φ h‖ₑ ^ 2 ∂(adelicGLHaar (Fin 2) (𝓞 F) F) < ⊤ := by
    refine (lintegral_iUnion_le _ _).trans_lt ?_
    rw [tsum_fintype]
    exact ENNReal.sum_lt_top.mpr fun n _ =>
      lintegral_centralScalar_mul_image_lt_top F W hWmeas ξ φ hφ hWmass (n : (AdeleRing (𝓞 F) F)ˣ)
  have hinvf : ∀ (γ : Matrix.GeneralLinearGroup (Fin 2) F) (x : AdelicGL2 (𝓞 F) F),
      ‖φ (globalPoints (𝓞 F) F γ * x)‖ₑ ^ 2 = ‖φ x‖ₑ ^ 2 := fun γ x => by rw [hφ.left_invariant γ x]
  have hΦmass : ∫⁻ h in Φ₀, ‖φ h‖ₑ ^ 2 ∂(adelicGLHaar (Fin 2) (𝓞 F) F) < ⊤ := by
    have hle := lintegral_fd_le F α β Φ₀ S hFD (fun h => ‖φ h‖ₑ ^ 2) hinvf hcover
    rw [Measure.restrict_restrict' (measurableSet_slab F α β), Measure.restrict_restrict' (measurableSet_slab F α β),
      Set.inter_eq_left.mpr hΦ₀] at hle
    exact hle.trans_lt ((lintegral_mono_set Set.inter_subset_left).trans_lt hSmass)
  refine ⟨hcont.aestronglyMeasurable, ?_⟩
  rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top two_ne_zero ENNReal.ofNat_ne_top]
  simpa only [ENNReal.toReal_ofNat, ENNReal.rpow_two] using hΦmass

private theorem lintegral_fd_pos [Countable F] (ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ)
    (φ : AdelicGL2 (𝓞 F) F → ℂ)
    (hφ : IsLsXiFunction (𝓞 F) F ⊤ ξ φ) (hcont : Continuous φ) (g₀ : AdelicGL2 (𝓞 F) F) (hg₀ : φ g₀ ≠ 0)
    (α β : ℝ) (hαg : α < ideleNorm F (Matrix.GeneralLinearGroup.det g₀))
    (hgβ : ideleNorm F (Matrix.GeneralLinearGroup.det g₀) < β) (Φ₀ : Set (AdelicGL2 (𝓞 F) F))
    (hFD : letI : MeasurableSpace (AdelicGL2 (𝓞 F) F) := glBorel (Fin 2) (𝓞 F) F
      IsFundamentalDomain (globalPoints (𝓞 F) F).range Φ₀ ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict (slab F α β))) :
    letI : MeasurableSpace (AdelicGL2 (𝓞 F) F) := glBorel (Fin 2) (𝓞 F) F
    0 < ∫⁻ h in Φ₀, ‖φ h‖ₑ ^ 2 ∂(adelicGLHaar (Fin 2) (𝓞 F) F) := by
  letI : MeasurableSpace (AdelicGL2 (𝓞 F) F) := glBorel (Fin 2) (𝓞 F) F
  haveI : BorelSpace (AdelicGL2 (𝓞 F) F) := borelSpace_glBorel (Fin 2) (𝓞 F) F
  haveI : (adelicGLHaar (Fin 2) (𝓞 F) F).IsHaarMeasure := isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 F) F
  haveI : Countable (globalPoints (𝓞 F) F).range := countable_range F
  haveI := smulInvariant_slab F α β
  set ν := (adelicGLHaar (Fin 2) (𝓞 F) F).restrict (slab F α β) with hν
  set U : Set (AdelicGL2 (𝓞 F) F) := {h | φ h ≠ 0} with hUdef
  have hUopen : IsOpen U := isOpen_ne_fun hcont continuous_const
  have hUinv : ∀ c : (globalPoints (𝓞 F) F).range, c • U = U := by
    rintro ⟨c, γ, rfl⟩
    ext h
    constructor
    · rintro ⟨y, hy, rfl⟩
      show φ (globalPoints (𝓞 F) F γ * y) ≠ 0
      rw [hφ.left_invariant]
      exact hy
    · intro hh
      refine ⟨globalPoints (𝓞 F) F γ⁻¹ * h, ?_, ?_⟩
      · show φ (globalPoints (𝓞 F) F γ⁻¹ * h) ≠ 0
        rw [hφ.left_invariant]
        exact hh
      · show globalPoints (𝓞 F) F γ * (globalPoints (𝓞 F) F γ⁻¹ * h) = h
        rw [← mul_assoc, ← map_mul, mul_inv_cancel, map_one, one_mul]

  set V : Set (AdelicGL2 (𝓞 F) F) :=
    U ∩ {h | ideleNorm F (Matrix.GeneralLinearGroup.det h) ∈ Set.Ioo α β} with hVdef
  have hVopen : IsOpen V :=
    hUopen.inter (isOpen_Ioo.preimage (NumberField.TateGlobal.continuous_ideleNorm_det F))
  have hVne : V.Nonempty := ⟨g₀, hg₀, hαg, hgβ⟩
  have hVsub : V ⊆ U ∩ slab F α β := fun h hh => ⟨hh.1, hh.2.1.le, hh.2.2.le⟩
  rw [pos_iff_ne_zero]
  intro hzero

  have hUΦ : ν (U ∩ Φ₀) = 0 := by
    have hmeas : Measurable fun h => ‖φ h‖ₑ ^ 2 := (hcont.measurable.enorm).pow_const 2
    have hnull := ae_iff.mp ((lintegral_eq_zero_iff hmeas).mp hzero)
    have hUΦ' : (adelicGLHaar (Fin 2) (𝓞 F) F).restrict Φ₀ U = 0 := by
      refine measure_mono_null (fun h (hh : φ h ≠ 0) => ?_) hnull
      show ¬ (‖φ h‖ₑ ^ 2 = (0 : AdelicGL2 (𝓞 F) F → ℝ≥0∞) h)
      simpa [enorm_eq_zero] using hh
    have hsub : ν (U ∩ Φ₀) ≤ (adelicGLHaar (Fin 2) (𝓞 F) F).restrict Φ₀ U := by
      rw [Measure.restrict_apply hUopen.measurableSet]
      exact Measure.restrict_apply_le _ _
    exact le_antisymm (hsub.trans hUΦ'.le) bot_le
  have hU : ν U = 0 := hFD.measure_zero_of_invariant U hUinv hUΦ
  rw [hν, Measure.restrict_apply hUopen.measurableSet] at hU
  exact (hVopen.measure_pos (adelicGLHaar (Fin 2) (𝓞 F) F) hVne).ne' (measure_mono_null hVsub hU)

end SlabGeometry

namespace SlabPairing

open IsDedekindDomain NumberField MeasureTheory
open NumberField.AdelicHaar NumberField.TateGlobal
p2m_open "AutomorphicForm~continuous_unipotentGL2~isIsotypicCuspFormAt_of_mem_isotypicCuspSubmodule"
open scoped ComplexConjugate ENNReal

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

variable {F : Type} [Field F] [NumberField F]

local notation "G𝔸" => AdelicGL2 (𝓞 F) F
local notation "μ𝔸" => adelicGLHaar (Fin 2) (𝓞 F) F

private def wdet (σ : ℝ) (x : G𝔸) : ℝ :=
  ideleNorm F (Matrix.GeneralLinearGroup.det x) ^ (-σ)

private theorem wdet_pos (σ : ℝ) (x : G𝔸) : 0 < wdet σ x :=
  Real.rpow_pos_of_pos (ideleNorm_pos _) _

private theorem wdet_le {σ α β : ℝ} (hα : 0 < α) {x : G𝔸}
    (hx : ideleNorm F (Matrix.GeneralLinearGroup.det x) ∈ Set.Icc α β) :
    wdet σ x ≤ α ^ (-σ) + β ^ (-σ) := by
  have hN : 0 < ideleNorm F (Matrix.GeneralLinearGroup.det x) := ideleNorm_pos _
  have hβ : 0 < β := hα.trans_le (hx.1.trans hx.2)
  by_cases hs : 0 ≤ -σ
  · calc wdet σ x ≤ β ^ (-σ) := Real.rpow_le_rpow hN.le hx.2 hs
      _ ≤ α ^ (-σ) + β ^ (-σ) := le_add_of_nonneg_left (Real.rpow_nonneg hα.le _)
  · calc wdet σ x ≤ α ^ (-σ) := Real.rpow_le_rpow_of_nonpos hα hx.1 (not_le.mp hs).le
      _ ≤ α ^ (-σ) + β ^ (-σ) := le_add_of_nonneg_right (Real.rpow_nonneg hβ.le _)

private theorem measurable_wdet (σ : ℝ)
    (hcont : Continuous fun x : G𝔸 => ideleNorm F (Matrix.GeneralLinearGroup.det x)) :
    Measurable (wdet (F := F) σ) :=
  hcont.measurable.pow_const _

private def _root_.SlabPairing.pair (σ : ℝ) (Φ₀ : Set G𝔸) (u v : G𝔸 → ℂ) : ℂ :=
  ∫ x in Φ₀, u x * conj (v x) * ((ideleNorm F (Matrix.GeneralLinearGroup.det x) ^ (-σ) : ℝ) : ℂ) ∂μ𝔸

p2m_export "SlabPairing" "pair"
private theorem pair_eq (σ : ℝ) (Φ₀ : Set G𝔸) (u v : G𝔸 → ℂ) :
    pair σ Φ₀ u v = ∫ x in Φ₀, u x * conj (v x) * ((wdet σ x : ℝ) : ℂ) ∂μ𝔸 :=
  rfl

private structure _root_.SlabPairing.SlabData (σ α β : ℝ) (Φ₀ : Set G𝔸) : Prop where
  hα : 0 < α
  hΦ₀ : Φ₀ ⊆ {g | ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}
  hΦm : NullMeasurableSet Φ₀ μ𝔸
  hcont : Continuous fun x : G𝔸 => ideleNorm F (Matrix.GeneralLinearGroup.det x)

p2m_export "SlabPairing" "SlabData"
p2m_export_all "SlabPairing" "SlabData"
namespace SlabData
private theorem _root_.SlabPairing.SlabData.ae_norm_wdet_le {σ α β : ℝ} {Φ₀ : Set G𝔸} (hS : SlabData σ α β Φ₀) :
    ∀ᵐ x ∂(Measure.restrict μ𝔸 Φ₀), ‖((wdet σ x : ℝ) : ℂ)‖ ≤ α ^ (-σ) + β ^ (-σ) := by
  rw [ae_restrict_iff'₀ hS.hΦm]
  refine Filter.Eventually.of_forall fun x hx => ?_
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (wdet_pos σ x)]
  exact wdet_le hS.hα (hS.hΦ₀ hx)

end SlabData
p2m_export "SlabPairing" "SlabData.ae_norm_wdet_le"
namespace SlabData
private theorem _root_.SlabPairing.SlabData.aestronglyMeasurable_wdet {σ α β : ℝ} {Φ₀ : Set G𝔸} (hS : SlabData σ α β Φ₀) :
    AEStronglyMeasurable (fun x : G𝔸 => ((wdet σ x : ℝ) : ℂ)) (Measure.restrict μ𝔸 Φ₀) :=
  (Complex.continuous_ofReal.measurable.comp (measurable_wdet σ hS.hcont)).aestronglyMeasurable

end SlabData
p2m_export "SlabPairing" "SlabData.aestronglyMeasurable_wdet"
private theorem integrable_pair_integrand {σ α β : ℝ} {Φ₀ : Set G𝔸} (hS : SlabData σ α β Φ₀) {u v : G𝔸 → ℂ}
    (hu : MemLp u 2 (Measure.restrict μ𝔸 Φ₀)) (hv : MemLp v 2 (Measure.restrict μ𝔸 Φ₀)) :
    Integrable (fun x => u x * conj (v x) * ((wdet σ x : ℝ) : ℂ)) (Measure.restrict μ𝔸 Φ₀) := by
  have huv : Integrable (fun x => u x * conj (v x)) (Measure.restrict μ𝔸 Φ₀) := hu.integrable_mul hv.star
  have h := huv.bdd_mul (SlabData.aestronglyMeasurable_wdet hS) (SlabData.ae_norm_wdet_le hS)
  refine h.congr (Filter.Eventually.of_forall fun x => ?_)
  dsimp only
  ring

private theorem _root_.SlabPairing.pair_add_left {σ α β : ℝ} {Φ₀ : Set G𝔸} (hS : SlabData σ α β Φ₀) {u₁ u₂ v : G𝔸 → ℂ}
    (hu₁ : MemLp u₁ 2 (Measure.restrict μ𝔸 Φ₀)) (hu₂ : MemLp u₂ 2 (Measure.restrict μ𝔸 Φ₀))
    (hv : MemLp v 2 (Measure.restrict μ𝔸 Φ₀)) :
    pair σ Φ₀ (u₁ + u₂) v = pair σ Φ₀ u₁ v + pair σ Φ₀ u₂ v := by
  simp only [pair_eq]
  rw [← integral_add (integrable_pair_integrand hS hu₁ hv) (integrable_pair_integrand hS hu₂ hv)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [Pi.add_apply]
  ring

p2m_export "SlabPairing" "pair_add_left"
private theorem _root_.SlabPairing.pair_smul_left (σ : ℝ) (Φ₀ : Set G𝔸) (c : ℂ) (u v : G𝔸 → ℂ) :
    pair σ Φ₀ (c • u) v = c * pair σ Φ₀ u v := by
  simp only [pair_eq]
  rw [← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

p2m_export "SlabPairing" "pair_smul_left"
private def diagIntegrand (σ : ℝ) (v : G𝔸 → ℂ) (x : G𝔸) : ℝ :=
  ‖v x‖ ^ 2 * wdet σ x

private theorem diagIntegrand_nonneg (σ : ℝ) (v : G𝔸 → ℂ) (x : G𝔸) : 0 ≤ diagIntegrand σ v x :=
  mul_nonneg (sq_nonneg _) (wdet_pos σ x).le

private theorem pair_self_eq (σ : ℝ) (Φ₀ : Set G𝔸) (v : G𝔸 → ℂ) :
    pair σ Φ₀ v v = ((∫ x in Φ₀, diagIntegrand σ v x ∂μ𝔸 : ℝ) : ℂ) := by
  rw [pair_eq, ← integral_complex_ofReal]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [diagIntegrand, Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.ofReal_mul, Complex.ofReal_pow]

private theorem integrable_diagIntegrand {σ α β : ℝ} {Φ₀ : Set G𝔸} (hS : SlabData σ α β Φ₀) {v : G𝔸 → ℂ}
    (hv : MemLp v 2 (Measure.restrict μ𝔸 Φ₀)) : Integrable (diagIntegrand σ v) (Measure.restrict μ𝔸 Φ₀) := by
  have h2 : Integrable (fun x => ‖v x‖ ^ 2) (Measure.restrict μ𝔸 Φ₀) := by
    have h := hv.integrable_norm_rpow (by norm_num) (by norm_num)
    refine h.congr (Filter.Eventually.of_forall fun x => ?_)
    simp
  have hw : AEStronglyMeasurable (wdet (F := F) σ) (Measure.restrict μ𝔸 Φ₀) :=
    (measurable_wdet σ hS.hcont).aestronglyMeasurable
  have hbound : ∀ᵐ x ∂(Measure.restrict μ𝔸 Φ₀), ‖wdet σ x‖ ≤ α ^ (-σ) + β ^ (-σ) := by
    rw [ae_restrict_iff'₀ hS.hΦm]
    refine Filter.Eventually.of_forall fun x hx => ?_
    rw [Real.norm_eq_abs, abs_of_pos (wdet_pos σ x)]
    exact wdet_le hS.hα (hS.hΦ₀ hx)
  have h := h2.bdd_mul hw hbound
  refine h.congr (Filter.Eventually.of_forall fun x => ?_)
  dsimp only [diagIntegrand]
  ring

private theorem diag_nonneg (σ : ℝ) (Φ₀ : Set G𝔸) (v : G𝔸 → ℂ) : 0 ≤ ∫ x in Φ₀, diagIntegrand σ v x ∂μ𝔸 :=
  integral_nonneg (diagIntegrand_nonneg σ v)

private theorem diag_pos {σ α β : ℝ} {Φ₀ : Set G𝔸} (hS : SlabData σ α β Φ₀) {v : G𝔸 → ℂ}
    (hv : MemLp v 2 (Measure.restrict μ𝔸 Φ₀)) (hmass : 0 < ∫⁻ x in Φ₀, ‖v x‖ₑ ^ 2 ∂μ𝔸) :
    0 < ∫ x in Φ₀, diagIntegrand σ v x ∂μ𝔸 := by
  rw [integral_pos_iff_support_of_nonneg (diagIntegrand_nonneg σ v) (integrable_diagIntegrand hS hv)]
  have hsupp : Function.support (diagIntegrand σ v) = Function.support v := by
    ext x
    simp only [Function.mem_support, diagIntegrand, ne_eq, mul_eq_zero, (wdet_pos σ x).ne', or_false,
      pow_eq_zero_iff, OfNat.ofNat_ne_zero, not_false_eq_true, norm_eq_zero]
  rw [hsupp]
  by_contra hzero
  rw [not_lt, nonpos_iff_eq_zero] at hzero
  refine hmass.ne' ((lintegral_congr_ae ?_).trans lintegral_zero)
  rw [Filter.EventuallyEq, ae_iff]
  refine measure_mono_null (fun x hx => ?_) hzero
  simp only [Set.mem_setOf_eq] at hx
  simp only [Function.mem_support, ne_eq]
  intro hvx
  apply hx
  simp [hvx]

private theorem eigenvalue_eq_const_add {σ α β : ℝ} {Φ₀ : Set G𝔸} (hS : SlabData σ α β Φ₀)
    {φ a b : G𝔸 → ℂ} (hφ : MemLp φ 2 (Measure.restrict μ𝔸 Φ₀)) (ha : MemLp a 2 (Measure.restrict μ𝔸 Φ₀))
    (hφmass : 0 < ∫⁻ x in Φ₀, ‖φ x‖ₑ ^ 2 ∂μ𝔸) {Ωφ : G𝔸 → ℂ} (lam c : ℂ)
    (heig : Ωφ = lam • φ) (hlad : Ωφ = (-(1 / 4 : ℂ)) • a + c • φ) (hadj : pair σ Φ₀ a φ = -pair σ Φ₀ b b) :
    ∃ t : ℝ, 0 ≤ t ∧ lam = c + t ∧ (t = 0 → ∫ x in Φ₀, diagIntegrand σ b x ∂μ𝔸 = 0) := by
  set P : ℝ := ∫ x in Φ₀, diagIntegrand σ φ x ∂μ𝔸 with hP
  set B : ℝ := ∫ x in Φ₀, diagIntegrand σ b x ∂μ𝔸 with hB
  have hPpos : 0 < P := diag_pos hS hφ hφmass
  have hBnn : 0 ≤ B := diag_nonneg σ Φ₀ b

  have h1 : pair σ Φ₀ Ωφ φ = lam * (P : ℂ) := by
    rw [heig, pair_smul_left, pair_self_eq]
  have h2 : pair σ Φ₀ Ωφ φ = (1 / 4 : ℂ) * (B : ℂ) + c * (P : ℂ) := by
    rw [hlad, pair_add_left hS (ha.const_smul _) (hφ.const_smul _) hφ, pair_smul_left, pair_smul_left, hadj,
      pair_self_eq, pair_self_eq]
    ring
  have hkey : lam * (P : ℂ) = (1 / 4 : ℂ) * (B : ℂ) + c * (P : ℂ) := h1.symm.trans h2
  refine ⟨B / (4 * P), by positivity, ?_, fun ht => ?_⟩
  · have hPne : (P : ℂ) ≠ 0 := by exact_mod_cast hPpos.ne'
    push_cast
    field_simp
    linear_combination (4 : ℂ) * hkey
  · rw [div_eq_zero_iff] at ht
    rcases ht with ht | ht
    · exact ht
    · exact absurd ht (by positivity)

end SlabPairing

namespace SkewAdjoint

open IsDedekindDomain NumberField MeasureTheory
open NumberField.AdelicHaar NumberField.TateGlobal NumberField.InfinitePlace.Completion
p2m_open "AutomorphicForm~continuous_unipotentGL2~isIsotypicCuspFormAt_of_mem_isotypicCuspSubmodule"
open scoped ComplexConjugate ENNReal

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

variable {F : Type} [Field F] [NumberField F]

local notation "G𝔸" => AdelicGL2 (𝓞 F) F
local notation "μ𝔸" => adelicGLHaar (Fin 2) (𝓞 F) F

private def wdet (σ : ℝ) (x : G𝔸) : ℝ :=
  ideleNorm F (Matrix.GeneralLinearGroup.det x) ^ (-σ)

private theorem wdet_pos (σ : ℝ) (x : G𝔸) : 0 < wdet σ x :=
  Real.rpow_pos_of_pos (ideleNorm_pos _) _

private theorem wdet_le {σ α β : ℝ} (hα : 0 < α) {x : G𝔸}
    (hx : ideleNorm F (Matrix.GeneralLinearGroup.det x) ∈ Set.Icc α β) :
    wdet σ x ≤ α ^ (-σ) + β ^ (-σ) := by
  have hN : 0 < ideleNorm F (Matrix.GeneralLinearGroup.det x) := ideleNorm_pos _
  have hβ : 0 < β := hα.trans_le (hx.1.trans hx.2)
  by_cases hs : 0 ≤ -σ
  · calc wdet σ x ≤ β ^ (-σ) := Real.rpow_le_rpow hN.le hx.2 hs
      _ ≤ α ^ (-σ) + β ^ (-σ) := le_add_of_nonneg_left (Real.rpow_nonneg hα.le _)
  · calc wdet σ x ≤ α ^ (-σ) := Real.rpow_le_rpow_of_nonpos hα hx.1 (not_le.mp hs).le
      _ ≤ α ^ (-σ) + β ^ (-σ) := le_add_of_nonneg_right (Real.rpow_nonneg hβ.le _)

private theorem measurable_wdet (σ : ℝ)
    (hcont : Continuous fun x : G𝔸 => ideleNorm F (Matrix.GeneralLinearGroup.det x)) :
    Measurable (wdet (F := F) σ) :=
  hcont.measurable.pow_const _

private def pair (σ : ℝ) (Φ₀ : Set G𝔸) (u v : G𝔸 → ℂ) : ℂ :=
  ∫ x in Φ₀, u x * conj (v x) * ((ideleNorm F (Matrix.GeneralLinearGroup.det x) ^ (-σ) : ℝ) : ℂ) ∂μ𝔸

private theorem pair_eq (σ : ℝ) (Φ₀ : Set G𝔸) (u v : G𝔸 → ℂ) :
    pair σ Φ₀ u v = ∫ x in Φ₀, u x * conj (v x) * ((wdet σ x : ℝ) : ℂ) ∂μ𝔸 :=
  rfl

private structure _root_.SkewAdjoint.SlabData (σ α β : ℝ) (Φ₀ : Set G𝔸) : Prop where
  hα : 0 < α
  hΦ₀ : Φ₀ ⊆ {g | ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}
  hΦm : NullMeasurableSet Φ₀ μ𝔸
  hcont : Continuous fun x : G𝔸 => ideleNorm F (Matrix.GeneralLinearGroup.det x)

p2m_export "SkewAdjoint" "SlabData"
p2m_export_all "SkewAdjoint" "SlabData"
namespace SlabData
private theorem _root_.SkewAdjoint.SlabData.ae_norm_wdet_le {σ α β : ℝ} {Φ₀ : Set G𝔸} (hS : SlabData σ α β Φ₀) :
    ∀ᵐ x ∂(Measure.restrict μ𝔸 Φ₀), ‖((wdet σ x : ℝ) : ℂ)‖ ≤ α ^ (-σ) + β ^ (-σ) := by
  rw [ae_restrict_iff'₀ hS.hΦm]
  refine Filter.Eventually.of_forall fun x hx => ?_
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (wdet_pos σ x)]
  exact wdet_le hS.hα (hS.hΦ₀ hx)

end SlabData
p2m_export "SkewAdjoint" "SlabData.ae_norm_wdet_le"
namespace SlabData
private theorem _root_.SkewAdjoint.SlabData.aestronglyMeasurable_wdet {σ α β : ℝ} {Φ₀ : Set G𝔸} (hS : SlabData σ α β Φ₀) :
    AEStronglyMeasurable (fun x : G𝔸 => ((wdet σ x : ℝ) : ℂ)) (Measure.restrict μ𝔸 Φ₀) :=
  (Complex.continuous_ofReal.measurable.comp (measurable_wdet σ hS.hcont)).aestronglyMeasurable

end SlabData
p2m_export "SkewAdjoint" "SlabData.aestronglyMeasurable_wdet"
private theorem integrable_pair_integrand {σ α β : ℝ} {Φ₀ : Set G𝔸} (hS : SlabData σ α β Φ₀) {u v : G𝔸 → ℂ}
    (hu : MemLp u 2 (Measure.restrict μ𝔸 Φ₀)) (hv : MemLp v 2 (Measure.restrict μ𝔸 Φ₀)) :
    Integrable (fun x => u x * conj (v x) * ((wdet σ x : ℝ) : ℂ)) (Measure.restrict μ𝔸 Φ₀) := by
  have huv : Integrable (fun x => u x * conj (v x)) (Measure.restrict μ𝔸 Φ₀) := hu.integrable_mul hv.star
  have h := huv.bdd_mul (SlabData.aestronglyMeasurable_wdet hS) (SlabData.ae_norm_wdet_le hS)
  refine h.congr (Filter.Eventually.of_forall fun x => ?_)
  dsimp only
  ring

private theorem pair_add_left {σ α β : ℝ} {Φ₀ : Set G𝔸} (hS : SlabData σ α β Φ₀) {u₁ u₂ v : G𝔸 → ℂ}
    (hu₁ : MemLp u₁ 2 (Measure.restrict μ𝔸 Φ₀)) (hu₂ : MemLp u₂ 2 (Measure.restrict μ𝔸 Φ₀))
    (hv : MemLp v 2 (Measure.restrict μ𝔸 Φ₀)) :
    pair σ Φ₀ (u₁ + u₂) v = pair σ Φ₀ u₁ v + pair σ Φ₀ u₂ v := by
  simp only [pair_eq]
  rw [← integral_add (integrable_pair_integrand hS hu₁ hv) (integrable_pair_integrand hS hu₂ hv)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [Pi.add_apply]
  ring

private theorem pair_smul_left (σ : ℝ) (Φ₀ : Set G𝔸) (c : ℂ) (u v : G𝔸 → ℂ) :
    pair σ Φ₀ (c • u) v = c * pair σ Φ₀ u v := by
  simp only [pair_eq]
  rw [← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

private theorem pair_neg_right (σ : ℝ) (Φ₀ : Set G𝔸) (u v : G𝔸 → ℂ) : pair σ Φ₀ u (-v) = -pair σ Φ₀ u v := by
  simp only [pair_eq]
  rw [← integral_neg]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [Pi.neg_apply, map_neg]
  ring

private theorem pair_smul_right (σ : ℝ) (Φ₀ : Set G𝔸) (c : ℂ) (u v : G𝔸 → ℂ) :
    pair σ Φ₀ u (c • v) = conj c * pair σ Φ₀ u v := by
  simp only [pair_eq]
  rw [← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [Pi.smul_apply, smul_eq_mul, map_mul]
  ring

private theorem pair_add_right {σ α β : ℝ} {Φ₀ : Set G𝔸} (hS : SlabData σ α β Φ₀) {u v₁ v₂ : G𝔸 → ℂ}
    (hu : MemLp u 2 (Measure.restrict μ𝔸 Φ₀)) (hv₁ : MemLp v₁ 2 (Measure.restrict μ𝔸 Φ₀))
    (hv₂ : MemLp v₂ 2 (Measure.restrict μ𝔸 Φ₀)) :
    pair σ Φ₀ u (v₁ + v₂) = pair σ Φ₀ u v₁ + pair σ Φ₀ u v₂ := by
  simp only [pair_eq]
  rw [← integral_add (integrable_pair_integrand hS hu hv₁) (integrable_pair_integrand hS hu hv₂)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [Pi.add_apply, map_add]
  ring

private theorem pair_sub_right {σ α β : ℝ} {Φ₀ : Set G𝔸} (hS : SlabData σ α β Φ₀) {u v₁ v₂ : G𝔸 → ℂ}
    (hu : MemLp u 2 (Measure.restrict μ𝔸 Φ₀)) (hv₁ : MemLp v₁ 2 (Measure.restrict μ𝔸 Φ₀))
    (hv₂ : MemLp v₂ 2 (Measure.restrict μ𝔸 Φ₀)) :
    pair σ Φ₀ u (v₁ - v₂) = pair σ Φ₀ u v₁ - pair σ Φ₀ u v₂ := by
  rw [sub_eq_add_neg, pair_add_right hS hu hv₁ hv₂.neg, pair_neg_right, sub_eq_add_neg]

private def _root_.SkewAdjoint.leftDeriv {w : InfinitePlace F} (hw : w.IsReal) (d : ArchDir) (α : G𝔸 → ℂ) : G𝔸 → ℂ :=
  fun y => deriv (fun t : ℝ => α (archFlowAt hw d (-t) * y)) 0

p2m_export "SkewAdjoint" "leftDeriv"
private theorem archDerivAt_conj {w : InfinitePlace F} (hw : w.IsReal) (d : ArchDir) (ψ : G𝔸 → ℂ) (y : G𝔸) :
    archDerivAt hw d (fun z => conj (ψ z)) y = conj (archDerivAt hw d ψ y) := by
  simp only [archDerivAt]
  have h : (fun t : ℝ => conj (ψ (y * archFlowAt hw d t))) = fun t : ℝ => star (ψ (y * archFlowAt hw d t)) := rfl
  rw [h, deriv.star]
  rfl

private theorem isArchSmoothAt_conj {w : InfinitePlace F} {hw : w.IsReal} {ψ : G𝔸 → ℂ} (h : IsArchSmoothAt hw ψ) :
    IsArchSmoothAt hw fun z => conj (ψ z) := by
  intro g
  exact Complex.conjCLE.contDiff.comp_contDiffOn (h g)

private theorem continuous_conj_comp_inv {ψ : G𝔸 → ℂ} (h : Continuous ψ) : Continuous fun z : G𝔸 => conj (ψ z⁻¹) :=
  Complex.continuous_conj.comp (h.comp continuous_inv)

private theorem hasCompactSupport_conj_comp_inv {ψ : G𝔸 → ℂ} (h : HasCompactSupport ψ) :
    HasCompactSupport fun z : G𝔸 => conj (ψ z⁻¹) := by
  have h1 : HasCompactSupport fun z : G𝔸 => ψ z⁻¹ := h.comp_homeomorph (Homeomorph.inv G𝔸)
  exact h1.comp_left (map_zero (starRingEnd ℂ))

private theorem det_archFlowMatrix (d : ArchDir) (t : ℝ) :
    ((archFlowMatrix d t : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ).det = 1 := by
  cases d
  · rw [archFlowMatrix, splitTorusGL2_coe, Matrix.det_fin_two_of, ← Real.exp_add, add_neg_cancel, Real.exp_zero]
    ring
  · rw [archFlowMatrix, unipotentGL2_coe, Matrix.det_fin_two_of]
    ring
  · rw [archFlowMatrix, lowerUnipotentGL2_coe, Matrix.det_fin_two_of]
    ring

private theorem det_glArch_archRealGLAt {w : InfinitePlace F} (hw : w.IsReal) {m : GL (Fin 2) ℝ}
    (hm : (m : Matrix (Fin 2) (Fin 2) ℝ).det = 1) :
    ((AdelicLevel.glArch (𝓞 F) F (archRealGLAt hw m) : GL (Fin 2) (InfiniteAdeleRing F)) :
        Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)).det = 1 := by
  have h1 : AdelicLevel.glArch (𝓞 F) F (archRealGLAt hw m)
      = archGLIncl F w (glEquivOfRingEquiv (ringEquivRealOfIsReal hw).symm m) :=
    glArch_adelicArchGLIncl F _
  rw [h1]
  funext v
  rw [show ((archGLIncl F w (glEquivOfRingEquiv (ringEquivRealOfIsReal hw).symm m) :
        GL (Fin 2) (InfiniteAdeleRing F)) : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)).det v
      = ((Pi.evalRingHom (fun u : InfinitePlace F => u.Completion) v).mapMatrix
          ((archGLIncl F w (glEquivOfRingEquiv (ringEquivRealOfIsReal hw).symm m) :
            GL (Fin 2) (InfiniteAdeleRing F)) : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F))).det from
      RingHom.map_det (Pi.evalRingHom (fun u : InfinitePlace F => u.Completion) v)
        ((archGLIncl F w (glEquivOfRingEquiv (ringEquivRealOfIsReal hw).symm m) :
            GL (Fin 2) (InfiniteAdeleRing F)) : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F))]
  by_cases hv : v = w
  · subst hv
    have hM : (Pi.evalRingHom (fun u : InfinitePlace F => u.Completion) v).mapMatrix
          ((archGLIncl F v (glEquivOfRingEquiv (ringEquivRealOfIsReal hw).symm m) :
            GL (Fin 2) (InfiniteAdeleRing F)) : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F))
        = ((glEquivOfRingEquiv (ringEquivRealOfIsReal hw).symm m : GL (Fin 2) v.Completion) :
            Matrix (Fin 2) (Fin 2) v.Completion) := by
      ext i j : 1
      exact archMatrixUpdate_apply_self F v _ i j
    have hM2 : ((glEquivOfRingEquiv (ringEquivRealOfIsReal hw).symm m : GL (Fin 2) v.Completion) :
          Matrix (Fin 2) (Fin 2) v.Completion)
        = (ringEquivRealOfIsReal hw).symm.toRingHom.mapMatrix (m : Matrix (Fin 2) (Fin 2) ℝ) := by
      ext i j
      rfl
    rw [hM, hM2, ← RingHom.map_det, hm, map_one]
    rfl
  · have hM : (Pi.evalRingHom (fun u : InfinitePlace F => u.Completion) v).mapMatrix
          ((archGLIncl F w (glEquivOfRingEquiv (ringEquivRealOfIsReal hw).symm m) :
            GL (Fin 2) (InfiniteAdeleRing F)) : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) = 1 := by
      ext i j : 1
      exact archMatrixUpdate_apply_of_ne F w _ i j hv
    rw [hM, Matrix.det_one]
    rfl

private theorem det_archFlowAt {w : InfinitePlace F} (hw : w.IsReal) (d : ArchDir) (t : ℝ) :
    Matrix.GeneralLinearGroup.det (archFlowAt hw d t) = 1 := by
  apply Units.ext
  show ((archFlowAt hw d t : G𝔸) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)).det = 1
  have hA : AdelicLevel.adeleArch (𝓞 F) F ((archFlowAt hw d t : G𝔸) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)).det
      = 1 := by
    have h : ((AdelicLevel.glArch (𝓞 F) F (archFlowAt hw d t) : GL (Fin 2) (InfiniteAdeleRing F)) :
          Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F))
        = (AdelicLevel.adeleArch (𝓞 F) F).mapMatrix ((archFlowAt hw d t : G𝔸) : Matrix (Fin 2) (Fin 2) _) := by
      ext i j
      rfl
    rw [RingHom.map_det, ← h]
    exact det_glArch_archRealGLAt hw (det_archFlowMatrix d t)
  have hF : AdelicLevel.adeleFin (𝓞 F) F ((archFlowAt hw d t : G𝔸) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)).det
      = 1 := by
    have h : ((AdelicLevel.glFin (𝓞 F) F (archFlowAt hw d t) : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)) :
          Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F))
        = (AdelicLevel.adeleFin (𝓞 F) F).mapMatrix ((archFlowAt hw d t : G𝔸) : Matrix (Fin 2) (Fin 2) _) := by
      ext i j
      rfl
    have h2 : AdelicLevel.glFin (𝓞 F) F (archFlowAt hw d t) = 1 := glFin_adelicArchGLIncl F _
    rw [RingHom.map_det, ← h, h2, Units.val_one, Matrix.det_one]
  exact Prod.ext hA hF

private theorem wdet_mul_archFlowAt (σ : ℝ) {w : InfinitePlace F} (hw : w.IsReal) (d : ArchDir) (y : G𝔸) (t : ℝ) :
    wdet σ (y * archFlowAt hw d t) = wdet σ y := by
  unfold wdet
  rw [map_mul, det_archFlowAt, mul_one]

section

variable {w : InfinitePlace F} {hw : w.IsReal} {σ α β : ℝ} {Φ₀ : Set (AdelicGL2 (𝓞 F) F)} (hS : SlabData σ α β Φ₀)
  (hFD : IsFundamentalDomain (globalPoints (𝓞 F) F).range Φ₀
    (Measure.restrict (adelicGLHaar (Fin 2) (𝓞 F) F)
      {g : AdelicGL2 (𝓞 F) F | ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}))
  (ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ)
  (hσ : ∀ z : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ), ‖((ξ z : ℂˣ) : ℂ)‖ = ideleNorm F (z : (AdeleRing (𝓞 F) F)ˣ) ^ σ)

private def wtℂ (σ : ℝ) (y : G𝔸) : ℂ := ((ideleNorm F (Matrix.GeneralLinearGroup.det y) ^ (-σ) : ℝ) : ℂ)

include hS in
private theorem continuous_wtℂ : Continuous (wtℂ (F := F) σ) := by
  unfold wtℂ
  refine Complex.continuous_ofReal.comp (hS.hcont.rpow_const fun x => Or.inl ?_)
  exact (ideleNorm_pos _).ne'

private theorem wtℂ_mul_archFlowAt (d : ArchDir) (y : G𝔸) (t : ℝ) : wtℂ σ (y * archFlowAt hw d t) = wtℂ σ y := by
  unfold wtℂ
  rw [map_mul, det_archFlowAt, mul_one]

private theorem archDerivAt_eq_rightConv_of_repro {ψ β' : G𝔸 → ℂ} (d : ArchDir)
    (hb_ψ : ∀ (d : ArchDir) (γ : G𝔸 → ℂ), IsFactorizableTestFn F γ →
      archDerivAt hw d (rightConv F ψ γ) = rightConv F ψ (leftDeriv hw d γ))
    (hβ' : IsFactorizableTestFn F β') (hrepro : rightConv F ψ β' = ψ) :
    archDerivAt hw d ψ = rightConv F ψ (leftDeriv hw d β') := by
  have h := hb_ψ d β' hβ'
  rwa [hrepro] at h

include hS hFD hσ in
private theorem memLp_archDerivAt_of_repro {ψ β' : G𝔸 → ℂ} (d : ArchDir)
    (hψL : IsLsXiFunction (𝓞 F) F ⊤ ξ ψ) (hψc : Continuous ψ) (hψ₂ : MemLp ψ 2 (Measure.restrict μ𝔸 Φ₀))
    (hb_ψ : ∀ (d : ArchDir) (γ : G𝔸 → ℂ), IsFactorizableTestFn F γ →
      archDerivAt hw d (rightConv F ψ γ) = rightConv F ψ (leftDeriv hw d γ))
    (hc : ∀ (d : ArchDir) (γ : G𝔸 → ℂ), IsFactorizableTestFn F γ → IsFactorizableTestFn F (leftDeriv hw d γ))
    (hβ' : IsFactorizableTestFn F β') (hrepro : rightConv F ψ β' = ψ) :
    MemLp (archDerivAt hw d ψ) 2 (Measure.restrict μ𝔸 Φ₀) := by
  rw [archDerivAt_eq_rightConv_of_repro d hb_ψ hβ' hrepro]
  obtain ⟨hlc, hls⟩ := continuous_and_hasCompactSupport_of_isFactorizableTestFn F _ (hc d β' hβ')
  exact (adjoint_rightConv_weightedPairing_of_isLsXiFunction F α β hS.hα Φ₀ hS.hΦ₀ hFD ξ σ hσ ψ ψ hψL hψL hψc hψc
    hψ₂ hψ₂ _ hlc hls).1

include hS hFD hσ in

private theorem pair_archDerivAt_left (d : ArchDir) {φ b βφ βb : G𝔸 → ℂ}
    (hφL : IsLsXiFunction (𝓞 F) F ⊤ ξ φ) (hφc : Continuous φ) (hφ₂ : MemLp φ 2 (Measure.restrict μ𝔸 Φ₀))
    (hbL : IsLsXiFunction (𝓞 F) F ⊤ ξ b) (hbc : Continuous b) (hb₂ : MemLp b 2 (Measure.restrict μ𝔸 Φ₀))
    (hDφL : IsLsXiFunction (𝓞 F) F ⊤ ξ (archDerivAt hw d φ)) (hDφc : Continuous (archDerivAt hw d φ))
    (hβφ : IsFactorizableTestFn F βφ) (hreproφ : rightConv F φ βφ = φ)
    (hβb : IsFactorizableTestFn F βb) (hreprob : rightConv F b βb = b)
    (hb_φ : ∀ (d : ArchDir) (γ : G𝔸 → ℂ), IsFactorizableTestFn F γ →
      archDerivAt hw d (rightConv F φ γ) = rightConv F φ (leftDeriv hw d γ))
    (hb_b : ∀ (d : ArchDir) (γ : G𝔸 → ℂ), IsFactorizableTestFn F γ →
      archDerivAt hw d (rightConv F b γ) = rightConv F b (leftDeriv hw d γ))
    (hc : ∀ (d : ArchDir) (γ : G𝔸 → ℂ), IsFactorizableTestFn F γ → IsFactorizableTestFn F (leftDeriv hw d γ))
    (hd₁ : ∀ (d : ArchDir) (γ : G𝔸 → ℂ) (y : G𝔸), leftDeriv hw d γ y⁻¹ = archDerivAt hw d (fun z => γ z⁻¹) y)
    (hd₂ : ∀ γ : G𝔸 → ℂ, IsFactorizableTestFn F γ → IsArchSmoothAt hw fun z => γ z⁻¹)
    (he : ∀ (d : ArchDir) (γ₀ wt : G𝔸 → ℂ), Continuous γ₀ → HasCompactSupport γ₀ → IsArchSmoothAt hw γ₀ →
      Continuous (archDerivAt hw d γ₀) → Continuous wt → (∀ (y : G𝔸) (t : ℝ), wt (y * archFlowAt hw d t) = wt y) →
      rightConv F φ (fun y => archDerivAt hw d γ₀ y * wt y)
        = -rightConv F (archDerivAt hw d φ) (fun y => γ₀ y * wt y)) :
    pair σ Φ₀ (archDerivAt hw d b) φ = -pair σ Φ₀ b (archDerivAt hw d φ) := by

  have h1 := archDerivAt_eq_rightConv_of_repro d hb_b hβb hreprob
  have hlD := hc d βb hβb
  obtain ⟨hlc, hls⟩ := continuous_and_hasCompactSupport_of_isFactorizableTestFn F _ hlD
  obtain ⟨hβc, hβs⟩ := continuous_and_hasCompactSupport_of_isFactorizableTestFn F _ hβb

  have A := (adjoint_rightConv_weightedPairing_of_isLsXiFunction F α β hS.hα Φ₀ hS.hΦ₀ hFD ξ σ hσ b φ hbL hφL hbc
    hφc hb₂ hφ₂ _ hlc hls).2.2

  have hflat : (fun y : G𝔸 => conj (leftDeriv hw d βb y⁻¹) *
        ((ideleNorm F (Matrix.GeneralLinearGroup.det y) ^ (-σ) : ℝ) : ℂ))
      = fun y => archDerivAt hw d (fun z => conj (βb z⁻¹)) y * wtℂ σ y := by
    funext y
    rw [hd₁ d βb y, archDerivAt_conj]
    rfl

  have hDγ : Continuous (archDerivAt hw d fun z : G𝔸 => conj (βb z⁻¹)) := by
    have : (archDerivAt hw d fun z : G𝔸 => conj (βb z⁻¹)) = fun y => conj (leftDeriv hw d βb y⁻¹) := by
      funext y
      rw [hd₁ d βb y, archDerivAt_conj]
    rw [this]
    exact continuous_conj_comp_inv hlc
  have E := he d (fun z => conj (βb z⁻¹)) (wtℂ σ) (continuous_conj_comp_inv hβc) (hasCompactSupport_conj_comp_inv hβs)
    (isArchSmoothAt_conj (hd₂ βb hβb)) hDγ (continuous_wtℂ hS) (wtℂ_mul_archFlowAt d)

  have hDφ₂ := memLp_archDerivAt_of_repro hS hFD ξ hσ d hφL hφc hφ₂ hb_φ hc hβφ hreproφ
  have B := (adjoint_rightConv_weightedPairing_of_isLsXiFunction F α β hS.hα Φ₀ hS.hΦ₀ hFD ξ σ hσ b
    (archDerivAt hw d φ) hbL hDφL hbc hDφc hb₂ hDφ₂ βb hβc hβs).2.2
  rw [hreprob] at B
  calc pair σ Φ₀ (archDerivAt hw d b) φ
      = pair σ Φ₀ (rightConv F b (leftDeriv hw d βb)) φ := by rw [h1]
    _ = pair σ Φ₀ b (rightConv F φ (fun y => conj (leftDeriv hw d βb y⁻¹) *
          ((ideleNorm F (Matrix.GeneralLinearGroup.det y) ^ (-σ) : ℝ) : ℂ))) := A
    _ = pair σ Φ₀ b (rightConv F φ (fun y => archDerivAt hw d (fun z => conj (βb z⁻¹)) y * wtℂ σ y)) := by
          rw [hflat]
    _ = pair σ Φ₀ b (-rightConv F (archDerivAt hw d φ) (fun y => conj (βb y⁻¹) * wtℂ σ y)) := by rw [E]
    _ = -pair σ Φ₀ b (rightConv F (archDerivAt hw d φ) (fun y => conj (βb y⁻¹) * wtℂ σ y)) := pair_neg_right _ _ _ _
    _ = -pair σ Φ₀ b (archDerivAt hw d φ) := congrArg Neg.neg B.symm

end

private def _root_.SkewAdjoint.lowerOp {w : InfinitePlace F} (hw : w.IsReal) (φ : G𝔸 → ℂ) : G𝔸 → ℂ :=
  archDerivAt hw .H φ - Complex.I • (archDerivAt hw .E φ + archDerivAt hw .Fm φ)

p2m_export "SkewAdjoint" "lowerOp"
private def _root_.SkewAdjoint.raiseOp {w : InfinitePlace F} (hw : w.IsReal) (φ : G𝔸 → ℂ) : G𝔸 → ℂ :=
  archDerivAt hw .H φ + Complex.I • (archDerivAt hw .E φ + archDerivAt hw .Fm φ)

p2m_export "SkewAdjoint" "raiseOp"
private theorem pair_raiseOp_eq_neg_pair_lowerOp {w : InfinitePlace F} {hw : w.IsReal} {σ α β : ℝ} {Φ₀ : Set G𝔸}
    (hS : SlabData σ α β Φ₀) {φ b : G𝔸 → ℂ} (hφ₂ : MemLp φ 2 (Measure.restrict μ𝔸 Φ₀))
    (hb₂ : MemLp b 2 (Measure.restrict μ𝔸 Φ₀))
    (hDb₂ : ∀ d : ArchDir, MemLp (archDerivAt hw d b) 2 (Measure.restrict μ𝔸 Φ₀))
    (hDφ₂ : ∀ d : ArchDir, MemLp (archDerivAt hw d φ) 2 (Measure.restrict μ𝔸 Φ₀))
    (hskew : ∀ d : ArchDir, pair σ Φ₀ (archDerivAt hw d b) φ = -pair σ Φ₀ b (archDerivAt hw d φ)) :
    pair σ Φ₀ (raiseOp hw b) φ = -pair σ Φ₀ b (lowerOp hw φ) := by
  unfold raiseOp lowerOp
  rw [pair_add_left hS (hDb₂ .H) (((hDb₂ .E).add (hDb₂ .Fm)).const_smul Complex.I) hφ₂, pair_smul_left,
    pair_add_left hS (hDb₂ .E) (hDb₂ .Fm) hφ₂, hskew .H, hskew .E, hskew .Fm,
    pair_sub_right hS hb₂ (hDφ₂ .H) (((hDφ₂ .E).add (hDφ₂ .Fm)).const_smul Complex.I), pair_smul_right,
    pair_add_right hS hb₂ (hDφ₂ .E) (hDφ₂ .Fm), Complex.conj_I]
  ring

end SkewAdjoint

namespace ArchExclusion

open scoped Real
p2m_open "AutomorphicForm~continuous_unipotentGL2~isIsotypicCuspFormAt_of_mem_isotypicCuspSubmodule Matrix"
open NumberField IsDedekindDomain NumberField.InfinitePlace NumberField.InfinitePlace.Completion

variable {K : Type} [Field K] [NumberField K]

private theorem det_of_symm_one : (Matrix.of (Matrix.of.symm (1 : Matrix (Fin 2) (Fin 2) ℝ))).det ≠ 0 := by
  rw [Equiv.apply_symm_apply, Matrix.det_one]
  exact one_ne_zero

private theorem det_coe_ne_zero (m : GL (Fin 2) ℝ) : ((m : Matrix (Fin 2) (Fin 2) ℝ)).det ≠ 0 :=
  ((Matrix.isUnit_iff_isUnit_det _).1 m.isUnit).ne_zero

private theorem archRealGLAt_eq_archRealLiftAt {w : InfinitePlace K} (hw : w.IsReal) (m : GL (Fin 2) ℝ) :
    archRealGLAt hw m = archRealLiftAt hw (Matrix.of.symm (m : Matrix (Fin 2) (Fin 2) ℝ)) := by
  have h := archRealLiftAt_mul_archRealGLAt hw det_of_symm_one m
  rw [archRealLiftAt_of_symm_one, one_mul, Equiv.apply_symm_apply, one_mul] at h
  exact h

private theorem hasDerivAt_conj_flow (k : GL (Fin 2) ℝ) (d : ArchDir) :
    HasDerivAt
      (fun t : ℝ =>
        (Matrix.of.symm (((k⁻¹ * archFlowMatrix d t * k : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)) :
          Fin 2 → Fin 2 → ℝ))
      (Matrix.of.symm
        (((k⁻¹ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) * archDirMatrix d * (k : Matrix (Fin 2) (Fin 2) ℝ)))
      0 := by
  rw [hasDerivAt_pi]
  intro i
  rw [hasDerivAt_pi]
  intro j
  simp only [Matrix.of_symm_apply, Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two]
  exact ((((hasDerivAt_archFlowMatrix_apply d 0 0).const_mul _).fun_add
      ((hasDerivAt_archFlowMatrix_apply d 1 0).const_mul _)).mul_const _).fun_add
    ((((hasDerivAt_archFlowMatrix_apply d 0 1).const_mul _).fun_add
      ((hasDerivAt_archFlowMatrix_apply d 1 1).const_mul _)).mul_const _)

private theorem archDerivAt_translate_eq_fderiv {w : InfinitePlace K} {hw : w.IsReal}
    {φ : AdelicGL2 (𝓞 K) K → ℂ} (hφ : IsArchSmoothAt hw φ) (k : GL (Fin 2) ℝ) (d : ArchDir)
    (g : AdelicGL2 (𝓞 K) K) :
    archDerivAt hw d (fun x => φ (x * archRealGLAt hw k)) g
      = fderiv ℝ (fun e : Fin 2 → Fin 2 → ℝ => φ (g * archRealGLAt hw k * archRealLiftAt hw e)) (Matrix.of.symm 1)
          (Matrix.of.symm
            (((k⁻¹ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) * archDirMatrix d
              * (k : Matrix (Fin 2) (Fin 2) ℝ))) := by
  have hopen := isOpen_setOf_det_ne_zero
  have hfun : (fun t : ℝ => (fun x => φ (x * archRealGLAt hw k)) (g * archFlowAt hw d t))
      = fun t : ℝ => (fun e : Fin 2 → Fin 2 → ℝ => φ (g * archRealGLAt hw k * archRealLiftAt hw e))
          (Matrix.of.symm (((k⁻¹ * archFlowMatrix d t * k : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ))) := by
    funext t
    show φ (g * archFlowAt hw d t * archRealGLAt hw k) = φ (g * archRealGLAt hw k * archRealLiftAt hw
      (Matrix.of.symm (((k⁻¹ * archFlowMatrix d t * k : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ))))
    rw [← archRealGLAt_eq_archRealLiftAt hw, map_mul, map_mul, map_inv, archFlowAt]
    exact congrArg φ (by group)
  have hdiff : HasFDerivAt (fun e : Fin 2 → Fin 2 → ℝ => φ (g * archRealGLAt hw k * archRealLiftAt hw e))
      (fderiv ℝ (fun e : Fin 2 → Fin 2 → ℝ => φ (g * archRealGLAt hw k * archRealLiftAt hw e)) (Matrix.of.symm 1))
      (Matrix.of.symm (((k⁻¹ * archFlowMatrix d 0 * k : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ))) := by
    rw [archFlowMatrix_zero, mul_one, inv_mul_cancel, Units.val_one]
    exact (((hφ (g * archRealGLAt hw k)).contDiffAt (hopen.mem_nhds det_of_symm_one)).differentiableAt
      (by simp)).hasFDerivAt
  show deriv (fun t : ℝ => (fun x => φ (x * archRealGLAt hw k)) (g * archFlowAt hw d t)) 0 = _
  rw [hfun]
  exact (hdiff.comp_hasDerivAt (0 : ℝ) (hasDerivAt_conj_flow k d)).deriv

private theorem archDerivAt_eq_fderiv {w : InfinitePlace K} {hw : w.IsReal}
    {φ : AdelicGL2 (𝓞 K) K → ℂ} (hφ : IsArchSmoothAt hw φ) (d : ArchDir) (x : AdelicGL2 (𝓞 K) K) :
    archDerivAt hw d φ x
      = fderiv ℝ (fun e : Fin 2 → Fin 2 → ℝ => φ (x * archRealLiftAt hw e)) (Matrix.of.symm 1)
          (Matrix.of.symm (archDirMatrix d)) := by
  have h := archDerivAt_translate_eq_fderiv hφ 1 d x
  simp only [map_one, mul_one, inv_one, Units.val_one, one_mul] at h
  exact h

private def rotK (s : ℝ) : GL (Fin 2) ℝ where
  val := !![(Real.sqrt (1 + s ^ 2))⁻¹, -(s * (Real.sqrt (1 + s ^ 2))⁻¹);
    s * (Real.sqrt (1 + s ^ 2))⁻¹, (Real.sqrt (1 + s ^ 2))⁻¹]
  inv := !![(Real.sqrt (1 + s ^ 2))⁻¹, s * (Real.sqrt (1 + s ^ 2))⁻¹;
    -(s * (Real.sqrt (1 + s ^ 2))⁻¹), (Real.sqrt (1 + s ^ 2))⁻¹]
  val_inv := by
    have hr : Real.sqrt (1 + s ^ 2) ^ 2 = 1 + s ^ 2 := Real.sq_sqrt (by positivity)
    have hr0 : Real.sqrt (1 + s ^ 2) ≠ 0 := (Real.sqrt_pos.mpr (by positivity)).ne'
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;>
      (field_simp; nlinarith [hr])
  inv_val := by
    have hr : Real.sqrt (1 + s ^ 2) ^ 2 = 1 + s ^ 2 := Real.sq_sqrt (by positivity)
    have hr0 : Real.sqrt (1 + s ^ 2) ≠ 0 := (Real.sqrt_pos.mpr (by positivity)).ne'
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;>
      (field_simp; nlinarith [hr])

private theorem rotK_coe (s : ℝ) :
    (rotK s : Matrix (Fin 2) (Fin 2) ℝ)
      = !![(Real.sqrt (1 + s ^ 2))⁻¹, -(s * (Real.sqrt (1 + s ^ 2))⁻¹);
          s * (Real.sqrt (1 + s ^ 2))⁻¹, (Real.sqrt (1 + s ^ 2))⁻¹] :=
  rfl

private theorem rotK_mem (s : ℝ) : rotK s ∈ rowIsometrySubgroup₀ ℝ := by
  have hr : Real.sqrt (1 + s ^ 2) ^ 2 = 1 + s ^ 2 := Real.sq_sqrt (by positivity)
  have hr0 : Real.sqrt (1 + s ^ 2) ≠ 0 := (Real.sqrt_pos.mpr (by positivity)).ne'
  have hdet : (rotK s : Matrix (Fin 2) (Fin 2) ℝ).det = 1 := by
    rw [rotK_coe, Matrix.det_fin_two_of]
    field_simp
    nlinarith [hr]
  rw [mem_rowIsometrySubgroup₀_iff]
  refine ⟨hdet, ?_, ?_⟩
  · rw [hdet, norm_one]
  · intro x y
    simp only [rotK_coe, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one, Real.norm_eq_abs, sq_abs]
    field_simp
    nlinarith [hr]

private theorem firstRowℂ_rotK (s : ℝ) :
    firstRowℂ (rotK s) = ⟨(Real.sqrt (1 + s ^ 2))⁻¹, -(s * (Real.sqrt (1 + s ^ 2))⁻¹)⟩ :=
  rfl

private theorem hasDerivAt_one_add_sq_zero : HasDerivAt (fun s : ℝ => 1 + s ^ 2) 0 0 := by
  simpa using ((hasDerivAt_pow 2 (0 : ℝ)).const_add 1)

private theorem hasDerivAt_inv_sqrt_zero : HasDerivAt (fun s : ℝ => (Real.sqrt (1 + s ^ 2))⁻¹) 0 0 := by
  have h1 : HasDerivAt (fun s : ℝ => Real.sqrt (1 + s ^ 2)) (1 / (2 * Real.sqrt (1 + (0 : ℝ) ^ 2)) * 0) 0 :=
    (Real.hasDerivAt_sqrt (x := 1 + (0 : ℝ) ^ 2) (by norm_num)).comp (0 : ℝ) hasDerivAt_one_add_sq_zero
  have h2 := h1.inv (by simp)
  simpa [Pi.inv_def] using h2

private theorem rotK_zero : rotK 0 = 1 := by
  apply Units.ext
  rw [rotK_coe, Units.val_one]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

private theorem hasDerivAt_flow_curve {w : InfinitePlace K} {hw : w.IsReal} {φ : AdelicGL2 (𝓞 K) K → ℂ}
    (hφ : IsArchSmoothAt hw φ) (d : ArchDir) (g : AdelicGL2 (𝓞 K) K) :
    HasDerivAt (fun t : ℝ => φ (g * archFlowAt hw d t)) (archDerivAt hw d φ g) 0 := by
  have hopen := isOpen_setOf_det_ne_zero
  have hfun : (fun t : ℝ => φ (g * archFlowAt hw d t))
      = fun t : ℝ => (fun e : Fin 2 → Fin 2 → ℝ => φ (g * archRealLiftAt hw e))
          (Matrix.of.symm (((1⁻¹ * archFlowMatrix d t * 1 : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ))) := by
    funext t
    show φ (g * archFlowAt hw d t) = φ (g * archRealLiftAt hw
      (Matrix.of.symm (((1⁻¹ * archFlowMatrix d t * 1 : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ))))
    rw [← archRealGLAt_eq_archRealLiftAt hw, inv_one, one_mul, mul_one, archFlowAt]
  have hdiff : HasFDerivAt (fun e : Fin 2 → Fin 2 → ℝ => φ (g * archRealLiftAt hw e))
      (fderiv ℝ (fun e : Fin 2 → Fin 2 → ℝ => φ (g * archRealLiftAt hw e)) (Matrix.of.symm 1))
      (Matrix.of.symm (((1⁻¹ * archFlowMatrix d 0 * 1 : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ))) := by
    rw [archFlowMatrix_zero, inv_one, one_mul, mul_one, Units.val_one]
    exact (((hφ g).contDiffAt (hopen.mem_nhds det_of_symm_one)).differentiableAt (by simp)).hasFDerivAt
  have h := hdiff.comp_hasDerivAt (0 : ℝ) (hasDerivAt_conj_flow 1 d)
  rw [archDerivAt_eq_fderiv hφ d g]
  have hdir : Matrix.of.symm (((1⁻¹ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) * archDirMatrix d
      * ((1 : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)) = Matrix.of.symm (archDirMatrix d) := by
    simp
  rw [hfun]
  rw [hdir] at h
  exact h

private theorem hasDerivAt_flow_curve_at {w : InfinitePlace K} {hw : w.IsReal} {φ : AdelicGL2 (𝓞 K) K → ℂ}
    (hφ : IsArchSmoothAt hw φ) (d : ArchDir) (g : AdelicGL2 (𝓞 K) K) (s : ℝ) :
    HasDerivAt (fun t : ℝ => φ (g * archFlowAt hw d t)) (archDerivAt hw d φ (g * archFlowAt hw d s)) s := by
  have h := hasDerivAt_flow_curve hφ d (g * archFlowAt hw d s)
  have hshift : (fun t : ℝ => φ (g * archFlowAt hw d t))
      = fun t : ℝ => φ (g * archFlowAt hw d s * archFlowAt hw d (t - s)) := by
    funext t
    rw [mul_assoc, ← archFlowAt_add, add_sub_cancel]
  rw [hshift]
  have h' : HasDerivAt (fun u : ℝ => φ (g * archFlowAt hw d s * archFlowAt hw d u))
      (archDerivAt hw d φ (g * archFlowAt hw d s)) (s - s) := by
    rw [sub_self]
    exact h
  exact h'.comp_sub_const s s

private theorem apply_mul_archFlowAt_of_archDerivAt_eq_zero {w : InfinitePlace K} {hw : w.IsReal}
    {φ : AdelicGL2 (𝓞 K) K → ℂ} (hφ : IsArchSmoothAt hw φ) (d : ArchDir) (h0 : archDerivAt hw d φ = 0)
    (g : AdelicGL2 (𝓞 K) K) (t : ℝ) : φ (g * archFlowAt hw d t) = φ g := by
  have hdiff : Differentiable ℝ fun t : ℝ => φ (g * archFlowAt hw d t) := fun s =>
    (hasDerivAt_flow_curve_at hφ d g s).differentiableAt
  have hder : ∀ s : ℝ, deriv (fun t : ℝ => φ (g * archFlowAt hw d t)) s = 0 := fun s => by
    rw [(hasDerivAt_flow_curve_at hφ d g s).deriv, h0]
    rfl
  have hc := is_const_of_deriv_eq_zero hdiff hder t 0
  simpa only [archFlowAt_zero, mul_one] using hc

private def _root_.ArchExclusion.HasRealWeight {w : InfinitePlace K} (hw : w.IsReal) (m : ℤ) (ψ : AdelicGL2 (𝓞 K) K → ℂ) : Prop :=
  ∀ (k : rowIsometrySubgroup₀ ℝ) (x : AdelicGL2 (𝓞 K) K),
    ψ (x * archRealGLAt hw (k : GL (Fin 2) ℝ)) = firstRowℂ (k : GL (Fin 2) ℝ) ^ m * ψ x

p2m_export "ArchExclusion" "HasRealWeight"
private theorem hasDerivAt_mul_inv_sqrt_zero : HasDerivAt (fun s : ℝ => s * (Real.sqrt (1 + s ^ 2))⁻¹) 1 0 := by
  have h := (hasDerivAt_id (0 : ℝ)).fun_mul hasDerivAt_inv_sqrt_zero
  simpa using h

private theorem hasDerivAt_rotK_chart :
    HasDerivAt (fun s : ℝ => (Matrix.of.symm ((rotK s : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) : Fin 2 → Fin 2 → ℝ))
      (Matrix.of.symm (archDirMatrix .Fm) - Matrix.of.symm (archDirMatrix .E)) 0 := by
  rw [hasDerivAt_pi]
  intro i
  rw [hasDerivAt_pi]
  intro j
  fin_cases i <;> fin_cases j <;>
    simp only [rotK_coe, archDirMatrix, Matrix.of_symm_apply, Pi.sub_apply, Matrix.of_apply, Matrix.cons_val',
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one, Fin.zero_eta,
      Fin.mk_one, Fin.isValue, sub_zero, zero_sub, sub_self]
  · exact hasDerivAt_inv_sqrt_zero
  · simpa [Pi.neg_def] using hasDerivAt_mul_inv_sqrt_zero.neg
  · exact hasDerivAt_mul_inv_sqrt_zero
  · exact hasDerivAt_inv_sqrt_zero

private theorem archDerivAt_E_eq_Fm_of_hasRealWeight_zero {w : InfinitePlace K} {hw : w.IsReal}
    {φ : AdelicGL2 (𝓞 K) K → ℂ} (hφ : IsArchSmoothAt hw φ) (h0 : HasRealWeight hw 0 φ) :
    archDerivAt hw .E φ = archDerivAt hw .Fm φ := by
  funext g
  have hopen := isOpen_setOf_det_ne_zero

  have hconst : (fun s : ℝ => φ (g * archRealLiftAt hw (Matrix.of.symm ((rotK s : GL (Fin 2) ℝ) :
      Matrix (Fin 2) (Fin 2) ℝ)))) = fun _ => φ g := by
    funext s
    rw [← archRealGLAt_eq_archRealLiftAt hw, h0 ⟨rotK s, rotK_mem s⟩ g, zpow_zero, one_mul]
  have hdiff : HasFDerivAt (fun e : Fin 2 → Fin 2 → ℝ => φ (g * archRealLiftAt hw e))
      (fderiv ℝ (fun e : Fin 2 → Fin 2 → ℝ => φ (g * archRealLiftAt hw e)) (Matrix.of.symm 1))
      (Matrix.of.symm ((rotK 0 : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)) := by
    rw [rotK_zero, Units.val_one]
    exact (((hφ g).contDiffAt (hopen.mem_nhds det_of_symm_one)).differentiableAt (by simp)).hasFDerivAt
  have hchain := hdiff.comp_hasDerivAt (0 : ℝ) hasDerivAt_rotK_chart
  simp only [Function.comp_def] at hchain
  rw [hconst] at hchain
  have hzero := (hasDerivAt_const (0 : ℝ) (φ g)).unique hchain
  rw [map_sub] at hzero
  rw [archDerivAt_eq_fderiv hφ .E g, archDerivAt_eq_fderiv hφ .Fm g]
  exact (sub_eq_zero.mp hzero.symm).symm

private def rotOf (c d : ℝ) (h : c ^ 2 + d ^ 2 ≠ 0) : GL (Fin 2) ℝ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero
    !![d / Real.sqrt (c ^ 2 + d ^ 2), -(c / Real.sqrt (c ^ 2 + d ^ 2));
       c / Real.sqrt (c ^ 2 + d ^ 2), d / Real.sqrt (c ^ 2 + d ^ 2)] (by
      have hpos : 0 < c ^ 2 + d ^ 2 := lt_of_le_of_ne (by positivity) (Ne.symm h)
      have hr : Real.sqrt (c ^ 2 + d ^ 2) ^ 2 = c ^ 2 + d ^ 2 := Real.sq_sqrt hpos.le
      have hr0 : Real.sqrt (c ^ 2 + d ^ 2) ≠ 0 := (Real.sqrt_pos.mpr hpos).ne'
      rw [Matrix.det_fin_two_of]
      have hone : d / Real.sqrt (c ^ 2 + d ^ 2) * (d / Real.sqrt (c ^ 2 + d ^ 2))
          - -(c / Real.sqrt (c ^ 2 + d ^ 2)) * (c / Real.sqrt (c ^ 2 + d ^ 2)) = 1 := by
        field_simp
        nlinarith [hr]
      rw [hone]
      exact one_ne_zero)

private theorem rotOf_coe (c d : ℝ) (h : c ^ 2 + d ^ 2 ≠ 0) :
    (rotOf c d h : Matrix (Fin 2) (Fin 2) ℝ)
      = !![d / Real.sqrt (c ^ 2 + d ^ 2), -(c / Real.sqrt (c ^ 2 + d ^ 2));
           c / Real.sqrt (c ^ 2 + d ^ 2), d / Real.sqrt (c ^ 2 + d ^ 2)] :=
  rfl

private theorem rotOf_mem (c d : ℝ) (h : c ^ 2 + d ^ 2 ≠ 0) : rotOf c d h ∈ rowIsometrySubgroup₀ ℝ := by
  have hpos : 0 < c ^ 2 + d ^ 2 := lt_of_le_of_ne (by positivity) (Ne.symm h)
  have hr : Real.sqrt (c ^ 2 + d ^ 2) ^ 2 = c ^ 2 + d ^ 2 := Real.sq_sqrt hpos.le
  have hr0 : Real.sqrt (c ^ 2 + d ^ 2) ≠ 0 := (Real.sqrt_pos.mpr hpos).ne'
  have hdet : (rotOf c d h : Matrix (Fin 2) (Fin 2) ℝ).det = 1 := by
    rw [rotOf_coe, Matrix.det_fin_two_of]
    field_simp
    nlinarith [hr]
  rw [mem_rowIsometrySubgroup₀_iff]
  refine ⟨hdet, ?_, ?_⟩
  · rw [hdet, norm_one]
  · intro x y
    simp only [rotOf_coe, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one, Real.norm_eq_abs, sq_abs]
    field_simp
    nlinarith [hr]

private theorem exists_iwasawa (m : GL (Fin 2) ℝ) (hm : (m : Matrix (Fin 2) (Fin 2) ℝ).det = 1) :
    ∃ (x t : ℝ) (k : rowIsometrySubgroup₀ ℝ),
      m = archFlowMatrix .E x * archFlowMatrix .H t * (k : GL (Fin 2) ℝ) := by
  set a := (m : Matrix (Fin 2) (Fin 2) ℝ) 0 0 with ha
  set b := (m : Matrix (Fin 2) (Fin 2) ℝ) 0 1 with hb
  set c := (m : Matrix (Fin 2) (Fin 2) ℝ) 1 0 with hc
  set dd := (m : Matrix (Fin 2) (Fin 2) ℝ) 1 1 with hdd
  have hdet : a * dd - b * c = 1 := by rw [← hm, Matrix.det_fin_two]
  have hcd : c ^ 2 + dd ^ 2 ≠ 0 := by
    intro h0
    have hc0 : c = 0 := by nlinarith [sq_nonneg c, sq_nonneg dd]
    have hd0 : dd = 0 := by nlinarith [sq_nonneg c, sq_nonneg dd]
    rw [hc0, hd0] at hdet
    simp at hdet
  have hpos : 0 < c ^ 2 + dd ^ 2 := lt_of_le_of_ne (by positivity) (Ne.symm hcd)
  set r := Real.sqrt (c ^ 2 + dd ^ 2) with hr_def
  have hr : r ^ 2 = c ^ 2 + dd ^ 2 := Real.sq_sqrt hpos.le
  have hrpos : 0 < r := Real.sqrt_pos.mpr hpos
  have hr0 : r ≠ 0 := hrpos.ne'
  refine ⟨(a * c + b * dd) / (c ^ 2 + dd ^ 2), -Real.log r, ⟨rotOf c dd hcd, rotOf_mem c dd hcd⟩, ?_⟩
  have hexp : Real.exp (-Real.log r) = r⁻¹ := by rw [Real.exp_neg, Real.exp_log hrpos]
  have hexp' : Real.exp (-(-Real.log r)) = r := by rw [neg_neg, Real.exp_log hrpos]
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j
  · simp only [archFlowMatrix, Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two, unipotentGL2_coe, splitTorusGL2_coe,
      rotOf_coe, hexp, hexp', Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one, Fin.zero_eta, Fin.isValue]
    rw [← hr_def] at *
    field_simp
    linear_combination (dd * (a * dd - b * c)) * hr + (dd * (c ^ 2 + dd ^ 2)) * hdet
  · simp only [archFlowMatrix, Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two, unipotentGL2_coe, splitTorusGL2_coe,
      rotOf_coe, hexp, hexp', Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one, Fin.zero_eta, Fin.mk_one, Fin.isValue]
    rw [← hr_def] at *
    field_simp
    linear_combination (-c * (a * dd - b * c)) * hr + (-c * (c ^ 2 + dd ^ 2)) * hdet
  · simp only [archFlowMatrix, Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two, unipotentGL2_coe, splitTorusGL2_coe,
      rotOf_coe, hexp, hexp', Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one, Fin.zero_eta, Fin.mk_one, Fin.isValue]
    rw [← hr_def] at *
    field_simp
    ring
  · simp only [archFlowMatrix, Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two, unipotentGL2_coe, splitTorusGL2_coe,
      rotOf_coe, hexp, hexp', Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one, Fin.mk_one, Fin.isValue]
    rw [← hr_def] at *
    field_simp
    ring

private theorem archDerivAt_H_eq_zero_and_E_eq_zero {w : InfinitePlace K} {hw : w.IsReal}
    {φ : AdelicGL2 (𝓞 K) K → ℂ} (hφ : IsArchSmoothAt hw φ) (h0 : HasRealWeight hw 0 φ)
    (hlow : archDerivAt hw .H φ - Complex.I • (archDerivAt hw .E φ + archDerivAt hw .Fm φ) = 0)
    (hraise : archDerivAt hw .H φ + Complex.I • (archDerivAt hw .E φ + archDerivAt hw .Fm φ) = 0) :
    archDerivAt hw .H φ = 0 ∧ archDerivAt hw .E φ = 0 := by
  have hEF := archDerivAt_E_eq_Fm_of_hasRealWeight_zero hφ h0
  constructor
  · funext g
    have h1 := congrFun hlow g
    have h2 := congrFun hraise g
    simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at h1 h2 ⊢
    linear_combination (1 / 2 : ℂ) * h1 + (1 / 2 : ℂ) * h2
  · funext g
    have h1 := congrFun hlow g
    have h2 := congrFun hraise g
    have h3 := congrFun hEF g
    simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at h1 h2 h3 ⊢

    have h4 : archDerivAt hw .E φ g + archDerivAt hw .Fm φ g = 0 := by
      have h5 : Complex.I * (archDerivAt hw .E φ g + archDerivAt hw .Fm φ g) = 0 := by
        linear_combination (1 / 2 : ℂ) * h2 - (1 / 2 : ℂ) * h1
      exact (mul_eq_zero.mp h5).resolve_left Complex.I_ne_zero
    linear_combination (1 / 2 : ℂ) * h4 + (1 / 2 : ℂ) * h3

private theorem apply_mul_archRealGLAt_of_det_one {w : InfinitePlace K} {hw : w.IsReal}
    {φ : AdelicGL2 (𝓞 K) K → ℂ} (hφ : IsArchSmoothAt hw φ) (h0 : HasRealWeight hw 0 φ)
    (hlow : archDerivAt hw .H φ - Complex.I • (archDerivAt hw .E φ + archDerivAt hw .Fm φ) = 0)
    (hraise : archDerivAt hw .H φ + Complex.I • (archDerivAt hw .E φ + archDerivAt hw .Fm φ) = 0)
    (m : GL (Fin 2) ℝ) (hm : (m : Matrix (Fin 2) (Fin 2) ℝ).det = 1) (g : AdelicGL2 (𝓞 K) K) :
    φ (g * archRealGLAt hw m) = φ g := by
  obtain ⟨hH, hE⟩ := archDerivAt_H_eq_zero_and_E_eq_zero hφ h0 hlow hraise
  obtain ⟨x, t, k, rfl⟩ := exists_iwasawa m hm
  rw [map_mul, map_mul, ← mul_assoc, h0 k, zpow_zero, one_mul, ← mul_assoc]
  show φ (g * archFlowAt hw .E x * archFlowAt hw .H t) = φ g
  rw [apply_mul_archFlowAt_of_archDerivAt_eq_zero hφ .H hH, apply_mul_archFlowAt_of_archDerivAt_eq_zero hφ .E hE]

end ArchExclusion

namespace AdelicExclusion

open IsDedekindDomain NumberField MeasureTheory Matrix
open NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
p2m_open "AutomorphicForm~continuous_unipotentGL2~isIsotypicCuspFormAt_of_mem_isotypicCuspSubmodule NumberField.InfinitePlace.Completion"
open scoped ProbabilityTheory

local notation "𝔸" => AdeleRing (𝓞 ℚ) ℚ
local notation "𝔸f" => FiniteAdeleRing (𝓞 ℚ) ℚ
local notation "G𝔸" => AdelicGL2 (𝓞 ℚ) ℚ

private theorem det_glFin_eq_one {s : G𝔸} (hs : (s : Matrix (Fin 2) (Fin 2) 𝔸).det = 1) :
    ((glFin (𝓞 ℚ) ℚ s : GL (Fin 2) 𝔸f) : Matrix (Fin 2) (Fin 2) 𝔸f).det = 1 := by
  have h : ((glFin (𝓞 ℚ) ℚ s : GL (Fin 2) 𝔸f) : Matrix (Fin 2) (Fin 2) 𝔸f)
      = (adeleFin (𝓞 ℚ) ℚ).mapMatrix (s : Matrix (Fin 2) (Fin 2) 𝔸) := by
    ext i j
    rfl
  rw [h, ← RingHom.map_det, hs, map_one]

private theorem glFin_globalPoints_toGL (γ : Matrix.SpecialLinearGroup (Fin 2) ℚ) :
    ((glFin (𝓞 ℚ) ℚ (globalPoints (𝓞 ℚ) ℚ (Matrix.SpecialLinearGroup.toGL γ)) : GL (Fin 2) 𝔸f) :
        Matrix (Fin 2) (Fin 2) 𝔸f)
      = ((Matrix.SpecialLinearGroup.map (n := Fin 2) (algebraMap ℚ 𝔸f) γ : Matrix.SpecialLinearGroup (Fin 2) 𝔸f) :
          Matrix (Fin 2) (Fin 2) 𝔸f) := by
  ext i j
  rfl

private theorem det_globalPoints_toGL (γ : Matrix.SpecialLinearGroup (Fin 2) ℚ) :
    ((globalPoints (𝓞 ℚ) ℚ (Matrix.SpecialLinearGroup.toGL γ) : G𝔸) : Matrix (Fin 2) (Fin 2) 𝔸).det = 1 := by
  have h : ((globalPoints (𝓞 ℚ) ℚ (Matrix.SpecialLinearGroup.toGL γ) : G𝔸) : Matrix (Fin 2) (Fin 2) 𝔸)
      = (algebraMap ℚ 𝔸).mapMatrix (γ : Matrix (Fin 2) (Fin 2) ℚ) := by
    ext i j
    rfl
  rw [h, ← RingHom.map_det, Matrix.SpecialLinearGroup.det_coe, map_one]

private theorem coe_inv_eq_adjugate {R : Type} [CommRing R] {u : GL (Fin 2) R}
    (hu : (u : Matrix (Fin 2) (Fin 2) R).det = 1) :
    ((u⁻¹ : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) = (u : Matrix (Fin 2) (Fin 2) R).adjugate := by
  rw [Matrix.coe_units_inv, Matrix.inv_def, hu, Ring.inverse_one, one_smul]

private theorem archGLIncl_archComponent (w : InfinitePlace ℚ) (k : GL (Fin 2) (InfiniteAdeleRing ℚ)) :
    archGLIncl ℚ w (archComponent ℚ w k) = k := by
  apply Units.ext
  ext i j
  funext w'
  obtain rfl : w' = w := Subsingleton.elim w' w
  exact archMatrixUpdate_apply_self ℚ w' _ i j

private theorem glArch_archRealGLAt_archRealProjAt {w : InfinitePlace ℚ} (hw : w.IsReal) (r : G𝔸) :
    glArch (𝓞 ℚ) ℚ (archRealGLAt hw (archRealProjAt hw r)) = glArch (𝓞 ℚ) ℚ r := by
  have h1 : glArch (𝓞 ℚ) ℚ (archRealGLAt hw (archRealProjAt hw r))
      = archGLIncl ℚ w
          (glEquivOfRingEquiv (ringEquivRealOfIsReal hw).symm (archRealProjAt hw r)) :=
    glArch_adelicArchGLIncl ℚ _
  rw [h1]
  have h2 : glEquivOfRingEquiv (ringEquivRealOfIsReal hw).symm (archRealProjAt hw r)
      = archComponent ℚ w (glArch (𝓞 ℚ) ℚ r) := by
    show glEquivOfRingEquiv (ringEquivRealOfIsReal hw).symm
      (glEquivOfRingEquiv (ringEquivRealOfIsReal hw) (archComponent ℚ w (glArch (𝓞 ℚ) ℚ r))) = _
    apply Units.ext
    ext i j : 1
    rw [glEquivOfRingEquiv_apply_entry, glEquivOfRingEquiv_apply_entry]
    exact (ringEquivRealOfIsReal hw).symm_apply_apply _
  rw [h2, archGLIncl_archComponent]

private theorem glFin_archRealGLAt {w : InfinitePlace ℚ} (hw : w.IsReal) (m : GL (Fin 2) ℝ) :
    glFin (𝓞 ℚ) ℚ (archRealGLAt hw m) = 1 :=
  glFin_adelicArchGLIncl ℚ _

private theorem det_archRealProjAt {w : InfinitePlace ℚ} (hw : w.IsReal) {r : G𝔸}
    (hr : (r : Matrix (Fin 2) (Fin 2) 𝔸).det = 1) :
    ((archRealProjAt hw r : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ).det = 1 := by
  have h : ((archRealProjAt hw r : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)
      = ((ringEquivRealOfIsReal hw).toRingHom.comp ((archEval ℚ w).comp (adeleArch (𝓞 ℚ) ℚ))).mapMatrix
          (r : Matrix (Fin 2) (Fin 2) 𝔸) := by
    ext i j
    rfl
  rw [h, ← RingHom.map_det, hr, map_one]

private theorem exists_eq_archRealGLAt_mul {w : InfinitePlace ℚ} (hw : w.IsReal) (r : G𝔸) :
    ∃ u : G𝔸, r = archRealGLAt hw (archRealProjAt hw r) * u ∧ glArch (𝓞 ℚ) ℚ u = 1 ∧
      glFin (𝓞 ℚ) ℚ u = glFin (𝓞 ℚ) ℚ r := by
  refine ⟨(archRealGLAt hw (archRealProjAt hw r))⁻¹ * r, by rw [mul_inv_cancel_left], ?_, ?_⟩
  · rw [map_mul, map_inv, glArch_archRealGLAt_archRealProjAt, inv_mul_cancel]
  · rw [map_mul, map_inv, glFin_archRealGLAt, inv_one, one_mul]

private theorem isLevelOneMatrix_one (N : Ideal (𝓞 ℚ)) : IsLevelOneMatrix (𝓞 ℚ) ℚ N (1 : Matrix (Fin 2) (Fin 2) 𝔸f) :=
  ((mem_finiteLevelOne_iff (N := N)).mp (one_mem (finiteLevelOne (𝓞 ℚ) ℚ N))).1

private theorem apply_mul_eq_of_det_eq_one {w : InfinitePlace ℚ} (hw : w.IsReal) (φ : G𝔸 → ℂ)
    (hleft : ∀ (γ : GL (Fin 2) ℚ) (x : G𝔸), φ (globalPoints (𝓞 ℚ) ℚ γ * x) = φ x)
    (N : Ideal (𝓞 ℚ)) (hN : N ≠ ⊥)
    (hlev : ∀ x : G𝔸, ∀ u ∈ levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ, φ (x * u) = φ x)
    (harch : ∀ m : GL (Fin 2) ℝ, (m : Matrix (Fin 2) (Fin 2) ℝ).det = 1 → ∀ x : G𝔸, φ (x * archRealGLAt hw m) = φ x)
    (x s : G𝔸) (hs : (s : Matrix (Fin 2) (Fin 2) 𝔸).det = 1) : φ (x * s) = φ x := by
  set xf : GL (Fin 2) 𝔸f := glFin (𝓞 ℚ) ℚ x with hxf
  set sf : GL (Fin 2) 𝔸f := glFin (𝓞 ℚ) ℚ s with hsf
  have hsf1 : (sf : Matrix (Fin 2) (Fin 2) 𝔸f).det = 1 := det_glFin_eq_one hs

  let Fm : Matrix.SpecialLinearGroup (Fin 2) 𝔸f → Matrix (Fin 2) (Fin 2) 𝔸f × Matrix (Fin 2) (Fin 2) 𝔸f :=
    fun y => (((xf⁻¹ : GL (Fin 2) 𝔸f) : Matrix (Fin 2) (Fin 2) 𝔸f) * (y : Matrix (Fin 2) (Fin 2) 𝔸f).adjugate
        * (xf : Matrix (Fin 2) (Fin 2) 𝔸f) * (sf : Matrix (Fin 2) (Fin 2) 𝔸f),
      ((sf⁻¹ : GL (Fin 2) 𝔸f) : Matrix (Fin 2) (Fin 2) 𝔸f) * ((xf⁻¹ : GL (Fin 2) 𝔸f) : Matrix (Fin 2) (Fin 2) 𝔸f)
        * (y : Matrix (Fin 2) (Fin 2) 𝔸f) * (xf : Matrix (Fin 2) (Fin 2) 𝔸f))
  have hFm : Continuous Fm := by
    have hy : Continuous fun y : Matrix.SpecialLinearGroup (Fin 2) 𝔸f => (y : Matrix (Fin 2) (Fin 2) 𝔸f) :=
      continuous_subtype_val
    refine Continuous.prodMk ?_ ?_
    · exact ((continuous_const.matrix_mul hy.matrix_adjugate).matrix_mul continuous_const).matrix_mul continuous_const
    · exact ((continuous_const.matrix_mul continuous_const).matrix_mul hy).matrix_mul continuous_const
  set O : Set (Matrix.SpecialLinearGroup (Fin 2) 𝔸f) :=
    Fm ⁻¹' ({m | IsLevelOneMatrix (𝓞 ℚ) ℚ N m} ×ˢ {m | IsLevelOneMatrix (𝓞 ℚ) ℚ N m}) with hO
  have hOopen : IsOpen O :=
    hFm.isOpen_preimage _
      ((isOpen_setOf_isLevelOneMatrix (𝓞 ℚ) ℚ hN).prod (isOpen_setOf_isLevelOneMatrix (𝓞 ℚ) ℚ hN))

  have hu₀det : ((xf * sf * xf⁻¹ : GL (Fin 2) 𝔸f) : Matrix (Fin 2) (Fin 2) 𝔸f).det = 1 := by
    simp only [Units.val_mul, Matrix.det_mul, hsf1, mul_one]
    rw [← Matrix.det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.det_one]
  set y₀ : Matrix.SpecialLinearGroup (Fin 2) 𝔸f :=
    ⟨((xf * sf * xf⁻¹ : GL (Fin 2) 𝔸f) : Matrix (Fin 2) (Fin 2) 𝔸f), hu₀det⟩ with hy₀
  have hy₀O : y₀ ∈ O := by
    have hadj : (y₀ : Matrix (Fin 2) (Fin 2) 𝔸f).adjugate
        = (((xf * sf * xf⁻¹)⁻¹ : GL (Fin 2) 𝔸f) : Matrix (Fin 2) (Fin 2) 𝔸f) := (coe_inv_eq_adjugate hu₀det).symm
    have h1 : (Fm y₀).1 = 1 := by
      show ((xf⁻¹ : GL (Fin 2) 𝔸f) : Matrix (Fin 2) (Fin 2) 𝔸f) * (y₀ : Matrix (Fin 2) (Fin 2) 𝔸f).adjugate
        * (xf : Matrix (Fin 2) (Fin 2) 𝔸f) * (sf : Matrix (Fin 2) (Fin 2) 𝔸f) = 1
      rw [hadj, ← Units.val_mul, ← Units.val_mul, ← Units.val_mul]
      rw [show xf⁻¹ * (xf * sf * xf⁻¹)⁻¹ * xf * sf = 1 by group, Units.val_one]
    have h2 : (Fm y₀).2 = 1 := by
      show ((sf⁻¹ : GL (Fin 2) 𝔸f) : Matrix (Fin 2) (Fin 2) 𝔸f) * ((xf⁻¹ : GL (Fin 2) 𝔸f) : Matrix (Fin 2) (Fin 2) 𝔸f)
        * (y₀ : Matrix (Fin 2) (Fin 2) 𝔸f) * (xf : Matrix (Fin 2) (Fin 2) 𝔸f) = 1
      show ((sf⁻¹ : GL (Fin 2) 𝔸f) : Matrix (Fin 2) (Fin 2) 𝔸f) * ((xf⁻¹ : GL (Fin 2) 𝔸f) : Matrix (Fin 2) (Fin 2) 𝔸f)
        * ((xf * sf * xf⁻¹ : GL (Fin 2) 𝔸f) : Matrix (Fin 2) (Fin 2) 𝔸f) * (xf : Matrix (Fin 2) (Fin 2) 𝔸f) = 1
      rw [← Units.val_mul, ← Units.val_mul, ← Units.val_mul]
      rw [show sf⁻¹ * xf⁻¹ * (xf * sf * xf⁻¹) * xf = 1 by group, Units.val_one]
    rw [hO, Set.mem_preimage, Set.mem_prod, h1, h2]
    exact ⟨isLevelOneMatrix_one N, isLevelOneMatrix_one N⟩

  obtain ⟨γ, hγ⟩ := (NumberField.denseRange_specialLinearGroup_map_finiteAdeleRing ℚ).exists_mem_open hOopen ⟨y₀, hy₀O⟩
  set Γ : G𝔸 := globalPoints (𝓞 ℚ) ℚ (Matrix.SpecialLinearGroup.toGL γ) with hΓ
  have hΓdet : (Γ : Matrix (Fin 2) (Fin 2) 𝔸).det = 1 := det_globalPoints_toGL γ
  have hΓf : ((glFin (𝓞 ℚ) ℚ Γ : GL (Fin 2) 𝔸f) : Matrix (Fin 2) (Fin 2) 𝔸f)
      = ((Matrix.SpecialLinearGroup.map (n := Fin 2) (algebraMap ℚ 𝔸f) γ : Matrix.SpecialLinearGroup (Fin 2) 𝔸f) :
          Matrix (Fin 2) (Fin 2) 𝔸f) := glFin_globalPoints_toGL γ
  have hΓfdet : ((glFin (𝓞 ℚ) ℚ Γ : GL (Fin 2) 𝔸f) : Matrix (Fin 2) (Fin 2) 𝔸f).det = 1 := det_glFin_eq_one hΓdet

  set r : G𝔸 := x⁻¹ * Γ⁻¹ * x * s with hr
  have hrf : glFin (𝓞 ℚ) ℚ r ∈ finiteLevelOne (𝓞 ℚ) ℚ N := by
    have hγ' : Fm (Matrix.SpecialLinearGroup.map (n := Fin 2) (algebraMap ℚ 𝔸f) γ)
        ∈ {m | IsLevelOneMatrix (𝓞 ℚ) ℚ N m} ×ˢ {m | IsLevelOneMatrix (𝓞 ℚ) ℚ N m} := hγ
    obtain ⟨hγ1, hγ2⟩ := Set.mem_prod.mp hγ'
    rw [mem_finiteLevelOne_iff]
    constructor
    · have h : ((glFin (𝓞 ℚ) ℚ r : GL (Fin 2) 𝔸f) : Matrix (Fin 2) (Fin 2) 𝔸f)
          = (Fm (Matrix.SpecialLinearGroup.map (n := Fin 2) (algebraMap ℚ 𝔸f) γ)).1 := by
        show ((glFin (𝓞 ℚ) ℚ r : GL (Fin 2) 𝔸f) : Matrix (Fin 2) (Fin 2) 𝔸f)
          = ((xf⁻¹ : GL (Fin 2) 𝔸f) : Matrix (Fin 2) (Fin 2) 𝔸f)
            * ((Matrix.SpecialLinearGroup.map (n := Fin 2) (algebraMap ℚ 𝔸f) γ :
                Matrix.SpecialLinearGroup (Fin 2) 𝔸f) : Matrix (Fin 2) (Fin 2) 𝔸f).adjugate
            * (xf : Matrix (Fin 2) (Fin 2) 𝔸f) * (sf : Matrix (Fin 2) (Fin 2) 𝔸f)
        rw [← hΓf, ← coe_inv_eq_adjugate hΓfdet, hr, map_mul, map_mul, map_mul, map_inv, map_inv, Units.val_mul,
          Units.val_mul, Units.val_mul]
      rw [h]
      exact hγ1
    · have h : (((glFin (𝓞 ℚ) ℚ r)⁻¹ : GL (Fin 2) 𝔸f) : Matrix (Fin 2) (Fin 2) 𝔸f)
          = (Fm (Matrix.SpecialLinearGroup.map (n := Fin 2) (algebraMap ℚ 𝔸f) γ)).2 := by
        show (((glFin (𝓞 ℚ) ℚ r)⁻¹ : GL (Fin 2) 𝔸f) : Matrix (Fin 2) (Fin 2) 𝔸f)
          = ((sf⁻¹ : GL (Fin 2) 𝔸f) : Matrix (Fin 2) (Fin 2) 𝔸f) * ((xf⁻¹ : GL (Fin 2) 𝔸f) : Matrix (Fin 2) (Fin 2) 𝔸f)
            * ((Matrix.SpecialLinearGroup.map (n := Fin 2) (algebraMap ℚ 𝔸f) γ :
                Matrix.SpecialLinearGroup (Fin 2) 𝔸f) : Matrix (Fin 2) (Fin 2) 𝔸f)
            * (xf : Matrix (Fin 2) (Fin 2) 𝔸f)
        rw [← hΓf, hr, map_mul, map_mul, map_mul, map_inv, map_inv, ← Units.val_mul, ← Units.val_mul, ← Units.val_mul]
        congr 1
        rw [hxf, hsf]
        group
      rw [h]
      exact hγ2
  have hrdet : (r : Matrix (Fin 2) (Fin 2) 𝔸).det = 1 := by
    have hx : ((x⁻¹ : G𝔸) : Matrix (Fin 2) (Fin 2) 𝔸).det * (x : Matrix (Fin 2) (Fin 2) 𝔸).det = 1 := by
      rw [← Matrix.det_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.det_one]
    have hΓ' : ((Γ⁻¹ : G𝔸) : Matrix (Fin 2) (Fin 2) 𝔸).det = 1 := by
      rw [coe_inv_eq_adjugate hΓdet, Matrix.det_adjugate, hΓdet, one_pow]
    rw [hr, Units.val_mul, Units.val_mul, Units.val_mul, Matrix.det_mul, Matrix.det_mul, Matrix.det_mul, hs, hΓ',
      mul_one, mul_one]
    exact hx

  obtain ⟨u, hru, huarch, huf⟩ := exists_eq_archRealGLAt_mul hw r
  have huU : u ∈ levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ := by
    refine ⟨?_, huarch⟩
    show u ∈ levelOne (𝓞 ℚ) ℚ N
    rw [mem_levelOne_iff, huf]
    exact hrf
  have hxs : x * s = Γ * (x * r) := by
    rw [hr]
    group
  rw [hxs, hleft, hru, ← mul_assoc, hlev _ u huU, harch _ (det_archRealProjAt hw hrdet)]

private theorem det_unipotentGL2 (q : 𝔸) : ((unipotentGL2 q : G𝔸) : Matrix (Fin 2) (Fin 2) 𝔸).det = 1 := by
  rw [unipotentGL2_coe, Matrix.det_fin_two_of]
  ring

private theorem eq_zero_of_isCuspidalFn {w : InfinitePlace ℚ} (hw : w.IsReal) (φ : G𝔸 → ℂ)
    (hleft : ∀ (γ : GL (Fin 2) ℚ) (x : G𝔸), φ (globalPoints (𝓞 ℚ) ℚ γ * x) = φ x)
    (N : Ideal (𝓞 ℚ)) (hN : N ≠ ⊥)
    (hlev : ∀ x : G𝔸, ∀ u ∈ levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ, φ (x * u) = φ x)
    (harch : ∀ m : GL (Fin 2) ℝ, (m : Matrix (Fin 2) (Fin 2) ℝ).det = 1 → ∀ x : G𝔸, φ (x * archRealGLAt hw m) = φ x)
    (hcusp : @IsCuspidalFn _ (adeleBorel (𝓞 ℚ) ℚ) _ _
      (@ProbabilityTheory.cond _ (adeleBorel (𝓞 ℚ) ℚ) (adelicAddHaar (𝓞 ℚ) ℚ) (adelicBox ℚ)) unipotentGL2 φ)
    (g : G𝔸) : φ g = 0 := by
  letI : MeasurableSpace 𝔸 := adeleBorel (𝓞 ℚ) ℚ
  haveI : IsProbabilityMeasure ((adelicAddHaar (𝓞 ℚ) ℚ)[|adelicBox ℚ]) := isProbabilityMeasure_cond_adelicBox ℚ
  have hconst : ∀ q : 𝔸, φ (unipotentGL2 q * g) = φ g := by
    intro q
    have h1 : unipotentGL2 q * g = g * (g⁻¹ * unipotentGL2 q * g) := by group
    have h2 : ((g⁻¹ * unipotentGL2 q * g : G𝔸) : Matrix (Fin 2) (Fin 2) 𝔸).det = 1 := by
      rw [Units.val_mul, Units.val_mul, Matrix.det_mul, Matrix.det_mul, det_unipotentGL2, mul_one, ← Matrix.det_mul,
        ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.det_one]
    rw [h1]
    exact apply_mul_eq_of_det_eq_one hw φ hleft N hN hlev harch g _ h2
  have hct := hcusp g
  unfold constantTerm constantTermIntegrand at hct
  simp only [hconst, integral_const, probReal_univ, one_smul] at hct
  exact hct

end AdelicExclusion

namespace ArchParameter

open LanglandsTunnell

private def Spec (P : RealArchParam) (k₀ : ℤ) (lam u₀ : ℂ) (a j : ZMod 2) (t : ℝ) : Prop :=
  (∀ (u : ℂ) (n : ℕ) (hn : 1 ≤ n), P ≠ RealArchParam.discrete u n hn) ∧
  RealArchParam.laplaceEigenvalue P = lam ∧
  P.centralExponent + 1 = u₀ ∧
  P.centralSign = a ∧
  (∀ (u₁ u₂ : ℂ) (a₁ a₂ : ZMod 2), P = RealArchParam.principal u₁ a₁ u₂ a₂ → |(u₁ - u₂).re| < 1) ∧
  (∀ (u₁ u₂ : ℂ) (a₁ a₂ : ZMod 2), P = RealArchParam.principal u₁ a₁ u₂ a₂ →
    (k₀ = 0 ∨ k₀ = 1) ∧ ((k₀ : ZMod 2) = a₁ + a₂)) ∧
  (∀ (u₁ u₂ : ℂ) (a₁ : ZMod 2), P = RealArchParam.principal u₁ a₁ u₂ a₁ → a₁ = j) ∧
  (∀ (u : ℂ) (a₁ a₂ : ZMod 2), P = RealArchParam.principal u a₁ u a₂ → a₁ ≠ a₂ → t = 0)

private def δ₀ (t : ℝ) : ℂ :=
  if 4 * t ≤ 1 then ((Real.sqrt (1 - 4 * t) : ℝ) : ℂ) else Complex.I * ((Real.sqrt (4 * t - 1) : ℝ) : ℂ)

private theorem δ₀_sq (t : ℝ) : δ₀ t ^ 2 = 1 - 4 * (t : ℂ) := by
  unfold δ₀
  split_ifs with h
  · rw [← Complex.ofReal_pow, Real.sq_sqrt (by linarith)]
    push_cast
    ring
  · rw [mul_pow, Complex.I_sq, ← Complex.ofReal_pow, Real.sq_sqrt (by linarith)]
    push_cast
    ring

private theorem abs_re_δ₀_lt_one {t : ℝ} (ht : 0 < t) : |(δ₀ t).re| < 1 := by
  unfold δ₀
  split_ifs with h
  · rw [Complex.ofReal_re, abs_of_nonneg (Real.sqrt_nonneg _), Real.sqrt_lt' zero_lt_one, one_pow]
    linarith
  · simp

private def δ₁ (t : ℝ) : ℂ := Complex.I * ((2 * Real.sqrt t : ℝ) : ℂ)

private theorem δ₁_sq {t : ℝ} (ht : 0 ≤ t) : δ₁ t ^ 2 = -(4 * (t : ℂ)) := by
  unfold δ₁
  rw [mul_pow, Complex.I_sq, ← Complex.ofReal_pow, mul_pow, Real.sq_sqrt ht]
  push_cast
  ring

private theorem re_δ₁ (t : ℝ) : (δ₁ t).re = 0 := by
  simp [δ₁]

private theorem δ₁_eq_zero {t : ℝ} (ht : 0 ≤ t) (h : δ₁ t = 0) : t = 0 := by
  unfold δ₁ at h
  rcases mul_eq_zero.mp h with h | h
  · exact absurd h Complex.I_ne_zero
  · have h' : (2 * Real.sqrt t : ℝ) = 0 := by exact_mod_cast h
    have : Real.sqrt t = 0 := by linarith
    exact (Real.sqrt_eq_zero ht).mp this

private def param₀ (u₀ : ℂ) (j : ZMod 2) (t : ℝ) : RealArchParam :=
  RealArchParam.principal ((u₀ - 1 + δ₀ t) / 2) j ((u₀ - 1 - δ₀ t) / 2) j

private def param₁ (u₀ : ℂ) (t : ℝ) : RealArchParam :=
  RealArchParam.principal ((u₀ - 1 + δ₁ t) / 2) 0 ((u₀ - 1 - δ₁ t) / 2) 1

private theorem add_self_zmod_two (j : ZMod 2) : j + j = 0 := by
  revert j
  decide

private theorem spec_param₀ (u₀ : ℂ) (j : ZMod 2) {t : ℝ} (ht : 0 < t) {lam : ℂ} (hlam : lam = t) {a : ZMod 2}
    (ha : a = 0) : Spec (param₀ u₀ j t) 0 lam u₀ a j t := by
  refine ⟨fun u n hn h => RealArchParam.noConfusion h, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hlam]
    show 1 / 4 - (((u₀ - 1 + δ₀ t) / 2 - (u₀ - 1 - δ₀ t) / 2) / 2) ^ 2 = (t : ℂ)
    have h : ((u₀ - 1 + δ₀ t) / 2 - (u₀ - 1 - δ₀ t) / 2) / 2 = δ₀ t / 2 := by ring
    rw [h, div_pow, δ₀_sq]
    ring
  · show (u₀ - 1 + δ₀ t) / 2 + (u₀ - 1 - δ₀ t) / 2 + 1 = u₀
    ring
  · show j + j = a
    rw [add_self_zmod_two, ha]
  · intro u₁ u₂ a₁ a₂ h
    simp only [param₀, RealArchParam.principal.injEq] at h
    obtain ⟨rfl, -, rfl, -⟩ := h
    have hd : (u₀ - 1 + δ₀ t) / 2 - (u₀ - 1 - δ₀ t) / 2 = δ₀ t := by ring
    rw [hd]
    exact abs_re_δ₀_lt_one ht
  · intro u₁ u₂ a₁ a₂ h
    simp only [param₀, RealArchParam.principal.injEq] at h
    obtain ⟨-, rfl, -, rfl⟩ := h
    exact ⟨Or.inl rfl, by rw [add_self_zmod_two]; simp⟩
  · intro u₁ u₂ a₁ h
    simp only [param₀, RealArchParam.principal.injEq] at h
    exact h.2.1.symm
  · intro u a₁ a₂ h hne
    simp only [param₀, RealArchParam.principal.injEq] at h
    exact absurd (h.2.1.symm.trans h.2.2.2) hne

private theorem spec_param₁ (u₀ : ℂ) (j : ZMod 2) {t : ℝ} (ht : 0 ≤ t) {lam : ℂ} (hlam : lam = 1 / 4 + t)
    {a : ZMod 2} (ha : a = 1) : Spec (param₁ u₀ t) 1 lam u₀ a j t := by
  refine ⟨fun u n hn h => RealArchParam.noConfusion h, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hlam]
    show 1 / 4 - (((u₀ - 1 + δ₁ t) / 2 - (u₀ - 1 - δ₁ t) / 2) / 2) ^ 2 = 1 / 4 + (t : ℂ)
    have h : ((u₀ - 1 + δ₁ t) / 2 - (u₀ - 1 - δ₁ t) / 2) / 2 = δ₁ t / 2 := by ring
    rw [h, div_pow, δ₁_sq ht]
    ring
  · show (u₀ - 1 + δ₁ t) / 2 + (u₀ - 1 - δ₁ t) / 2 + 1 = u₀
    ring
  · show (0 : ZMod 2) + 1 = a
    rw [ha, zero_add]
  · intro u₁ u₂ a₁ a₂ h
    simp only [param₁, RealArchParam.principal.injEq] at h
    obtain ⟨rfl, -, rfl, -⟩ := h
    have hd : (u₀ - 1 + δ₁ t) / 2 - (u₀ - 1 - δ₁ t) / 2 = δ₁ t := by ring
    rw [hd, re_δ₁, abs_zero]
    exact zero_lt_one
  · intro u₁ u₂ a₁ a₂ h
    simp only [param₁, RealArchParam.principal.injEq] at h
    obtain ⟨-, rfl, -, rfl⟩ := h
    exact ⟨Or.inr rfl, by simp⟩
  · intro u₁ u₂ a₁ h
    simp only [param₁, RealArchParam.principal.injEq] at h
    obtain ⟨-, h₁, -, h₂⟩ := h
    exact absurd (h₁.trans h₂.symm) (by decide)
  · intro u a₁ a₂ h _
    simp only [param₁, RealArchParam.principal.injEq] at h
    obtain ⟨h₁, -, h₂, -⟩ := h
    have hδ : δ₁ t = 0 := by
      have := h₁.trans h₂.symm
      linear_combination this
    exact δ₁_eq_zero ht hδ

private theorem exists_spec {k₀ : ℤ} (hk₀ : k₀ = 0 ∨ k₀ = 1) {lam : ℂ} {t : ℝ} (ht : 0 ≤ t)
    (hlam : lam = (1 - ((k₀ : ℂ) - 1) ^ 2) / 4 + t) (ht0 : k₀ = 0 → 0 < t) (u₀ : ℂ) {a : ZMod 2}
    (hpar : ((k₀ : ℤ) : ZMod 2) = a) (j : ZMod 2) : ∃ P : RealArchParam, Spec P k₀ lam u₀ a j t := by
  rcases hk₀ with rfl | rfl
  · refine ⟨param₀ u₀ j t, spec_param₀ u₀ j (ht0 rfl) ?_ ?_⟩
    · rw [hlam]
      push_cast
      ring
    · rw [← hpar]
      simp
  · refine ⟨param₁ u₀ t, spec_param₁ u₀ j ht ?_ ?_⟩
    · rw [hlam]
      push_cast
      ring
    · rw [← hpar]
      simp

private def SpecD (P : RealArchParam) (k₀ : ℤ) (lam u₀ : ℂ) (a : ZMod 2) : Prop :=
  (∀ (u₁ u₂ : ℂ) (a₁ a₂ : ZMod 2), P ≠ RealArchParam.principal u₁ a₁ u₂ a₂) ∧
  RealArchParam.laplaceEigenvalue P = lam ∧
  P.centralExponent + 1 = u₀ ∧
  P.centralSign = a ∧
  (∀ (u : ℂ) (n : ℕ) (hn : 1 ≤ n), P = RealArchParam.discrete u n hn → k₀ = (n : ℤ) + 1)

private theorem one_le_toNat_sub_one {k₀ : ℤ} (hk₀ : 2 ≤ k₀) : 1 ≤ (k₀ - 1).toNat := by
  omega

private theorem toNat_sub_one_cast {k₀ : ℤ} (hk₀ : 2 ≤ k₀) : (((k₀ - 1).toNat : ℕ) : ℤ) = k₀ - 1 :=
  Int.toNat_of_nonneg (by omega)

private def paramD (u₀ : ℂ) {k₀ : ℤ} (hk₀ : 2 ≤ k₀) : RealArchParam :=
  RealArchParam.discrete ((u₀ - 1) / 2) (k₀ - 1).toNat (one_le_toNat_sub_one hk₀)

private theorem spec_paramD (u₀ : ℂ) {k₀ : ℤ} (hk₀ : 2 ≤ k₀) {lam : ℂ} (hlam : lam = (1 - ((k₀ : ℂ) - 1) ^ 2) / 4)
    {a : ZMod 2} (hpar : ((k₀ : ℤ) : ZMod 2) = a) : SpecD (paramD u₀ hk₀) k₀ lam u₀ a := by
  have hcast : (((k₀ - 1).toNat : ℕ) : ℂ) = (k₀ : ℂ) - 1 := by
    have h := congrArg (fun z : ℤ => (z : ℂ)) (toNat_sub_one_cast hk₀)
    push_cast at h
    exact h
  refine ⟨fun u₁ u₂ a₁ a₂ h => RealArchParam.noConfusion h, ?_, ?_, ?_, ?_⟩
  · rw [hlam]
    show (1 - (((k₀ - 1).toNat : ℕ) : ℂ) ^ 2) / 4 = (1 - ((k₀ : ℂ) - 1) ^ 2) / 4
    rw [hcast]
  · show 2 * ((u₀ - 1) / 2) + 1 = u₀
    ring
  · show (((k₀ - 1).toNat : ℕ) : ZMod 2) + 1 = a
    rw [← hpar, ← Int.cast_natCast, toNat_sub_one_cast hk₀]
    push_cast
    ring
  · intro u n hn h
    have hn' : (k₀ - 1).toNat = n := (RealArchParam.discrete.inj h).2
    rw [← hn', toNat_sub_one_cast hk₀]
    ring

private theorem exists_specD {k₀ : ℤ} (hk₀ : 2 ≤ k₀) {lam : ℂ} (hlam : lam = (1 - ((k₀ : ℂ) - 1) ^ 2) / 4) (u₀ : ℂ)
    {a : ZMod 2} (hpar : ((k₀ : ℤ) : ZMod 2) = a) : ∃ P : RealArchParam, SpecD P k₀ lam u₀ a :=
  ⟨paramD u₀ hk₀, spec_paramD u₀ hk₀ hlam hpar⟩

end ArchParameter

namespace MinimalWeight

open Classical in
private theorem exists_minimal_natAbs {P : ℤ → Prop} {m₀ : ℤ} (h : P m₀) :
    ∃ k₀ : ℕ, (P (k₀ : ℤ) ∨ P (-(k₀ : ℤ))) ∧ ∀ m : ℤ, m.natAbs < k₀ → ¬ P m := by
  have hQ : ∃ n : ℕ, P (n : ℤ) ∨ P (-(n : ℤ)) := by
    refine ⟨m₀.natAbs, ?_⟩
    rcases Int.natAbs_eq m₀ with hm | hm
    · exact Or.inl (hm ▸ h)
    · exact Or.inr (hm ▸ h)
  refine ⟨Nat.find hQ, Nat.find_spec hQ, fun m hm hPm => ?_⟩
  apply Nat.find_min hQ hm
  rcases Int.natAbs_eq m with hm' | hm'
  · exact Or.inl (hm' ▸ hPm)
  · exact Or.inr (hm' ▸ hPm)

private theorem exists_minimal_natAbs' {P : ℤ → Prop} {m₀ : ℤ} (h : P m₀) :
    ∃ k₀ : ℕ, (∀ m : ℤ, m.natAbs < k₀ → ¬ P m) ∧ (P (k₀ : ℤ) ∨ (¬ P (k₀ : ℤ) ∧ P (-(k₀ : ℤ)))) := by
  obtain ⟨k₀, hk, hmin⟩ := exists_minimal_natAbs h
  refine ⟨k₀, hmin, ?_⟩
  by_cases hpos : P (k₀ : ℤ)
  · exact Or.inl hpos
  · exact Or.inr ⟨hpos, hk.resolve_left hpos⟩

end MinimalWeight

namespace TestCalculus

p2m_open "AutomorphicForm~continuous_unipotentGL2~isIsotypicCuspFormAt_of_mem_isotypicCuspSubmodule NumberField NumberField.AdelicLevel IsDedekindDomain"
open scoped Classical

variable {K : Type} [Field K] [NumberField K]

private def _root_.TestCalculus.leftDeriv {w : InfinitePlace K} (hw : w.IsReal) (d : ArchDir) (α : AdelicGL2 (𝓞 K) K → ℂ) :
    AdelicGL2 (𝓞 K) K → ℂ :=
  fun y => deriv (fun t : ℝ => α (archFlowAt hw d (-t) * y)) 0

p2m_export "TestCalculus" "leftDeriv"
private def _root_.TestCalculus.lowerOp {w : InfinitePlace K} (hw : w.IsReal) (φ : AdelicGL2 (𝓞 K) K → ℂ) : AdelicGL2 (𝓞 K) K → ℂ :=
  archDerivAt hw .H φ - Complex.I • (archDerivAt hw .E φ + archDerivAt hw .Fm φ)

p2m_export "TestCalculus" "lowerOp"
private def lowerTest {w : InfinitePlace K} (hw : w.IsReal) (β : AdelicGL2 (𝓞 K) K → ℂ) : AdelicGL2 (𝓞 K) K → ℂ :=
  leftDeriv hw .H β - Complex.I • (leftDeriv hw .E β + leftDeriv hw .Fm β)

private def casimirTest {w : InfinitePlace K} (hw : w.IsReal) (β : AdelicGL2 (𝓞 K) K → ℂ) :
    AdelicGL2 (𝓞 K) K → ℂ :=
  -((1 / 4 : ℂ) • leftDeriv hw .H (leftDeriv hw .H β) - (1 / 2 : ℂ) • leftDeriv hw .H β +
    leftDeriv hw .E (leftDeriv hw .Fm β))

private def LeftDerivTensor {w : InfinitePlace K} (hw : w.IsReal) : Prop :=
  ∀ (d : ArchDir) (fa : GL (Fin 2) (InfiniteAdeleRing K) → ℂ) (ff : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K) → ℂ),
    IsArchTestFactor K fa →
      ∃ fa' : GL (Fin 2) (InfiniteAdeleRing K) → ℂ, IsArchTestFactor K fa' ∧
        leftDeriv hw d (fun z => fa (glArch (𝓞 K) K z) * ff (glFin (𝓞 K) K z))
          = fun y => fa' (glArch (𝓞 K) K y) * ff (glFin (𝓞 K) K y)

private theorem hasCompactSupport_const_smul {X : Type} [TopologicalSpace X] (c : ℂ) {f : X → ℂ}
    (hf : HasCompactSupport f) : HasCompactSupport (c • f) :=
  hf.comp_left (g := fun z : ℂ => c * z) (mul_zero c)

private theorem isArchTestFactor_add {fa fb : GL (Fin 2) (InfiniteAdeleRing K) → ℂ} (ha : IsArchTestFactor K fa)
    (hb : IsArchTestFactor K fb) : IsArchTestFactor K (fa + fb) := by
  obtain ⟨⟨Φa, hΦa, hfa⟩, hsa⟩ := ha
  obtain ⟨⟨Φb, hΦb, hfb⟩, hsb⟩ := hb
  refine ⟨⟨Φa + Φb, hΦa.add hΦb, fun g => ?_⟩, hsa.add hsb⟩
  simp only [Pi.add_apply, hfa g, hfb g]

private theorem isArchTestFactor_smul (c : ℂ) {fa : GL (Fin 2) (InfiniteAdeleRing K) → ℂ}
    (ha : IsArchTestFactor K fa) : IsArchTestFactor K (c • fa) := by
  obtain ⟨⟨Φa, hΦa, hfa⟩, hsa⟩ := ha
  refine ⟨⟨c • Φa, hΦa.const_smul c, fun g => ?_⟩, hasCompactSupport_const_smul c hsa⟩
  simp only [Pi.smul_apply, hfa g]

private theorem isArchTestFactor_sub {fa fb : GL (Fin 2) (InfiniteAdeleRing K) → ℂ} (ha : IsArchTestFactor K fa)
    (hb : IsArchTestFactor K fb) : IsArchTestFactor K (fa - fb) := by
  have h : fa - fb = fa + (-1 : ℂ) • fb := by
    funext g
    simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [h]
  exact isArchTestFactor_add ha (isArchTestFactor_smul _ hb)

private theorem isArchTestFactor_neg {fa : GL (Fin 2) (InfiniteAdeleRing K) → ℂ} (ha : IsArchTestFactor K fa) :
    IsArchTestFactor K (-fa) := by
  have h : -fa = (-1 : ℂ) • fa := by
    funext g
    simp only [Pi.neg_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [h]
  exact isArchTestFactor_smul _ ha

private theorem eq_tensor_of_isFactorizableTestFn {β : AdelicGL2 (𝓞 K) K → ℂ} (hβ : IsFactorizableTestFn K β) :
    ∃ (fa : GL (Fin 2) (InfiniteAdeleRing K) → ℂ) (ff : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K) → ℂ),
      IsArchTestFactor K fa ∧ IsFinTestFactor K ff ∧ β = fun z => fa (glArch (𝓞 K) K z) * ff (glFin (𝓞 K) K z) := by
  obtain ⟨fa, ff, hfa, hff, h⟩ := hβ
  exact ⟨fa, ff, hfa, hff, funext h⟩

private theorem isFactorizableTestFn_leftDeriv {w : InfinitePlace K} {hw : w.IsReal} (hT : LeftDerivTensor hw)
    (d : ArchDir) {β : AdelicGL2 (𝓞 K) K → ℂ} (hβ : IsFactorizableTestFn K β) :
    IsFactorizableTestFn K (leftDeriv hw d β) := by
  obtain ⟨fa, ff, hfa, hff, rfl⟩ := eq_tensor_of_isFactorizableTestFn hβ
  obtain ⟨fa', hfa', h⟩ := hT d fa ff hfa
  rw [h]
  exact ⟨fa', ff, hfa', hff, fun _ => rfl⟩

private theorem isFactorizableTestFn_lowerTest {w : InfinitePlace K} {hw : w.IsReal} (hT : LeftDerivTensor hw)
    {β : AdelicGL2 (𝓞 K) K → ℂ} (hβ : IsFactorizableTestFn K β) : IsFactorizableTestFn K (lowerTest hw β) := by
  obtain ⟨fa, ff, hfa, hff, rfl⟩ := eq_tensor_of_isFactorizableTestFn hβ
  obtain ⟨fH, hfH, eH⟩ := hT .H fa ff hfa
  obtain ⟨fE, hfE, eE⟩ := hT .E fa ff hfa
  obtain ⟨fF, hfF, eF⟩ := hT .Fm fa ff hfa
  refine ⟨fH - Complex.I • (fE + fF), ff,
    isArchTestFactor_sub hfH (isArchTestFactor_smul _ (isArchTestFactor_add hfE hfF)), hff, fun y => ?_⟩
  simp only [lowerTest, eH, eE, eF, Pi.sub_apply, Pi.smul_apply, Pi.add_apply, smul_eq_mul]
  ring

private theorem isFactorizableTestFn_casimirTest {w : InfinitePlace K} {hw : w.IsReal} (hT : LeftDerivTensor hw)
    {β : AdelicGL2 (𝓞 K) K → ℂ} (hβ : IsFactorizableTestFn K β) : IsFactorizableTestFn K (casimirTest hw β) := by
  obtain ⟨fa, ff, hfa, hff, rfl⟩ := eq_tensor_of_isFactorizableTestFn hβ
  obtain ⟨fH, hfH, eH⟩ := hT .H fa ff hfa
  obtain ⟨fHH, hfHH, eHH⟩ := hT .H fH ff hfH
  obtain ⟨fF, hfF, eF⟩ := hT .Fm fa ff hfa
  obtain ⟨fEF, hfEF, eEF⟩ := hT .E fF ff hfF
  refine ⟨-((1 / 4 : ℂ) • fHH - (1 / 2 : ℂ) • fH + fEF), ff,
    isArchTestFactor_neg (isArchTestFactor_add (isArchTestFactor_sub (isArchTestFactor_smul _ hfHH)
      (isArchTestFactor_smul _ hfH)) hfEF), hff, fun y => ?_⟩
  simp only [casimirTest, eH, eHH, eF, eEF, Pi.neg_apply, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

section

variable {w : InfinitePlace K} {hw : w.IsReal} (hT : LeftDerivTensor hw) (φ : AdelicGL2 (𝓞 K) K → ℂ)
  (hb : ∀ (d : ArchDir) (γ : AdelicGL2 (𝓞 K) K → ℂ), IsFactorizableTestFn K γ →
    archDerivAt hw d (rightConv K φ γ) = rightConv K φ (leftDeriv hw d γ))
  (hadd : ∀ γ₁ γ₂ : AdelicGL2 (𝓞 K) K → ℂ, Continuous γ₁ → HasCompactSupport γ₁ → Continuous γ₂ →
    HasCompactSupport γ₂ → rightConv K φ (γ₁ + γ₂) = rightConv K φ γ₁ + rightConv K φ γ₂)
  (hsmul : ∀ (γ : AdelicGL2 (𝓞 K) K → ℂ) (c : ℂ), rightConv K φ (c • γ) = c • rightConv K φ γ)

include hadd in
private theorem rightConv_add_of_isFactorizableTestFn {γ₁ γ₂ : AdelicGL2 (𝓞 K) K → ℂ}
    (h₁ : IsFactorizableTestFn K γ₁) (h₂ : IsFactorizableTestFn K γ₂) :
    rightConv K φ (γ₁ + γ₂) = rightConv K φ γ₁ + rightConv K φ γ₂ :=
  hadd γ₁ γ₂ (continuous_and_hasCompactSupport_of_isFactorizableTestFn K γ₁ h₁).1
    (continuous_and_hasCompactSupport_of_isFactorizableTestFn K γ₁ h₁).2
    (continuous_and_hasCompactSupport_of_isFactorizableTestFn K γ₂ h₂).1
    (continuous_and_hasCompactSupport_of_isFactorizableTestFn K γ₂ h₂).2

include hadd hsmul in

private theorem rightConv_sub_smul_add {γ₁ γ₂ γ₃ : AdelicGL2 (𝓞 K) K → ℂ} (c : ℂ) (h₁ : IsFactorizableTestFn K γ₁)
    (h₂ : IsFactorizableTestFn K γ₂) (h₃ : IsFactorizableTestFn K γ₃) :
    rightConv K φ (γ₁ - c • (γ₂ + γ₃)) = rightConv K φ γ₁ - c • (rightConv K φ γ₂ + rightConv K φ γ₃) := by
  have hc₂ := continuous_and_hasCompactSupport_of_isFactorizableTestFn K γ₂ h₂
  have hc₃ := continuous_and_hasCompactSupport_of_isFactorizableTestFn K γ₃ h₃
  have hc₁ := continuous_and_hasCompactSupport_of_isFactorizableTestFn K γ₁ h₁
  have e : γ₁ - c • (γ₂ + γ₃) = γ₁ + (-c) • (γ₂ + γ₃) := by
    funext y
    simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [e, hadd γ₁ ((-c) • (γ₂ + γ₃)) hc₁.1 hc₁.2 ((hc₂.1.add hc₃.1).const_smul (-c))
      (hasCompactSupport_const_smul (-c) (hc₂.2.add hc₃.2)), hsmul, rightConv_add_of_isFactorizableTestFn φ hadd h₂ h₃]
  funext y
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

include hT hb hadd hsmul in

private theorem lowerOp_rightConv {β : AdelicGL2 (𝓞 K) K → ℂ} (hβ : IsFactorizableTestFn K β) :
    lowerOp hw (rightConv K φ β) = rightConv K φ (lowerTest hw β) := by
  unfold lowerOp lowerTest
  rw [hb .H β hβ, hb .E β hβ, hb .Fm β hβ,
    rightConv_sub_smul_add φ hadd hsmul _ (isFactorizableTestFn_leftDeriv hT .H hβ)
      (isFactorizableTestFn_leftDeriv hT .E hβ) (isFactorizableTestFn_leftDeriv hT .Fm hβ)]

include hadd hsmul in

private theorem rightConv_casimir_combo {γ₁ γ₂ γ₃ : AdelicGL2 (𝓞 K) K → ℂ} (a b : ℂ)
    (h₁ : IsFactorizableTestFn K γ₁) (h₂ : IsFactorizableTestFn K γ₂) (h₃ : IsFactorizableTestFn K γ₃) :
    rightConv K φ (-(a • γ₁ - b • γ₂ + γ₃))
      = -(a • rightConv K φ γ₁ - b • rightConv K φ γ₂ + rightConv K φ γ₃) := by
  have hc₁ := continuous_and_hasCompactSupport_of_isFactorizableTestFn K γ₁ h₁
  have hc₂ := continuous_and_hasCompactSupport_of_isFactorizableTestFn K γ₂ h₂
  have hc₃ := continuous_and_hasCompactSupport_of_isFactorizableTestFn K γ₃ h₃
  have e : -(a • γ₁ - b • γ₂ + γ₃) = (-a) • γ₁ + (b • γ₂ + (-1 : ℂ) • γ₃) := by
    funext y
    simp only [Pi.neg_apply, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [e, hadd ((-a) • γ₁) (b • γ₂ + (-1 : ℂ) • γ₃) (hc₁.1.const_smul (-a)) (hasCompactSupport_const_smul (-a) hc₁.2)
      ((hc₂.1.const_smul b).add (hc₃.1.const_smul (-1 : ℂ)))
      ((hasCompactSupport_const_smul b hc₂.2).add (hasCompactSupport_const_smul (-1 : ℂ) hc₃.2)),
    hadd (b • γ₂) ((-1 : ℂ) • γ₃) (hc₂.1.const_smul b) (hasCompactSupport_const_smul b hc₂.2)
      (hc₃.1.const_smul (-1 : ℂ))
      (hasCompactSupport_const_smul (-1 : ℂ) hc₃.2), hsmul, hsmul, hsmul]
  funext y
  simp only [Pi.neg_apply, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

include hT hb hadd hsmul in

private theorem archCasimirAt_rightConv {β : AdelicGL2 (𝓞 K) K → ℂ} (hβ : IsFactorizableTestFn K β) :
    archCasimirAt hw (rightConv K φ β) = rightConv K φ (casimirTest hw β) := by
  have hH := isFactorizableTestFn_leftDeriv hT .H hβ
  have hF := isFactorizableTestFn_leftDeriv hT .Fm hβ
  unfold archCasimirAt casimirTest
  rw [hb .H β hβ, hb .Fm β hβ, hb .H _ hH, hb .E _ hF,
    rightConv_casimir_combo φ hadd hsmul _ _ (isFactorizableTestFn_leftDeriv hT .H hH) hH
      (isFactorizableTestFn_leftDeriv hT .E hF)]

end

section

variable {w : InfinitePlace K} (hw : w.IsReal)

private theorem glFin_archFlowAt (d : ArchDir) (t : ℝ) : glFin (𝓞 K) K (archFlowAt hw d t) = 1 :=
  glFin_adelicArchGLIncl K _

private theorem exists_eq_mul_of_leftDeriv_ne_zero (U₀ : Subgroup (AdelicGL2 (𝓞 K) K)) (d : ArchDir)
    {γ : AdelicGL2 (𝓞 K) K → ℂ}
    (h : ∀ x, γ x ≠ 0 → ∃ a k : AdelicGL2 (𝓞 K) K, glFin (𝓞 K) K a = 1 ∧ k ∈ U₀ ∧ x = a * k) (x : AdelicGL2 (𝓞 K) K)
    (hx : leftDeriv hw d γ x ≠ 0) : ∃ a k : AdelicGL2 (𝓞 K) K, glFin (𝓞 K) K a = 1 ∧ k ∈ U₀ ∧ x = a * k := by
  by_contra hcon
  apply hx
  have hzero : ∀ t : ℝ, γ (archFlowAt hw d (-t) * x) = 0 := by
    intro t
    by_contra ht
    obtain ⟨a, k, ha, hk, hak⟩ := h _ ht
    exact hcon ⟨(archFlowAt hw d (-t))⁻¹ * a, k, by rw [map_mul, map_inv, glFin_archFlowAt, ha, inv_one, one_mul],
      hk, by rw [mul_assoc, ← hak, inv_mul_cancel_left]⟩
  show deriv (fun t : ℝ => γ (archFlowAt hw d (-t) * x)) 0 = 0
  simp only [hzero]
  exact deriv_const 0 (0 : ℂ)

private theorem exists_eq_mul_of_lowerTest_ne_zero (U₀ : Subgroup (AdelicGL2 (𝓞 K) K)) {β : AdelicGL2 (𝓞 K) K → ℂ}
    (h : ∀ x, β x ≠ 0 → ∃ a k : AdelicGL2 (𝓞 K) K, glFin (𝓞 K) K a = 1 ∧ k ∈ U₀ ∧ x = a * k) (x : AdelicGL2 (𝓞 K) K)
    (hx : lowerTest hw β x ≠ 0) : ∃ a k : AdelicGL2 (𝓞 K) K, glFin (𝓞 K) K a = 1 ∧ k ∈ U₀ ∧ x = a * k := by
  by_contra hcon
  apply hx
  have hH : leftDeriv hw .H β x = 0 := by
    by_contra h'
    exact hcon (exists_eq_mul_of_leftDeriv_ne_zero hw U₀ .H h x h')
  have hE : leftDeriv hw .E β x = 0 := by
    by_contra h'
    exact hcon (exists_eq_mul_of_leftDeriv_ne_zero hw U₀ .E h x h')
  have hF : leftDeriv hw .Fm β x = 0 := by
    by_contra h'
    exact hcon (exists_eq_mul_of_leftDeriv_ne_zero hw U₀ .Fm h x h')
  simp only [lowerTest, Pi.sub_apply, Pi.smul_apply, Pi.add_apply, hH, hE, hF, add_zero, smul_zero, sub_zero]

private theorem exists_eq_mul_of_casimirTest_ne_zero (U₀ : Subgroup (AdelicGL2 (𝓞 K) K)) {β : AdelicGL2 (𝓞 K) K → ℂ}
    (h : ∀ x, β x ≠ 0 → ∃ a k : AdelicGL2 (𝓞 K) K, glFin (𝓞 K) K a = 1 ∧ k ∈ U₀ ∧ x = a * k) (x : AdelicGL2 (𝓞 K) K)
    (hx : casimirTest hw β x ≠ 0) : ∃ a k : AdelicGL2 (𝓞 K) K, glFin (𝓞 K) K a = 1 ∧ k ∈ U₀ ∧ x = a * k := by
  by_contra hcon
  apply hx
  have hHH : leftDeriv hw .H (leftDeriv hw .H β) x = 0 := by
    by_contra h'
    exact hcon (exists_eq_mul_of_leftDeriv_ne_zero hw U₀ .H (exists_eq_mul_of_leftDeriv_ne_zero hw U₀ .H h) x h')
  have hH : leftDeriv hw .H β x = 0 := by
    by_contra h'
    exact hcon (exists_eq_mul_of_leftDeriv_ne_zero hw U₀ .H h x h')
  have hEF : leftDeriv hw .E (leftDeriv hw .Fm β) x = 0 := by
    by_contra h'
    exact hcon (exists_eq_mul_of_leftDeriv_ne_zero hw U₀ .E (exists_eq_mul_of_leftDeriv_ne_zero hw U₀ .Fm h) x h')
  simp only [casimirTest, Pi.neg_apply, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, hHH, hH, hEF, smul_zero, sub_zero,
    add_zero, neg_zero]

end

section

private def _root_.TestCalculus.raiseOp {w : InfinitePlace K} (hw : w.IsReal) (φ : AdelicGL2 (𝓞 K) K → ℂ) : AdelicGL2 (𝓞 K) K → ℂ :=
  archDerivAt hw .H φ + Complex.I • (archDerivAt hw .E φ + archDerivAt hw .Fm φ)

p2m_export "TestCalculus" "raiseOp"
private def raiseTest {w : InfinitePlace K} (hw : w.IsReal) (β : AdelicGL2 (𝓞 K) K → ℂ) : AdelicGL2 (𝓞 K) K → ℂ :=
  leftDeriv hw .H β + Complex.I • (leftDeriv hw .E β + leftDeriv hw .Fm β)

private theorem isFactorizableTestFn_raiseTest {w : InfinitePlace K} {hw : w.IsReal} (hT : LeftDerivTensor hw)
    {β : AdelicGL2 (𝓞 K) K → ℂ} (hβ : IsFactorizableTestFn K β) : IsFactorizableTestFn K (raiseTest hw β) := by
  obtain ⟨fa, ff, hfa, hff, rfl⟩ := eq_tensor_of_isFactorizableTestFn hβ
  obtain ⟨fH, hfH, eH⟩ := hT .H fa ff hfa
  obtain ⟨fE, hfE, eE⟩ := hT .E fa ff hfa
  obtain ⟨fF, hfF, eF⟩ := hT .Fm fa ff hfa
  refine ⟨fH + Complex.I • (fE + fF), ff,
    isArchTestFactor_add hfH (isArchTestFactor_smul _ (isArchTestFactor_add hfE hfF)), hff, fun y => ?_⟩
  simp only [raiseTest, eH, eE, eF, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

end

section

variable {w : InfinitePlace K} {hw : w.IsReal} (hT : LeftDerivTensor hw) (φ : AdelicGL2 (𝓞 K) K → ℂ)
  (hb : ∀ (d : ArchDir) (γ : AdelicGL2 (𝓞 K) K → ℂ), IsFactorizableTestFn K γ →
    archDerivAt hw d (rightConv K φ γ) = rightConv K φ (leftDeriv hw d γ))
  (hadd : ∀ γ₁ γ₂ : AdelicGL2 (𝓞 K) K → ℂ, Continuous γ₁ → HasCompactSupport γ₁ → Continuous γ₂ →
    HasCompactSupport γ₂ → rightConv K φ (γ₁ + γ₂) = rightConv K φ γ₁ + rightConv K φ γ₂)
  (hsmul : ∀ (γ : AdelicGL2 (𝓞 K) K → ℂ) (c : ℂ), rightConv K φ (c • γ) = c • rightConv K φ γ)

include hadd hsmul in
private theorem rightConv_add_smul_add {γ₁ γ₂ γ₃ : AdelicGL2 (𝓞 K) K → ℂ} (c : ℂ) (h₁ : IsFactorizableTestFn K γ₁)
    (h₂ : IsFactorizableTestFn K γ₂) (h₃ : IsFactorizableTestFn K γ₃) :
    rightConv K φ (γ₁ + c • (γ₂ + γ₃)) = rightConv K φ γ₁ + c • (rightConv K φ γ₂ + rightConv K φ γ₃) := by
  have hc₂ := continuous_and_hasCompactSupport_of_isFactorizableTestFn K γ₂ h₂
  have hc₃ := continuous_and_hasCompactSupport_of_isFactorizableTestFn K γ₃ h₃
  have hc₁ := continuous_and_hasCompactSupport_of_isFactorizableTestFn K γ₁ h₁
  rw [hadd γ₁ (c • (γ₂ + γ₃)) hc₁.1 hc₁.2 ((hc₂.1.add hc₃.1).const_smul c)
      (hasCompactSupport_const_smul c (hc₂.2.add hc₃.2)), hsmul, rightConv_add_of_isFactorizableTestFn φ hadd h₂ h₃]

include hT hb hadd hsmul in
private theorem raiseOp_rightConv {β : AdelicGL2 (𝓞 K) K → ℂ} (hβ : IsFactorizableTestFn K β) :
    raiseOp hw (rightConv K φ β) = rightConv K φ (raiseTest hw β) := by
  unfold raiseOp raiseTest
  rw [hb .H β hβ, hb .E β hβ, hb .Fm β hβ,
    rightConv_add_smul_add φ hadd hsmul _ (isFactorizableTestFn_leftDeriv hT .H hβ)
      (isFactorizableTestFn_leftDeriv hT .E hβ) (isFactorizableTestFn_leftDeriv hT .Fm hβ)]

end

section

variable {w : InfinitePlace K} (hw : w.IsReal)

private theorem exists_eq_mul_of_raiseTest_ne_zero (U₀ : Subgroup (AdelicGL2 (𝓞 K) K)) {β : AdelicGL2 (𝓞 K) K → ℂ}
    (h : ∀ x, β x ≠ 0 → ∃ a k : AdelicGL2 (𝓞 K) K, glFin (𝓞 K) K a = 1 ∧ k ∈ U₀ ∧ x = a * k) (x : AdelicGL2 (𝓞 K) K)
    (hx : raiseTest hw β x ≠ 0) : ∃ a k : AdelicGL2 (𝓞 K) K, glFin (𝓞 K) K a = 1 ∧ k ∈ U₀ ∧ x = a * k := by
  by_contra hcon
  apply hx
  have hH : leftDeriv hw .H β x = 0 := by
    by_contra h'
    exact hcon (exists_eq_mul_of_leftDeriv_ne_zero hw U₀ .H h x h')
  have hE : leftDeriv hw .E β x = 0 := by
    by_contra h'
    exact hcon (exists_eq_mul_of_leftDeriv_ne_zero hw U₀ .E h x h')
  have hF : leftDeriv hw .Fm β x = 0 := by
    by_contra h'
    exact hcon (exists_eq_mul_of_leftDeriv_ne_zero hw U₀ .Fm h x h')
  simp only [raiseTest, Pi.add_apply, Pi.smul_apply, hH, hE, hF, add_zero, smul_zero]

end

end TestCalculus

namespace ReproducingClosure

p2m_open "AutomorphicForm~continuous_unipotentGL2~isIsotypicCuspFormAt_of_mem_isotypicCuspSubmodule NumberField NumberField.AdelicLevel IsDedekindDomain Filter Topology"
open scoped Classical

variable {K : Type} [Field K] [NumberField K]

private theorem mem_of_tendsto_of_finiteDimensional {X : Type} (E : Submodule ℂ (X → ℂ)) [FiniteDimensional ℂ E]
    (L : Submodule ℂ (X → ℂ)) (hLE : L ≤ E) (u : ℕ → X → ℂ) (hu : ∀ n, u n ∈ L) (f : X → ℂ)
    (hlim : ∀ x, Tendsto (fun n => u n x) atTop (𝓝 (f x))) : f ∈ L := by
  haveI : FiniteDimensional ℂ L := Submodule.finiteDimensional_of_le hLE
  have ht : Tendsto u atTop (𝓝 f) := tendsto_pi_nhds.2 hlim
  exact L.closed_of_finiteDimensional.mem_of_tendsto ht (Eventually.of_forall hu)

private theorem hasCompactSupport_const_smul {X : Type} [TopologicalSpace X] (c : ℂ) {f : X → ℂ}
    (hf : HasCompactSupport f) : HasCompactSupport (c • f) :=
  hf.comp_left (g := fun z : ℂ => c * z) (mul_zero c)

private theorem isArchTestFactor_add {fa fb : GL (Fin 2) (InfiniteAdeleRing K) → ℂ} (ha : IsArchTestFactor K fa)
    (hb : IsArchTestFactor K fb) : IsArchTestFactor K (fa + fb) := by
  obtain ⟨⟨Φa, hΦa, hfa⟩, hsa⟩ := ha
  obtain ⟨⟨Φb, hΦb, hfb⟩, hsb⟩ := hb
  refine ⟨⟨Φa + Φb, hΦa.add hΦb, fun g => ?_⟩, hsa.add hsb⟩
  simp only [Pi.add_apply, hfa g, hfb g]

private theorem isArchTestFactor_smul (c : ℂ) {fa : GL (Fin 2) (InfiniteAdeleRing K) → ℂ}
    (ha : IsArchTestFactor K fa) : IsArchTestFactor K (c • fa) := by
  obtain ⟨⟨Φa, hΦa, hfa⟩, hsa⟩ := ha
  refine ⟨⟨c • Φa, hΦa.const_smul c, fun g => ?_⟩, hasCompactSupport_const_smul c hsa⟩
  simp only [Pi.smul_apply, hfa g]

section

variable (Q : (GL (Fin 2) (InfiniteAdeleRing K) → ℂ) → Prop) (hQ0 : Q 0)
  (hQadd : ∀ {fa fb : GL (Fin 2) (InfiniteAdeleRing K) → ℂ}, Q fa → Q fb → Q (fa + fb))
  (hQsmul : ∀ (c : ℂ) {fa : GL (Fin 2) (InfiniteAdeleRing K) → ℂ}, Q fa → Q (c • fa))

include hQ0 hQadd hQsmul in

private def typedTestFactors : Submodule ℂ (GL (Fin 2) (InfiniteAdeleRing K) → ℂ) where
  carrier := {fa | IsArchTestFactor K fa ∧ Q fa}
  zero_mem' := ⟨isArchTestFactor_zero K, hQ0⟩
  add_mem' := fun ha hb => ⟨isArchTestFactor_add ha.1 hb.1, hQadd ha.2 hb.2⟩
  smul_mem' := fun c _ ha => ⟨isArchTestFactor_smul c ha.1, hQsmul c ha.2⟩

include hQ0 hQadd hQsmul in
private theorem mem_typedTestFactors {fa : GL (Fin 2) (InfiniteAdeleRing K) → ℂ} :
    fa ∈ typedTestFactors Q hQ0 hQadd hQsmul ↔ IsArchTestFactor K fa ∧ Q fa :=
  Iff.rfl

end

private def tensor (fa : GL (Fin 2) (InfiniteAdeleRing K) → ℂ) (ff : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K) → ℂ) :
    AdelicGL2 (𝓞 K) K → ℂ :=
  fun g => fa (glArch (𝓞 K) K g) * ff (glFin (𝓞 K) K g)

private theorem tensor_add (fa fb : GL (Fin 2) (InfiniteAdeleRing K) → ℂ)
    (ff : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K) → ℂ) :
    tensor (fa + fb) ff = tensor fa ff + tensor fb ff := by
  funext g
  simp only [tensor, Pi.add_apply]
  ring

private theorem tensor_smul (c : ℂ) (fa : GL (Fin 2) (InfiniteAdeleRing K) → ℂ)
    (ff : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K) → ℂ) : tensor (c • fa) ff = c • tensor fa ff := by
  funext g
  simp only [tensor, Pi.smul_apply, smul_eq_mul]
  ring

private theorem isFactorizableTestFn_tensor {fa : GL (Fin 2) (InfiniteAdeleRing K) → ℂ}
    {ff : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K) → ℂ} (hfa : IsArchTestFactor K fa) (hff : IsFinTestFactor K ff) :
    IsFactorizableTestFn K (tensor fa ff) :=
  ⟨fa, ff, hfa, hff, fun _ => rfl⟩

section

variable (Q : (GL (Fin 2) (InfiniteAdeleRing K) → ℂ) → Prop) (hQ0 : Q 0)
  (hQadd : ∀ {fa fb : GL (Fin 2) (InfiniteAdeleRing K) → ℂ}, Q fa → Q fb → Q (fa + fb))
  (hQsmul : ∀ (c : ℂ) {fa : GL (Fin 2) (InfiniteAdeleRing K) → ℂ}, Q fa → Q (c • fa))
  (f : AdelicGL2 (𝓞 K) K → ℂ) {ff : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K) → ℂ} (hff : IsFinTestFactor K ff)
  (hadd : ∀ γ₁ γ₂ : AdelicGL2 (𝓞 K) K → ℂ, Continuous γ₁ → HasCompactSupport γ₁ → Continuous γ₂ →
    HasCompactSupport γ₂ → rightConv K f (γ₁ + γ₂) = rightConv K f γ₁ + rightConv K f γ₂)
  (hsmul : ∀ (γ : AdelicGL2 (𝓞 K) K → ℂ) (c : ℂ), rightConv K f (c • γ) = c • rightConv K f γ)

include Q hQ0 hQadd hQsmul f hff hadd

private theorem rightConv_tensor_add (a b : typedTestFactors Q hQ0 hQadd hQsmul) :
    rightConv K f (tensor ((a : GL (Fin 2) (InfiniteAdeleRing K) → ℂ) + (b : GL (Fin 2) (InfiniteAdeleRing K) → ℂ)) ff)
      = rightConv K f (tensor a ff) + rightConv K f (tensor b ff) := by
  have h1 := continuous_and_hasCompactSupport_of_isFactorizableTestFn K _
    (isFactorizableTestFn_tensor ((mem_typedTestFactors Q hQ0 hQadd hQsmul).1 a.2).1 hff)
  have h2 := continuous_and_hasCompactSupport_of_isFactorizableTestFn K _
    (isFactorizableTestFn_tensor ((mem_typedTestFactors Q hQ0 hQadd hQsmul).1 b.2).1 hff)
  rw [tensor_add, hadd _ _ h1.1 h1.2 h2.1 h2.2]

private def convMap : typedTestFactors Q hQ0 hQadd hQsmul →ₗ[ℂ] (AdelicGL2 (𝓞 K) K → ℂ) where
  toFun a := rightConv K f (tensor (a : GL (Fin 2) (InfiniteAdeleRing K) → ℂ) ff)
  map_add' a b := by
    show rightConv K f (tensor ((a : GL (Fin 2) (InfiniteAdeleRing K) → ℂ)
        + (b : GL (Fin 2) (InfiniteAdeleRing K) → ℂ)) ff) = rightConv K f (tensor a ff) + rightConv K f (tensor b ff)
    exact rightConv_tensor_add Q hQ0 hQadd hQsmul f hff hadd a b
  map_smul' c a := by
    show rightConv K f (tensor (c • (a : GL (Fin 2) (InfiniteAdeleRing K) → ℂ)) ff)
      = c • rightConv K f (tensor (a : GL (Fin 2) (InfiniteAdeleRing K) → ℂ) ff)
    rw [tensor_smul, hsmul]

private theorem convMap_apply (a : typedTestFactors Q hQ0 hQadd hQsmul) :
    convMap Q hQ0 hQadd hQsmul f hff hadd hsmul a
      = rightConv K f (tensor (a : GL (Fin 2) (InfiniteAdeleRing K) → ℂ) ff) :=
  rfl

include hsmul in
private theorem exists_isFactorizableTestFn_rightConv_eq (E : Submodule ℂ (AdelicGL2 (𝓞 K) K → ℂ))
    [FiniteDimensional ℂ E]
    (hmem : ∀ a : GL (Fin 2) (InfiniteAdeleRing K) → ℂ, IsArchTestFactor K a → Q a → rightConv K f (tensor a ff) ∈ E)
    (fa : ℕ → GL (Fin 2) (InfiniteAdeleRing K) → ℂ) (hfa : ∀ n, IsArchTestFactor K (fa n)) (hfaQ : ∀ n, Q (fa n))
    (hlim : ∀ g : AdelicGL2 (𝓞 K) K, Tendsto (fun n => rightConv K f (tensor (fa n) ff) g) atTop (𝓝 (f g))) :
    ∃ a : GL (Fin 2) (InfiniteAdeleRing K) → ℂ, IsArchTestFactor K a ∧ Q a ∧ rightConv K f (tensor a ff) = f := by
  set L := LinearMap.range (convMap Q hQ0 hQadd hQsmul f hff hadd hsmul) with hL
  have hLE : L ≤ E := by
    intro x hx
    obtain ⟨a, ha⟩ := LinearMap.mem_range.1 hx
    rw [← ha, convMap_apply]
    obtain ⟨ha1, ha2⟩ := (mem_typedTestFactors Q hQ0 hQadd hQsmul).1 a.2
    exact hmem _ ha1 ha2
  have hfL : f ∈ L :=
    mem_of_tendsto_of_finiteDimensional E L hLE (fun n => rightConv K f (tensor (fa n) ff))
      (fun n => ⟨⟨fa n, (mem_typedTestFactors Q hQ0 hQadd hQsmul).2 ⟨hfa n, hfaQ n⟩⟩, rfl⟩) f hlim
  obtain ⟨a, ha⟩ := LinearMap.mem_range.1 hfL
  obtain ⟨ha1, ha2⟩ := (mem_typedTestFactors Q hQ0 hQadd hQsmul).1 a.2
  exact ⟨(a : GL (Fin 2) (InfiniteAdeleRing K) → ℂ), ha1, ha2, ha⟩

end

end ReproducingClosure

namespace ConstituentSupply

open IsDedekindDomain NumberField MeasureTheory Matrix
open NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open NumberField.InfinitePlace.Completion
p2m_open "AutomorphicForm~continuous_unipotentGL2~isIsotypicCuspFormAt_of_mem_isotypicCuspSubmodule AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering"
open LanglandsTunnell LanglandsTunnell.Converse NumberField.TateGlobal
open AutomorphicForm.CuspidalConstituent

private def _root_.ConstituentSupply.catFamily (t₁ t₂ : ArchTypeFamily ℚ) : ArchTypeFamily ℚ where
  card w := t₁.card w + t₂.card w
  rep w i := Fin.addCases (t₁.rep w) (t₂.rep w) i

p2m_export "ConstituentSupply" "catFamily"
private theorem _root_.ConstituentSupply.left_isContainedIn_catFamily (t₁ t₂ : ArchTypeFamily ℚ) :
    ArchTypeFamily.IsContainedIn ℚ t₁ (catFamily t₁ t₂) :=
  fun w i => ⟨Fin.castAdd (t₂.card w) i, by simp [catFamily]⟩

p2m_export "ConstituentSupply" "left_isContainedIn_catFamily"
private theorem _root_.ConstituentSupply.right_isContainedIn_catFamily (t₁ t₂ : ArchTypeFamily ℚ) :
    ArchTypeFamily.IsContainedIn ℚ t₂ (catFamily t₁ t₂) :=
  fun w i => ⟨Fin.natAdd (t₁.card w) i, by simp [catFamily]⟩

p2m_export "ConstituentSupply" "right_isContainedIn_catFamily"
private theorem exists_mem_archCutSubmodule_of_mem_cuspKFiniteSubmodule {pins : CarrierPins ℚ} {ξ : pins.Z →* ℂˣ}
    {φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ} (hφ : φ ∈ cuspKFiniteSubmodule ℚ pins ξ) :
    ∃ tys : ArchTypeFamily ℚ, φ ∈ archCutSubmodule ℚ tys := by
  refine Submodule.span_induction (p := fun u _ => ∃ tys : ArchTypeFamily ℚ, u ∈ archCutSubmodule ℚ tys)
    (fun u hu => hu.2.2) ?_ ?_ ?_ hφ
  · exact ⟨⟨fun _ => 0, fun _ i => i.elim0⟩, Submodule.zero_mem _⟩
  · rintro u v _ _ ⟨t₁, h₁⟩ ⟨t₂, h₂⟩
    exact ⟨catFamily t₁ t₂, Submodule.add_mem _ (archCutSubmodule_mono ℚ (left_isContainedIn_catFamily t₁ t₂) h₁)
      (archCutSubmodule_mono ℚ (right_isContainedIn_catFamily t₁ t₂) h₂)⟩
  · rintro c u _ ⟨t, h⟩
    exact ⟨t, Submodule.smul_mem _ c h⟩

private theorem exists_of_ne_zero_of_mem_iSup {M : Type} [AddCommGroup M] [Module ℂ M] {ι : Type}
    (P : ι → Prop) (f : ι → Submodule ℂ M) {x : M} (hx0 : x ≠ 0) (hx : x ∈ ⨆ (i : ι) (_ : P i), f i) :
    ∃ i, P i := by
  by_contra h
  have hbot : (⨆ (i : ι) (_ : P i), f i) = ⊥ :=
    iSup_eq_bot.2 fun i => iSup_neg fun hi => h ⟨i, hi⟩
  rw [hbot, Submodule.mem_bot] at hx
  exact hx0 hx

private abbrev pinsOf (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 ℚ) ℚ)) : CarrierPins ℚ :=
  productionPinsOf ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂)
    (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ)

private theorem exists_isCuspConstituent_and_isIsotypicCuspFormAt_and_mem_archCutSubmodule
    (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 ℚ) ℚ)) (hd : d₁ < d₂)
    (hcov : CoversModCentre ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂))
    (Φ : HeckeEigensystem ℚ ℂ) (R : SmoothCuspRealizationAt ℚ (pinsOf c u d₁ d₂ T) Φ.toRawCentral)
    (hR : Continuous R.toFun) :
    ∃ (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (V : Submodule ℂ (AdelicGL2 (𝓞 ℚ) ℚ → ℂ))
      (ψ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ) (tys : ArchTypeFamily ℚ),
      R.exceptionalSet ⊆ S ∧ IsCuspConstituent ℚ (pinsOf c u d₁ d₂ T) R.centralChar V ∧ ψ ∈ V ∧ ψ ≠ 0 ∧
        IsIsotypicCuspFormAt ℚ (pinsOf c u d₁ d₂ T) R.centralChar Φ.level S Φ ψ ∧ ψ ∈ archCutSubmodule ℚ tys := by
  obtain ⟨S, tys₀, f, hS, _hf, _hbi, hne, hiso, hcut⟩ :=
    LanglandsTunnell.exists_rightConv_ne_zero_mem_isotypicCuspSubmodule_mem_archCutSubmodule c u d₁ d₂ T hd hcov Φ R
      hR
  have hsup := AutomorphicForm.isotypicCuspSubmodule_inf_archCutSubmodule_le_iSup_isCuspConstituent ℚ c u d₁ d₂ T hd
    hcov R.centralChar Φ.level S tys₀ Φ (Submodule.mem_inf.2 ⟨hiso, hcut⟩)
  obtain ⟨V, hV, hmeet, _⟩ := exists_of_ne_zero_of_mem_iSup _ _ hne hsup
  obtain ⟨ψ, hψV, hψ0, hψ⟩ := hmeet
  obtain ⟨tys, htys⟩ := exists_mem_archCutSubmodule_of_mem_cuspKFiniteSubmodule (hV.1.le hψV)
  exact ⟨S, V, ψ, tys, hS, hV, hψV, hψ0, hψ, htys⟩

end ConstituentSupply

namespace TranslateHull

open NumberField IsDedekindDomain
p2m_open "AutomorphicForm~continuous_unipotentGL2~isIsotypicCuspFormAt_of_mem_isotypicCuspSubmodule"

section

variable {G H : Type} [Group G] [Group H] {W : Type} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]

private theorem exists_finiteDimensional_of_mem_typeSubmodule (ι : H →* G) (ρ : Representation ℂ H W)
    {u : G → ℂ} (hu : u ∈ typeSubmodule ι ρ) :
    ∃ V : Submodule ℂ (G → ℂ), FiniteDimensional ℂ V ∧ u ∈ V ∧ ∀ k : H, ∀ v ∈ V, (fun x => v (x * ι k)) ∈ V := by
  refine Submodule.span_induction
    (p := fun u _ => ∃ V : Submodule ℂ (G → ℂ), FiniteDimensional ℂ V ∧ u ∈ V ∧
      ∀ k : H, ∀ v ∈ V, (fun x => v (x * ι k)) ∈ V) ?_ ?_ ?_ ?_ hu
  · rintro f ⟨T, hT, hf⟩
    refine ⟨LinearMap.range T, inferInstance, hf, ?_⟩
    rintro k _ ⟨v, rfl⟩
    refine ⟨ρ k v, ?_⟩
    funext x
    exact hT k v x
  · exact ⟨⊥, inferInstance, Submodule.zero_mem _, fun k v hv => by
      rw [Submodule.mem_bot] at hv ⊢
      subst hv
      rfl⟩
  · rintro f g _ _ ⟨V₁, h₁, hf, hV₁⟩ ⟨V₂, h₂, hg, hV₂⟩
    refine ⟨V₁ ⊔ V₂, Submodule.finiteDimensional_sup V₁ V₂, Submodule.add_mem_sup hf hg, ?_⟩
    intro k v hv
    obtain ⟨v₁, hv₁, v₂, hv₂, rfl⟩ := Submodule.mem_sup.1 hv
    exact Submodule.add_mem_sup (hV₁ k v₁ hv₁) (hV₂ k v₂ hv₂)
  · rintro c f _ ⟨V, hV, hf, hstab⟩
    exact ⟨V, hV, Submodule.smul_mem _ c hf, hstab⟩

private theorem exists_finiteDimensional_of_mem_iSup {n : ℕ} (ι : H →* G)
    (ρ : Fin n → (Σ m : ℕ, Representation ℂ H (Fin m → ℂ))) {u : G → ℂ}
    (hu : u ∈ ⨆ i, typeSubmodule ι (ρ i).2) :
    ∃ V : Submodule ℂ (G → ℂ), FiniteDimensional ℂ V ∧ u ∈ V ∧ ∀ k : H, ∀ v ∈ V, (fun x => v (x * ι k)) ∈ V := by
  refine Submodule.iSup_induction _ (motive := fun u => ∃ V : Submodule ℂ (G → ℂ), FiniteDimensional ℂ V ∧ u ∈ V ∧
      ∀ k : H, ∀ v ∈ V, (fun x => v (x * ι k)) ∈ V) hu ?_ ?_ ?_
  · intro i u hu
    exact exists_finiteDimensional_of_mem_typeSubmodule ι (ρ i).2 hu
  · exact ⟨⊥, inferInstance, Submodule.zero_mem _, fun k v hv => by
      rw [Submodule.mem_bot] at hv ⊢
      subst hv
      rfl⟩
  · rintro f g ⟨V₁, h₁, hf, hV₁⟩ ⟨V₂, h₂, hg, hV₂⟩
    refine ⟨V₁ ⊔ V₂, Submodule.finiteDimensional_sup V₁ V₂, Submodule.add_mem_sup hf hg, ?_⟩
    intro k v hv
    obtain ⟨v₁, hv₁, v₂, hv₂, rfl⟩ := Submodule.mem_sup.1 hv
    exact Submodule.add_mem_sup (hV₁ k v₁ hv₁) (hV₂ k v₂ hv₂)

private def invMap : (G → ℂ) →ₗ[ℂ] (G → ℂ) where
  toFun f := fun x => f x⁻¹
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private theorem invMap_apply (f : G → ℂ) (x : G) : invMap f x = f x⁻¹ := rfl

private theorem finiteDimensional_span_leftTranslates (ι : H →* G) (f : G → ℂ) (V : Submodule ℂ (G → ℂ))
    [FiniteDimensional ℂ V] (hf : invMap f ∈ V) (hV : ∀ k : H, ∀ v ∈ V, (fun x => v (x * ι k)) ∈ V) :
    FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k : H => fun y => f ((ι k)⁻¹ * y))) := by
  have hle : Submodule.span ℂ (Set.range fun k : H => fun y => f ((ι k)⁻¹ * y)) ≤ V.map (invMap (G := G)) := by
    rw [Submodule.span_le]
    rintro _ ⟨k, rfl⟩
    refine ⟨fun x => invMap f (x * ι k), hV k _ hf, ?_⟩
    funext y
    simp only [invMap_apply, mul_inv_rev, inv_inv]
  exact Submodule.finiteDimensional_of_le hle

end

section

variable (F : Type) [Field F] [NumberField F]

private theorem finiteDimensional_span_leftTranslates_of_isArchBiFinite (w : InfinitePlace F)
    {tys : ArchTypeFamily F} {f : AdelicGL2 (𝓞 F) F → ℂ} (hf : IsArchBiFinite F tys f) :
    FiniteDimensional ℂ (Submodule.span ℂ
      (Set.range fun k : rowIsometrySubgroup₀ w.Completion => fun y => f ((rowIsometryInclAt₀ F w k)⁻¹ * y))) := by
  have hw : (fun x => f x⁻¹) ∈ ⨆ i : Fin (tys.card w), archTypeSubmoduleAt F w (tys.rep w i) :=
    (Submodule.mem_iInf _).1 hf.1 w
  obtain ⟨V, hV, hmem, hstab⟩ := exists_finiteDimensional_of_mem_iSup (rowIsometryInclAt₀ F w)
    (fun i => ⟨(tys.rep w i).n, (tys.rep w i).ρ⟩) hw
  haveI := hV
  exact finiteDimensional_span_leftTranslates (rowIsometryInclAt₀ F w) f V hmem hstab

end

end TranslateHull

namespace RotationSpan

open NumberField NumberField.AdelicHaar NumberField.AdelicLevel MeasureTheory
p2m_open "AutomorphicForm~continuous_unipotentGL2~isIsotypicCuspFormAt_of_mem_isotypicCuspSubmodule"

variable (F : Type) [Field F] [NumberField F]

private theorem rightConv_mul_right (φ f : AdelicGL2 (𝓞 F) F → ℂ) (k g : AdelicGL2 (𝓞 F) F) :
    rightConv F φ f (g * k) = rightConv F φ (fun y => f (k⁻¹ * y)) g := by
  letI : MeasurableSpace (AdelicGL2 (𝓞 F) F) := glBorel (Fin 2) (𝓞 F) F
  haveI : BorelSpace (AdelicGL2 (𝓞 F) F) := borelSpace_glBorel (Fin 2) (𝓞 F) F
  haveI : (adelicGLHaar (Fin 2) (𝓞 F) F).IsHaarMeasure := isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 F) F
  rw [rightConv_apply, rightConv_apply]
  have key : (fun x => φ (g * k * x) * f x) =
      fun x => (fun y => φ (g * y) * f (k⁻¹ * y)) (k * x) := by
    funext x
    simp only [mul_assoc, inv_mul_cancel_left]
  rw [key]
  exact MeasureTheory.integral_mul_left_eq_self (fun y => φ (g * y) * f (k⁻¹ * y)) k

private theorem integrable_rightConv_integrand (φ : AdelicGL2 (𝓞 F) F → ℂ) (hφ : Continuous φ)
    (f : AdelicGL2 (𝓞 F) F → ℂ) (hf : Continuous f) (hfc : HasCompactSupport f) (g : AdelicGL2 (𝓞 F) F) :
    letI : MeasurableSpace (AdelicGL2 (𝓞 F) F) := glBorel (Fin 2) (𝓞 F) F
    Integrable (fun x => φ (g * x) * f x) (adelicGLHaar (Fin 2) (𝓞 F) F) := by
  letI : MeasurableSpace (AdelicGL2 (𝓞 F) F) := glBorel (Fin 2) (𝓞 F) F
  haveI : BorelSpace (AdelicGL2 (𝓞 F) F) := borelSpace_glBorel (Fin 2) (𝓞 F) F
  haveI : (adelicGLHaar (Fin 2) (𝓞 F) F).IsHaarMeasure := isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 F) F
  have hcont : Continuous fun x => φ (g * x) * f x := (hφ.comp (continuous_const_mul g)).mul hf
  have hsupp : HasCompactSupport fun x => φ (g * x) * f x := hfc.mul_left
  exact hcont.integrable_of_hasCompactSupport hsupp

private theorem rightConv_mem_span {n : ℕ} (φ : AdelicGL2 (𝓞 F) F → ℂ) (hφ : Continuous φ)
    (fs : Fin n → AdelicGL2 (𝓞 F) F → ℂ) (hfs : ∀ i, Continuous (fs i)) (hfsc : ∀ i, HasCompactSupport (fs i))
    (f : AdelicGL2 (𝓞 F) F → ℂ) (hf : f ∈ Submodule.span ℂ (Set.range fs)) :
    rightConv F φ f ∈ Submodule.span ℂ (Set.range fun i => rightConv F φ (fs i)) := by
  letI : MeasurableSpace (AdelicGL2 (𝓞 F) F) := glBorel (Fin 2) (𝓞 F) F
  refine (Submodule.span_induction
    (p := fun f _ => (∀ g, Integrable (fun x => φ (g * x) * f x) (adelicGLHaar (Fin 2) (𝓞 F) F)) ∧
      rightConv F φ f ∈ Submodule.span ℂ (Set.range fun i => rightConv F φ (fs i)))
    ?_ ?_ ?_ ?_ hf).2
  · rintro _ ⟨i, rfl⟩
    exact ⟨fun g => integrable_rightConv_integrand F φ hφ (fs i) (hfs i) (hfsc i) g,
      Submodule.subset_span ⟨i, rfl⟩⟩
  · refine ⟨fun g => ?_, ?_⟩
    · have e : (fun x => φ (g * x) * (0 : AdelicGL2 (𝓞 F) F → ℂ) x) = fun _ => (0 : ℂ) := by
        funext x
        simp
      rw [e]
      exact integrable_zero _ _ _
    · have e : rightConv F φ (0 : AdelicGL2 (𝓞 F) F → ℂ) = 0 := by
        funext g
        simp [rightConv]
      rw [e]
      exact Submodule.zero_mem _
  · rintro f₁ f₂ - - ⟨h₁, m₁⟩ ⟨h₂, m₂⟩
    refine ⟨fun g => ?_, ?_⟩
    · have e : (fun x => φ (g * x) * (f₁ + f₂) x) = fun x => φ (g * x) * f₁ x + φ (g * x) * f₂ x := by
        funext x
        simp only [Pi.add_apply, mul_add]
      rw [e]
      exact (h₁ g).add (h₂ g)
    · have e : rightConv F φ (f₁ + f₂) = rightConv F φ f₁ + rightConv F φ f₂ := by
        funext g
        rw [Pi.add_apply, rightConv_apply, rightConv_apply, rightConv_apply]
        simp only [Pi.add_apply, mul_add]
        exact MeasureTheory.integral_add (h₁ g) (h₂ g)
      rw [e]
      exact Submodule.add_mem _ m₁ m₂
  · rintro a f₁ - ⟨h₁, m₁⟩
    refine ⟨fun g => ?_, ?_⟩
    · have e : (fun x => φ (g * x) * (a • f₁) x) = fun x => a * (φ (g * x) * f₁ x) := by
        funext x
        simp only [Pi.smul_apply, smul_eq_mul]
        ring
      rw [e]
      exact (h₁ g).const_mul a
    · have e : rightConv F φ (a • f₁) = a • rightConv F φ f₁ := by
        funext g
        rw [Pi.smul_apply, smul_eq_mul, rightConv_apply, rightConv_apply, ← MeasureTheory.integral_const_mul]
        congr 1
        funext x
        simp only [Pi.smul_apply, smul_eq_mul]
        ring
      rw [e]
      exact Submodule.smul_mem _ a m₁

private theorem hasCompactSupport_const_smul {X : Type} [TopologicalSpace X] (c : ℂ) {f : X → ℂ}
    (hf : HasCompactSupport f) : HasCompactSupport (c • f) :=
  hf.comp_left (g := fun z : ℂ => c * z) (mul_zero c)

private def ccSubmodule : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ) where
  carrier := {f | Continuous f ∧ HasCompactSupport f}
  add_mem' := fun ⟨hf, hfc⟩ ⟨hg, hgc⟩ => ⟨hf.add hg, hfc.add hgc⟩
  zero_mem' := ⟨continuous_const, HasCompactSupport.zero⟩
  smul_mem' := fun c _ ⟨hf, hfc⟩ => ⟨hf.const_smul c, hasCompactSupport_const_smul c hfc⟩

private theorem mem_ccSubmodule {f : AdelicGL2 (𝓞 F) F → ℂ} (hf : f ∈ ccSubmodule F) :
    Continuous f ∧ HasCompactSupport f := hf

private theorem support_mul_inv_left {α : AdelicGL2 (𝓞 F) F → ℂ} {U₀ : Subgroup (AdelicGL2 (𝓞 F) F)}
    (hsupp : ∀ x, α x ≠ 0 → ∃ a k : AdelicGL2 (𝓞 F) F, glFin (𝓞 F) F a = 1 ∧ k ∈ U₀ ∧ x = a * k)
    {t : AdelicGL2 (𝓞 F) F} (ht : glFin (𝓞 F) F t = 1) :
    ∀ x, (fun y => α (t⁻¹ * y)) x ≠ 0 →
      ∃ a k : AdelicGL2 (𝓞 F) F, glFin (𝓞 F) F a = 1 ∧ k ∈ U₀ ∧ x = a * k := by
  intro x hx
  obtain ⟨a, k, ha, hk, hx'⟩ := hsupp (t⁻¹ * x) hx
  refine ⟨t * a, k, ?_, hk, ?_⟩
  · rw [map_mul, ht, ha, one_mul]
  · rw [mul_assoc, ← hx', mul_inv_cancel_left]

private theorem rightTranslate_rightConv_eq (ψ α : AdelicGL2 (𝓞 F) F → ℂ) (t : AdelicGL2 (𝓞 F) F) :
    CuspidalConstituent.rightTranslate F t (rightConv F ψ α) = rightConv F ψ (fun y => α (t⁻¹ * y)) := by
  funext x
  exact rightConv_mul_right F ψ α t x

private theorem exists_rotationSpan {w : InfinitePlace F} (hw : w.IsReal) (ψ : AdelicGL2 (𝓞 F) F → ℂ)
    (hψ : Continuous ψ) (α : AdelicGL2 (𝓞 F) F → ℂ) (hα : IsFactorizableTestFn F α)
    [hWfin : FiniteDimensional ℂ (Submodule.span ℂ
      (Set.range fun r : rowIsometrySubgroup₀ w.Completion => fun y => α ((rowIsometryInclAt₀ F w r)⁻¹ * y)))]
    (U₀ : Subgroup (AdelicGL2 (𝓞 F) F))
    (hsupp : ∀ x, α x ≠ 0 → ∃ a k : AdelicGL2 (𝓞 F) F, glFin (𝓞 F) F a = 1 ∧ k ∈ U₀ ∧ x = a * k)
    (hne : rightConv F ψ α ≠ 0)
    (I : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ))
    (hI : ∀ t : AdelicGL2 (𝓞 F) F → ℂ, IsFactorizableTestFn F t →
      (∀ x, t x ≠ 0 → ∃ a k : AdelicGL2 (𝓞 F) F, glFin (𝓞 F) F a = 1 ∧ k ∈ U₀ ∧ x = a * k) → rightConv F ψ t ∈ I)
    (V : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ)) (hαV : rightConv F ψ α ∈ V)
    (hV : ∀ φ ∈ V, ∀ r : rowIsometrySubgroup₀ w.Completion,
      CuspidalConstituent.rightTranslate F (rowIsometryInclAt₀ F w r) φ ∈ V)
    (hsm : ∀ t : AdelicGL2 (𝓞 F) F → ℂ, IsFactorizableTestFn F t → IsArchSmoothAt hw (rightConv F ψ t)) :
    ∃ U : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ), FiniteDimensional ℂ U ∧ U ≠ ⊥ ∧ U ≤ I ∧ U ≤ V ∧
      (∀ φ ∈ U, IsArchSmoothAt hw φ) ∧
      ∀ φ ∈ U, ∀ r : rowIsometrySubgroup₀ w.Completion,
        CuspidalConstituent.rightTranslate F (rowIsometryInclAt₀ F w r) φ ∈ U := by
  set W : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ) := Submodule.span ℂ
    (Set.range fun r : rowIsometrySubgroup₀ w.Completion => fun y => α ((rowIsometryInclAt₀ F w r)⁻¹ * y)) with hWdef
  have hαr : ∀ r : rowIsometrySubgroup₀ w.Completion,
      IsFactorizableTestFn F (fun y => α ((rowIsometryInclAt₀ F w r)⁻¹ * y)) := fun r =>
    AutomorphicForm.isFactorizableTestFn_comp_inv_mul_of_isFactorizableTestFn F α hα _
  have hWcc : W ≤ ccSubmodule F := by
    rw [hWdef, Submodule.span_le]
    rintro _ ⟨r, rfl⟩
    exact (AutomorphicForm.continuous_and_hasCompactSupport_of_isFactorizableTestFn F _ (hαr r) :
      Continuous _ ∧ HasCompactSupport _)
  refine ⟨Submodule.span ℂ (Set.range fun r : rowIsometrySubgroup₀ w.Completion =>
    CuspidalConstituent.rightTranslate F (rowIsometryInclAt₀ F w r) (rightConv F ψ α)), ?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    obtain ⟨S, hSfin, hS⟩ := Submodule.fg_def.1 ((Submodule.fg_iff_finiteDimensional _).2 hWfin)
    obtain ⟨n, fs, hfs⟩ := hSfin.fin_embedding
    have hmemS : ∀ i, (fs i : AdelicGL2 (𝓞 F) F → ℂ) ∈ W := fun i => by
      rw [← hS]
      refine Submodule.subset_span ?_
      rw [← hfs]
      exact Set.mem_range_self i
    have hle : Submodule.span ℂ (Set.range fun r : rowIsometrySubgroup₀ w.Completion =>
        CuspidalConstituent.rightTranslate F (rowIsometryInclAt₀ F w r) (rightConv F ψ α))
        ≤ Submodule.span ℂ (Set.range fun i => rightConv F ψ (fs i)) := by
      rw [Submodule.span_le]
      rintro _ ⟨r, rfl⟩
      beta_reduce
      rw [rightTranslate_rightConv_eq]
      refine rightConv_mem_span F ψ hψ (fun i => fs i) (fun i => (mem_ccSubmodule F (hWcc (hmemS i))).1)
        (fun i => (mem_ccSubmodule F (hWcc (hmemS i))).2) _ ?_
      have hr : (fun y => α ((rowIsometryInclAt₀ F w r)⁻¹ * y)) ∈ W := Submodule.subset_span ⟨r, rfl⟩
      rw [← hS, ← hfs] at hr
      exact hr
    haveI : FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun i => rightConv F ψ (fs i))) :=
      FiniteDimensional.span_of_finite ℂ (Set.finite_range _)
    exact Submodule.finiteDimensional_of_le hle
  ·
    intro hbot
    have h1 : CuspidalConstituent.rightTranslate F (rowIsometryInclAt₀ F w 1) (rightConv F ψ α) ∈
        Submodule.span ℂ (Set.range fun r : rowIsometrySubgroup₀ w.Completion =>
          CuspidalConstituent.rightTranslate F (rowIsometryInclAt₀ F w r) (rightConv F ψ α)) :=
      Submodule.subset_span ⟨1, rfl⟩
    have e : CuspidalConstituent.rightTranslate F 1 (rightConv F ψ α) = rightConv F ψ α := by
      funext x
      rw [CuspidalConstituent.rightTranslate_apply, mul_one]
    rw [hbot, Submodule.mem_bot, map_one, e] at h1
    exact hne h1
  · rw [Submodule.span_le]
    rintro _ ⟨r, rfl⟩
    beta_reduce
    rw [rightTranslate_rightConv_eq]
    exact hI _ (hαr r) (support_mul_inv_left F hsupp (glFin_rowIsometryInclAt₀ F w r))
  · rw [Submodule.span_le]
    rintro _ ⟨r, rfl⟩
    exact hV _ hαV r
  · intro φ hφ
    have h0 : IsArchSmoothAt hw (0 : AdelicGL2 (𝓞 F) F → ℂ) := by
      have h := (hsm α hα).smul 0
      rwa [zero_smul] at h
    refine Submodule.span_induction (p := fun φ _ => IsArchSmoothAt hw φ) ?_ h0 ?_ ?_ hφ
    · rintro _ ⟨r, rfl⟩
      beta_reduce
      rw [rightTranslate_rightConv_eq]
      exact hsm _ (hαr r)
    · intro φ₁ φ₂ _ _ h₁ h₂
      exact h₁.add h₂
    · intro c φ₁ _ h₁
      exact h₁.smul c
  · intro φ hφ r
    refine Submodule.span_induction
      (p := fun φ _ => CuspidalConstituent.rightTranslate F (rowIsometryInclAt₀ F w r) φ ∈ Submodule.span ℂ
        (Set.range fun r : rowIsometrySubgroup₀ w.Completion =>
          CuspidalConstituent.rightTranslate F (rowIsometryInclAt₀ F w r) (rightConv F ψ α))) ?_ ?_ ?_ ?_ hφ
    · rintro _ ⟨r', rfl⟩
      beta_reduce
      rw [CuspidalConstituent.rightTranslate_rightTranslate, ← map_mul]
      exact Submodule.subset_span ⟨r * r', rfl⟩
    · beta_reduce
      rw [CuspidalConstituent.rightTranslate_zero]
      exact Submodule.zero_mem _
    · intro φ₁ φ₂ _ _ h₁ h₂
      beta_reduce at h₁ h₂ ⊢
      rw [CuspidalConstituent.rightTranslate_add]
      exact Submodule.add_mem _ h₁ h₂
    · intro c φ₁ _ h₁
      beta_reduce at h₁ ⊢
      rw [CuspidalConstituent.rightTranslate_smul]
      exact Submodule.smul_mem _ c h₁

end RotationSpan

namespace RotationWeight

open scoped Real Topology
p2m_open "AutomorphicForm~continuous_unipotentGL2~isIsotypicCuspFormAt_of_mem_isotypicCuspSubmodule Matrix Filter"
open AutomorphicForm.CuspidalConstituent
open NumberField IsDedekindDomain NumberField.InfinitePlace NumberField.InfinitePlace.Completion

section

private def rotM (θ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![Real.cos θ, Real.sin θ; -Real.sin θ, Real.cos θ]

private theorem det_rotM (θ : ℝ) : (rotM θ).det = 1 := by
  rw [rotM, Matrix.det_fin_two_of]
  linear_combination Real.cos_sq_add_sin_sq θ

private def rot (θ : ℝ) : GL (Fin 2) ℝ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (rotM θ) (by rw [det_rotM]; exact one_ne_zero)

private theorem rot_coe (θ : ℝ) : ((rot θ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = rotM θ := rfl

private theorem rot_zero : rot 0 = 1 := by
  apply Units.ext
  rw [rot_coe, Units.val_one]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [rotM]

private theorem rot_two_pi : rot (2 * π) = 1 := by
  apply Units.ext
  rw [rot_coe, Units.val_one]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [rotM]

private theorem rot_add (s t : ℝ) : rot (s + t) = rot s * rot t := by
  apply Units.ext
  rw [Units.val_mul, rot_coe, rot_coe, rot_coe]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rotM, Matrix.mul_apply, Fin.sum_univ_two, Real.cos_add, Real.sin_add] <;> ring

private theorem rot_mem (θ : ℝ) : rot θ ∈ rowIsometrySubgroup₀ ℝ := by
  have hdet : ((rot θ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ).det = 1 := by rw [rot_coe, det_rotM]
  rw [mem_rowIsometrySubgroup₀_iff]
  refine ⟨hdet, ?_, ?_⟩
  · rw [hdet, norm_one]
  · intro x y
    simp only [rot_coe, rotM, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one, Real.norm_eq_abs, sq_abs]
    linear_combination (x ^ 2 + y ^ 2) * Real.cos_sq_add_sin_sq θ

private theorem firstRowℂ_rot (θ : ℝ) : firstRowℂ (rot θ) = Complex.exp ((θ : ℂ) * Complex.I) := by
  apply Complex.ext
  · simp [firstRowℂ, rot_coe, rotM, Complex.exp_ofReal_mul_I_re]
  · simp [firstRowℂ, rot_coe, rotM, Complex.exp_ofReal_mul_I_im]

private theorem exists_rot_eq {k : GL (Fin 2) ℝ} (hk : k ∈ rowIsometrySubgroup₀ ℝ) : ∃ θ : ℝ, rot θ = k := by
  obtain ⟨h10, h11, -⟩ := entries_of_mem_rowIsometrySubgroup₀ hk
  have hz : firstRowℂ k ≠ 0 := firstRowℂ_ne_zero_of_mem hk
  have hn : ‖firstRowℂ k‖ = 1 := by
    have h := normSq_firstRowℂ_of_mem hk
    rw [Complex.normSq_eq_norm_sq] at h
    nlinarith [norm_nonneg (firstRowℂ k)]
  have hcos : Real.cos (Complex.arg (firstRowℂ k)) = (k : Matrix (Fin 2) (Fin 2) ℝ) 0 0 := by
    rw [Complex.cos_arg hz, hn, div_one]; rfl
  have hsin : Real.sin (Complex.arg (firstRowℂ k)) = (k : Matrix (Fin 2) (Fin 2) ℝ) 0 1 := by
    rw [Complex.sin_arg, hn, div_one]; rfl
  refine ⟨Complex.arg (firstRowℂ k), Units.ext ?_⟩
  rw [rot_coe]
  ext i j
  fin_cases i <;> fin_cases j
  · simpa [rotM] using hcos
  · simpa [rotM] using hsin
  · simp only [rotM, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one, Fin.zero_eta, Fin.mk_one, Fin.isValue]
    rw [hsin, h10]
  · simp only [rotM, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one, Fin.mk_one, Fin.isValue]
    rw [hcos, h11]

private theorem differentiableAt_rot_entries (θ₀ : ℝ) :
    DifferentiableAt ℝ (fun θ : ℝ => (Matrix.of.symm ((rot θ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) :
      Fin 2 → Fin 2 → ℝ)) θ₀ := by
  refine differentiableAt_pi.2 fun i => differentiableAt_pi.2 fun j => ?_
  fin_cases i <;> fin_cases j <;> simp [rot_coe, rotM]

end

section

variable {K : Type} [Field K] [NumberField K] {w : InfinitePlace K}

private theorem det_of_symm_one : (Matrix.of (Matrix.of.symm (1 : Matrix (Fin 2) (Fin 2) ℝ))).det ≠ 0 := by
  rw [Equiv.apply_symm_apply, Matrix.det_one]
  exact one_ne_zero

private theorem archRealGLAt_eq_archRealLiftAt (hw : w.IsReal) (m : GL (Fin 2) ℝ) :
    archRealGLAt hw m = archRealLiftAt hw (Matrix.of.symm (m : Matrix (Fin 2) (Fin 2) ℝ)) := by
  have h := archRealLiftAt_mul_archRealGLAt hw det_of_symm_one m
  rw [archRealLiftAt_of_symm_one, one_mul, Equiv.apply_symm_apply, one_mul] at h
  exact h

omit [NumberField K] in

private theorem symm_mem_rowIsometrySubgroup₀ (hw : w.IsReal) (k : rowIsometrySubgroup₀ ℝ) :
    glEquivOfRingEquiv (ringEquivRealOfIsReal hw).symm (k : GL (Fin 2) ℝ) ∈ rowIsometrySubgroup₀ w.Completion :=
  map_mem_rowIsometrySubgroup₀_of_normPreserving _
    (fun x => by
      rw [← norm_ringEquivRealOfIsReal hw ((ringEquivRealOfIsReal hw).symm x), RingEquiv.apply_symm_apply])
    _ k.2

private def rotAt (hw : w.IsReal) (θ : ℝ) : rowIsometrySubgroup₀ w.Completion :=
  ⟨_, symm_mem_rowIsometrySubgroup₀ hw ⟨rot θ, rot_mem θ⟩⟩

private theorem rowIsometryInclAt₀_rotAt (hw : w.IsReal) (θ : ℝ) :
    rowIsometryInclAt₀ K w (rotAt hw θ) = archRealGLAt hw (rot θ) := rfl

private theorem differentiableAt_orbit (hw : w.IsReal) {ψ : AdelicGL2 (𝓞 K) K → ℂ} (hψ : IsArchSmoothAt hw ψ)
    (x : AdelicGL2 (𝓞 K) K) (θ₀ : ℝ) : DifferentiableAt ℝ (fun θ : ℝ => ψ (x * archRealGLAt hw (rot θ))) θ₀ := by
  have hfun : (fun θ : ℝ => ψ (x * archRealGLAt hw (rot θ))) =
      (fun e : Fin 2 → Fin 2 → ℝ => ψ (x * archRealLiftAt hw e)) ∘
        fun θ : ℝ => (Matrix.of.symm ((rot θ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) : Fin 2 → Fin 2 → ℝ) := by
    funext θ
    simp only [Function.comp_apply, archRealGLAt_eq_archRealLiftAt hw]
  have hmem : (Matrix.of.symm ((rot θ₀ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) : Fin 2 → Fin 2 → ℝ) ∈
      {e : Fin 2 → Fin 2 → ℝ | (Matrix.of e).det ≠ 0} := by
    show (Matrix.of (Matrix.of.symm _)).det ≠ 0
    rw [Equiv.apply_symm_apply, rot_coe, det_rotM]
    exact one_ne_zero
  rw [hfun]
  exact (((hψ x).differentiableOn (by simp) _ hmem).differentiableAt
    (isOpen_setOf_det_ne_zero.mem_nhds hmem)).comp θ₀ (differentiableAt_rot_entries θ₀)

private def rotDeriv (hw : w.IsReal) (ψ : AdelicGL2 (𝓞 K) K → ℂ) : AdelicGL2 (𝓞 K) K → ℂ :=
  fun x => deriv (fun θ : ℝ => ψ (x * archRealGLAt hw (rot θ))) 0

private theorem hasDerivAt_orbit_zero (hw : w.IsReal) {ψ : AdelicGL2 (𝓞 K) K → ℂ} (hψ : IsArchSmoothAt hw ψ)
    (x : AdelicGL2 (𝓞 K) K) :
    HasDerivAt (fun θ : ℝ => ψ (x * archRealGLAt hw (rot θ))) (rotDeriv hw ψ x) 0 :=
  (differentiableAt_orbit hw hψ x 0).hasDerivAt

private theorem hasDerivAt_orbit (hw : w.IsReal) {ψ : AdelicGL2 (𝓞 K) K → ℂ} (hψ : IsArchSmoothAt hw ψ)
    (x : AdelicGL2 (𝓞 K) K) (θ₀ : ℝ) :
    HasDerivAt (fun θ : ℝ => ψ (x * archRealGLAt hw (rot θ))) (rotDeriv hw ψ (x * archRealGLAt hw (rot θ₀))) θ₀ := by
  have hfun : (fun θ : ℝ => ψ (x * archRealGLAt hw (rot θ))) =
      (fun s : ℝ => ψ (x * archRealGLAt hw (rot θ₀) * archRealGLAt hw (rot s))) ∘ fun θ : ℝ => θ - θ₀ := by
    funext θ
    show ψ (x * archRealGLAt hw (rot θ)) = ψ (x * archRealGLAt hw (rot θ₀) * archRealGLAt hw (rot (θ - θ₀)))
    rw [mul_assoc, ← map_mul, ← rot_add, show θ₀ + (θ - θ₀) = θ by ring]
  have hpt : HasDerivAt (fun s : ℝ => ψ (x * archRealGLAt hw (rot θ₀) * archRealGLAt hw (rot s)))
      (rotDeriv hw ψ (x * archRealGLAt hw (rot θ₀))) (θ₀ - θ₀) := by
    rw [sub_self]
    exact hasDerivAt_orbit_zero hw hψ _
  rw [hfun]
  have h := hpt.scomp (h := fun θ : ℝ => θ - θ₀) θ₀ ((hasDerivAt_sub_const_iff θ₀).2 (hasDerivAt_id θ₀))
  rw [one_smul] at h
  exact h

private theorem rotDeriv_add (hw : w.IsReal) {ψ χ : AdelicGL2 (𝓞 K) K → ℂ} (hψ : IsArchSmoothAt hw ψ)
    (hχ : IsArchSmoothAt hw χ) : rotDeriv hw (ψ + χ) = rotDeriv hw ψ + rotDeriv hw χ := by
  funext x
  exact ((hasDerivAt_orbit_zero hw hψ x).add (hasDerivAt_orbit_zero hw hχ x)).deriv

private theorem rotDeriv_smul (hw : w.IsReal) (c : ℂ) (ψ : AdelicGL2 (𝓞 K) K → ℂ) :
    rotDeriv hw (c • ψ) = c • rotDeriv hw ψ := by
  funext x
  exact deriv_const_mul_field c

end

section

variable {K : Type} [Field K] [NumberField K] {w : InfinitePlace K}

private theorem hasDerivAt_cexp_mul (μ : ℂ) (θ : ℝ) :
    HasDerivAt (fun θ : ℝ => Complex.exp (μ * θ)) (Complex.exp (μ * θ) * μ) θ := by
  have h : HasDerivAt (fun θ : ℝ => μ * (θ : ℂ)) (μ * 1) θ := (HasDerivAt.ofReal_comp (hasDerivAt_id θ)).const_mul μ
  simpa using h.cexp

private theorem apply_mul_rot_of_rotDeriv_eq (hw : w.IsReal) {ψ : AdelicGL2 (𝓞 K) K → ℂ} (hψ : IsArchSmoothAt hw ψ)
    {μ : ℂ} (hμ : rotDeriv hw ψ = μ • ψ) (g : AdelicGL2 (𝓞 K) K) (θ : ℝ) :
    ψ (g * archRealGLAt hw (rot θ)) = Complex.exp (μ * θ) * ψ g := by
  set F : ℝ → ℂ := fun θ => ψ (g * archRealGLAt hw (rot θ)) with hF
  have hF' : ∀ θ : ℝ, HasDerivAt F (μ * F θ) θ := by
    intro θ
    have h := hasDerivAt_orbit hw hψ g θ
    rw [hμ, Pi.smul_apply, smul_eq_mul] at h
    exact h
  set H : ℝ → ℂ := fun θ => Complex.exp (-μ * θ) * F θ with hH
  have hH' : ∀ θ : ℝ, HasDerivAt H 0 θ := by
    intro θ
    refine ((hasDerivAt_cexp_mul (-μ) θ).mul (hF' θ)).congr_deriv ?_
    ring
  have hconst := is_const_of_deriv_eq_zero (fun θ => (hH' θ).differentiableAt) (fun θ => (hH' θ).deriv) θ 0
  have h0 : H 0 = ψ g := by
    simp only [hH, hF, Complex.ofReal_zero, mul_zero, Complex.exp_zero, one_mul, rot_zero, map_one, mul_one]
  rw [h0] at hconst
  calc F θ = Complex.exp (μ * θ) * (Complex.exp (-μ * θ) * F θ) := by
        rw [← mul_assoc, ← Complex.exp_add]
        simp
    _ = Complex.exp (μ * θ) * ψ g := by rw [← hconst]

private theorem exists_int_eq_of_rotDeriv_eq (hw : w.IsReal) {ψ : AdelicGL2 (𝓞 K) K → ℂ} (hψ : IsArchSmoothAt hw ψ)
    (hψ0 : ψ ≠ 0) {μ : ℂ} (hμ : rotDeriv hw ψ = μ • ψ) : ∃ k : ℤ, μ = k * Complex.I := by
  obtain ⟨g, hg⟩ := Function.ne_iff.1 hψ0
  have h := apply_mul_rot_of_rotDeriv_eq hw hψ hμ g (2 * π)
  rw [rot_two_pi, map_one, mul_one] at h
  have hexp : Complex.exp (μ * ((2 * π : ℝ) : ℂ)) = 1 := by
    have h' : (Complex.exp (μ * ((2 * π : ℝ) : ℂ)) - 1) * ψ g = 0 := by linear_combination -h
    rcases mul_eq_zero.1 h' with h'' | h''
    · exact sub_eq_zero.1 h''
    · exact absurd h'' hg
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.1 hexp
  refine ⟨n, ?_⟩
  have hπ : (2 * (π : ℂ)) ≠ 0 := by simp [Real.pi_ne_zero]
  apply mul_right_cancel₀ hπ
  push_cast at hn
  linear_combination hn

end

section

variable {K : Type} [Field K] [NumberField K] {w : InfinitePlace K}

omit [NumberField K] in
private theorem archWeightCharℝ_apply_coe (n : ℤ) (k : rowIsometrySubgroup₀ ℝ) :
    (archWeightCharℝ n k : ℂ) = firstRowℂ (k : GL (Fin 2) ℝ) ^ n := by
  simp only [archWeightCharℝ, MonoidHom.coe_comp, Function.comp_apply, zpowGroupHom_apply,
    Units.val_zpow_eq_zpow_val]
  rfl

omit [NumberField K] in

private theorem mem_rowIsometrySubgroup₀_real_of_mem (hw : w.IsReal) (k : rowIsometrySubgroup₀ w.Completion) :
    glEquivOfRingEquiv (ringEquivRealOfIsReal hw) (k : GL (Fin 2) w.Completion) ∈ rowIsometrySubgroup₀ ℝ :=
  map_mem_rowIsometrySubgroup₀_of_normPreserving _ (norm_ringEquivRealOfIsReal hw) _ k.2

omit [NumberField K] in
private theorem archWeightCharAt_apply_coe (hw : w.IsReal) (m : ℤ) (k : rowIsometrySubgroup₀ w.Completion) :
    (archWeightCharAt hw m k : ℂ)
      = firstRowℂ (glEquivOfRingEquiv (ringEquivRealOfIsReal hw) (k : GL (Fin 2) w.Completion)) ^ m := by
  have h := archWeightCharℝ_apply_coe m
    (rowIsometrySubgroup₀Map (ringEquivRealOfIsReal hw) (norm_ringEquivRealOfIsReal hw) k)
  simp only [archWeightCharAt, archWeightOneAt, archWeightCharℝ, MonoidHom.comp_apply] at h ⊢
  exact h

private theorem hasArchCharacterAt₀_of_rotDeriv_eq (hw : w.IsReal) {ψ : AdelicGL2 (𝓞 K) K → ℂ}
    (hψ : IsArchSmoothAt hw ψ) (k : ℤ) (hμ : rotDeriv hw ψ = ((k : ℂ) * Complex.I) • ψ) :
    HasArchCharacterAt₀ K w (archWeightCharAt hw k) ψ := by
  intro r x
  obtain ⟨θ, hθ⟩ := exists_rot_eq (mem_rowIsometrySubgroup₀_real_of_mem hw r)
  have hι : archRealGLAt hw (rot θ) = adelicArchGLInclAt K w (r : GL (Fin 2) w.Completion) := by
    rw [hθ]
    exact archRealGLAt_glEquivOfRingEquiv hw _
  rw [archWeightCharAt_apply_coe, ← hθ, ← hι, apply_mul_rot_of_rotDeriv_eq hw hψ hμ x θ, firstRowℂ_rot,
    ← Complex.exp_int_mul]
  congr 2
  ring

end

section

variable {K : Type} [Field K] [NumberField K] {w : InfinitePlace K}

private theorem rotDeriv_mem (hw : w.IsReal) (U : Submodule ℂ (AdelicGL2 (𝓞 K) K → ℂ)) [FiniteDimensional ℂ U]
    (hsmooth : ∀ φ ∈ U, IsArchSmoothAt hw φ)
    (hstab : ∀ φ ∈ U, ∀ r : rowIsometrySubgroup₀ w.Completion, rightTranslate K (rowIsometryInclAt₀ K w r) φ ∈ U)
    {ψ : AdelicGL2 (𝓞 K) K → ℂ} (hψ : ψ ∈ U) : rotDeriv hw ψ ∈ U := by
  have htr : ∀ θ : ℝ, (fun x => ψ (x * archRealGLAt hw (rot θ))) ∈ U := fun θ => by
    have h := hstab ψ hψ (rotAt hw θ)
    rwa [rowIsometryInclAt₀_rotAt] at h
  have hquot : ∀ θ : ℝ, (θ - 0)⁻¹ • ((fun x => ψ (x * archRealGLAt hw (rot θ))) -
      fun x => ψ (x * archRealGLAt hw (rot 0))) ∈ U :=
    fun θ => U.smul_of_tower_mem _ (U.sub_mem (htr θ) (htr 0))
  have hlim : Tendsto (fun θ : ℝ => (θ - 0)⁻¹ • ((fun x => ψ (x * archRealGLAt hw (rot θ))) -
      fun x => ψ (x * archRealGLAt hw (rot 0)))) (𝓝[≠] 0) (𝓝 (rotDeriv hw ψ)) := by
    rw [tendsto_pi_nhds]
    intro x
    have h := hasDerivAt_iff_tendsto_slope.1 (hasDerivAt_orbit_zero hw (hsmooth ψ hψ) x)
    refine h.congr fun θ => ?_
    simp only [slope, vsub_eq_sub, Pi.smul_apply, Pi.sub_apply]
  exact U.closed_of_finiteDimensional.mem_of_tendsto hlim (Eventually.of_forall hquot)

private def rotDerivOn (hw : w.IsReal) (U : Submodule ℂ (AdelicGL2 (𝓞 K) K → ℂ)) [FiniteDimensional ℂ U]
    (hsmooth : ∀ φ ∈ U, IsArchSmoothAt hw φ)
    (hstab : ∀ φ ∈ U, ∀ r : rowIsometrySubgroup₀ w.Completion, rightTranslate K (rowIsometryInclAt₀ K w r) φ ∈ U) :
    Module.End ℂ U where
  toFun ψ := ⟨rotDeriv hw ψ, rotDeriv_mem hw U hsmooth hstab ψ.2⟩
  map_add' ψ χ := Subtype.ext (rotDeriv_add hw (hsmooth ψ ψ.2) (hsmooth χ χ.2))
  map_smul' c ψ := Subtype.ext (rotDeriv_smul hw c ψ)

private theorem exists_mem_ne_zero_hasArchCharacterAt₀ (hw : w.IsReal) (U : Submodule ℂ (AdelicGL2 (𝓞 K) K → ℂ))
    [FiniteDimensional ℂ U] (hU : U ≠ ⊥) (hsmooth : ∀ φ ∈ U, IsArchSmoothAt hw φ)
    (hstab : ∀ φ ∈ U, ∀ r : rowIsometrySubgroup₀ w.Completion, rightTranslate K (rowIsometryInclAt₀ K w r) φ ∈ U) :
    ∃ φ ∈ U, φ ≠ 0 ∧ ∃ k : ℤ, HasArchCharacterAt₀ K w (archWeightCharAt hw k) φ := by
  haveI : Nontrivial U := Submodule.nontrivial_iff_ne_bot.2 hU
  obtain ⟨μ, hμ⟩ := Module.End.exists_eigenvalue (rotDerivOn hw U hsmooth hstab)
  obtain ⟨v, hv⟩ := hμ.exists_hasEigenvector
  have hv0 : (v : AdelicGL2 (𝓞 K) K → ℂ) ≠ 0 := fun h => (Module.End.hasEigenvector_iff.1 hv).2 (Subtype.ext h)
  have hvμ : rotDeriv hw (v : AdelicGL2 (𝓞 K) K → ℂ) = μ • (v : AdelicGL2 (𝓞 K) K → ℂ) :=
    congrArg Subtype.val hv.apply_eq_smul
  obtain ⟨k, rfl⟩ := exists_int_eq_of_rotDeriv_eq hw (hsmooth v v.2) hv0 hvμ
  exact ⟨v, v.2, hv0, k, hasArchCharacterAt₀_of_rotDeriv_eq hw (hsmooth v v.2) k hvμ⟩

end

end RotationWeight

namespace PredicateClosure

open IsDedekindDomain NumberField MeasureTheory
open NumberField.AdelicHaar NumberField.AdelicBox NumberField.AdelicLevel
open FLT.SmoothVectors
p2m_open "AutomorphicForm~continuous_unipotentGL2~isIsotypicCuspFormAt_of_mem_isotypicCuspSubmodule AutomorphicForm.SmoothCusp"

variable (F : Type) [Field F] [NumberField F]

section

private theorem isKfSmooth_add {φ ψ : AdelicGL2 (𝓞 F) F → ℂ} (hφ : IsKfSmooth F φ) (hψ : IsKfSmooth F ψ) :
    IsKfSmooth F (φ + ψ) := by
  unfold IsKfSmooth at hφ hψ ⊢
  rw [isSmoothVector_iff_isOpen_stabilizer] at hφ hψ ⊢
  refine Subgroup.isOpen_mono (H₁ := MulAction.stabilizer (finiteAdelicGL2Subgroup F)
    (RightTranslationFn.mk φ : RightTranslationFn (AdelicGL2 (𝓞 F) F) ℂ) ⊓
      MulAction.stabilizer (finiteAdelicGL2Subgroup F)
        (RightTranslationFn.mk ψ : RightTranslationFn (AdelicGL2 (𝓞 F) F) ℂ)) ?_ ?_
  · intro g hg
    rw [Subgroup.mem_inf, MulAction.mem_stabilizer_iff, MulAction.mem_stabilizer_iff] at hg
    rw [MulAction.mem_stabilizer_iff]
    refine RightTranslationFn.ext fun x => ?_
    have h₁ := congrArg (fun f => RightTranslationFn.toFun f x) hg.1
    have h₂ := congrArg (fun f => RightTranslationFn.toFun f x) hg.2
    change φ (x * (g : AdelicGL2 (𝓞 F) F)) = φ x at h₁
    change ψ (x * (g : AdelicGL2 (𝓞 F) F)) = ψ x at h₂
    change (φ + ψ) (x * (g : AdelicGL2 (𝓞 F) F)) = (φ + ψ) x
    simp only [Pi.add_apply, h₁, h₂]
  · rw [Subgroup.coe_inf]
    exact hφ.inter hψ

private theorem isKfSmooth_smul {φ : AdelicGL2 (𝓞 F) F → ℂ} (hφ : IsKfSmooth F φ) (c : ℂ) : IsKfSmooth F (c • φ) := by
  unfold IsKfSmooth at hφ ⊢
  rw [isSmoothVector_iff_isOpen_stabilizer] at hφ ⊢
  refine Subgroup.isOpen_mono (H₁ := MulAction.stabilizer (finiteAdelicGL2Subgroup F)
    (RightTranslationFn.mk φ : RightTranslationFn (AdelicGL2 (𝓞 F) F) ℂ)) ?_ hφ
  intro g hg
  rw [MulAction.mem_stabilizer_iff] at hg ⊢
  refine RightTranslationFn.ext fun x => ?_
  have h₁ := congrArg (fun f => RightTranslationFn.toFun f x) hg
  change φ (x * (g : AdelicGL2 (𝓞 F) F)) = φ x at h₁
  change (c • φ) (x * (g : AdelicGL2 (𝓞 F) F)) = (c • φ) x
  simp only [Pi.smul_apply, h₁]

private theorem isLsXiFunction_add {Z : Subgroup (AdeleRing (𝓞 F) F)ˣ} {ξ : Z →* ℂˣ}
    {φ ψ : AdelicGL2 (𝓞 F) F → ℂ} (hφ : IsLsXiFunction (𝓞 F) F Z ξ φ) (hψ : IsLsXiFunction (𝓞 F) F Z ξ ψ) :
    IsLsXiFunction (𝓞 F) F Z ξ (φ + ψ) :=
  ⟨fun γ g => by simp only [Pi.add_apply, hφ.left_invariant γ g, hψ.left_invariant γ g],
   fun z g => by simp only [Pi.add_apply, hφ.central_transform z g, hψ.central_transform z g, mul_add]⟩

private theorem isLsXiFunction_smul {Z : Subgroup (AdeleRing (𝓞 F) F)ˣ} {ξ : Z →* ℂˣ}
    {φ : AdelicGL2 (𝓞 F) F → ℂ} (hφ : IsLsXiFunction (𝓞 F) F Z ξ φ) (c : ℂ) :
    IsLsXiFunction (𝓞 F) F Z ξ (c • φ) :=
  ⟨fun γ g => by simp only [Pi.smul_apply, hφ.left_invariant γ g],
   fun z g => by simp only [Pi.smul_apply, hφ.central_transform z g, smul_eq_mul, mul_left_comm]⟩

private theorem isAutomorphicFnAt_add (pins : CarrierPins F) (ξ : pins.Z →* ℂˣ) {φ ψ : AdelicGL2 (𝓞 F) F → ℂ}
    (hφ : IsAutomorphicFnAt F pins ξ φ) (hψ : IsAutomorphicFnAt F pins ξ ψ) : IsAutomorphicFnAt F pins ξ (φ + ψ) := by
  have h₁ := (@lsXiMemberAt_iff (𝓞 F) F _ _ _ _ _ pins.mS pins.μ pins.Z ξ pins.D φ).mp hφ
  have h₂ := (@lsXiMemberAt_iff (𝓞 F) F _ _ _ _ _ pins.mS pins.μ pins.Z ξ pins.D ψ).mp hψ
  exact (@lsXiMemberAt_iff (𝓞 F) F _ _ _ _ _ pins.mS pins.μ pins.Z ξ pins.D (φ + ψ)).mpr
    ⟨isLsXiFunction_add F h₁.1 h₂.1, h₁.2.add h₂.2⟩

private theorem isAutomorphicFnAt_smul (pins : CarrierPins F) (ξ : pins.Z →* ℂˣ) {φ : AdelicGL2 (𝓞 F) F → ℂ}
    (hφ : IsAutomorphicFnAt F pins ξ φ) (c : ℂ) : IsAutomorphicFnAt F pins ξ (c • φ) := by
  have h₁ := (@lsXiMemberAt_iff (𝓞 F) F _ _ _ _ _ pins.mS pins.μ pins.Z ξ pins.D φ).mp hφ
  exact (@lsXiMemberAt_iff (𝓞 F) F _ _ _ _ _ pins.mS pins.μ pins.Z ξ pins.D (c • φ)).mpr
    ⟨isLsXiFunction_smul F h₁.1 c, h₁.2.const_smul c⟩

private theorem continuous_unipotentGL2 :
    Continuous (unipotentGL2 : AdeleRing (𝓞 F) F → GL (Fin 2) (AdeleRing (𝓞 F) F)) := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · refine continuous_pi fun i => continuous_pi fun j => ?_
    fin_cases i <;> fin_cases j <;> simp [unipotentGL2] <;> fun_prop
  · refine continuous_pi fun i => continuous_pi fun j => ?_
    fin_cases i <;> fin_cases j <;> simp [unipotentGL2] <;> fun_prop

private theorem integrable_constantTermIntegrand_box {φ : AdelicGL2 (𝓞 F) F → ℂ} (hφ : Continuous φ)
    (g : AdelicGL2 (𝓞 F) F) :
    Integrable[adeleBorel (𝓞 F) F] (constantTermIntegrand unipotentGL2 φ g)
      (@ProbabilityTheory.cond _ (adeleBorel (𝓞 F) F) (adelicAddHaar (𝓞 F) F) (adelicBox F)) := by
  letI := adeleBorel (𝓞 F) F
  haveI := borelSpace_adeleBorel (𝓞 F) F
  haveI := isAddHaarMeasure_adelicAddHaar (𝓞 F) F
  have hcont : Continuous (constantTermIntegrand unipotentGL2 φ g) :=
    hφ.comp ((continuous_unipotentGL2 F).mul continuous_const)
  obtain ⟨C, hC, hsub⟩ := exists_isCompact_adelicBox_subset F
  have hint : IntegrableOn (constantTermIntegrand unipotentGL2 φ g) (adelicBox F) (adelicAddHaar (𝓞 F) F) :=
    (hcont.continuousOn.integrableOn_compact hC).mono_set hsub
  rw [ProbabilityTheory.cond]
  exact hint.smul_measure (ENNReal.inv_ne_top.2 (adelicAddHaar_adelicBox_pos F).ne')

end

section

private abbrev pinsAt (D : Set (AdelicGL2 (𝓞 F) F)) (U : Ideal (𝓞 F) → Subgroup (AdelicGL2 (𝓞 F) F))
    (gen : HeightOneSpectrum (𝓞 F) → AdelicGL2 (𝓞 F) F) : CarrierPins F :=
  productionPinsOf F D U gen (adelicBox F)

variable {F}
variable {D : Set (AdelicGL2 (𝓞 F) F)} {U : Ideal (𝓞 F) → Subgroup (AdelicGL2 (𝓞 F) F)}
  {gen : HeightOneSpectrum (𝓞 F) → AdelicGL2 (𝓞 F) F} {ξ : (pinsAt F D U gen).Z →* ℂˣ} {N : Ideal (𝓞 F)}
  {S : Finset (HeightOneSpectrum (𝓞 F))} {Φ : HeckeEigensystem F ℂ}

private theorem isIsotypicCuspFormAt_add {φ ψ : AdelicGL2 (𝓞 F) F → ℂ}
    (hφ : IsIsotypicCuspFormAt F (pinsAt F D U gen) ξ N S Φ φ)
    (hψ : IsIsotypicCuspFormAt F (pinsAt F D U gen) ξ N S Φ ψ) :
    IsIsotypicCuspFormAt F (pinsAt F D U gen) ξ N S Φ (φ + ψ) where
  smoothCusp := by
    refine ⟨⟨isAutomorphicFnAt_add F _ ξ hφ.smoothCusp.1.1 hψ.smoothCusp.1.1, ?_⟩,
      isKfSmooth_add F hφ.smoothCusp.2 hψ.smoothCusp.2⟩
    exact @AutomorphicForm.IsCuspidalFn.add _ (adeleBorel (𝓞 F) F) _ _ _ unipotentGL2 φ ψ hφ.smoothCusp.1.2
      hψ.smoothCusp.1.2 (fun g => integrable_constantTermIntegrand_box F hφ.continuous g)
      (fun g => integrable_constantTermIntegrand_box F hψ.continuous g)
  continuous := hφ.continuous.add hψ.continuous
  level_invariant := fun g u hu => by
    simp only [Pi.add_apply, hφ.level_invariant g u hu, hψ.level_invariant g u hu]
  hecke_eigen := fun v hv => by
    obtain ⟨reps, hsys, hφv⟩ := hφ.hecke_eigen v hv
    obtain ⟨reps', hsys', hψv⟩ := hψ.hecke_eigen v hv
    refine ⟨reps, hsys, fun g => ?_⟩
    have hψreps : heckeCosetSum F reps ψ g = heckeCosetSum F reps' ψ g :=
      HeckeIntegralSeam.heckeCosetSum_eq_of_isHeckeCosetSystem hsys' hsys hψ.level_invariant g
    have h := congrArg₂ (· + ·) (hφv g) (hψreps.trans (hψv g))
    simp only [heckeCosetSum, Pi.add_apply, Finset.sum_add_distrib] at h ⊢
    rw [h, mul_add]
  central_eigen := fun v hv g => by
    simp only [Pi.add_apply, hφ.central_eigen v hv g, hψ.central_eigen v hv g, mul_add]

private theorem isIsotypicCuspFormAt_smul {φ : AdelicGL2 (𝓞 F) F → ℂ}
    (hφ : IsIsotypicCuspFormAt F (pinsAt F D U gen) ξ N S Φ φ) (c : ℂ) :
    IsIsotypicCuspFormAt F (pinsAt F D U gen) ξ N S Φ (c • φ) where
  smoothCusp := by
    refine ⟨⟨isAutomorphicFnAt_smul F _ ξ hφ.smoothCusp.1.1 c, ?_⟩, isKfSmooth_smul F hφ.smoothCusp.2 c⟩
    exact @AutomorphicForm.IsCuspidalFn.smul _ (adeleBorel (𝓞 F) F) _ _ _ unipotentGL2 φ hφ.smoothCusp.1.2 c
  continuous := hφ.continuous.const_smul c
  level_invariant := fun g u hu => by simp only [Pi.smul_apply, hφ.level_invariant g u hu]
  hecke_eigen := fun v hv => by
    obtain ⟨reps, hsys, hφv⟩ := hφ.hecke_eigen v hv
    refine ⟨reps, hsys, fun g => ?_⟩
    have h := hφv g
    simp only [heckeCosetSum] at h
    simp only [heckeCosetSum, Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum, h]
    ring
  central_eigen := fun v hv g => by
    simp only [Pi.smul_apply, hφ.central_eigen v hv g, smul_eq_mul, mul_left_comm]

private theorem isIsotypicCuspFormAt_zero_of {φ₀ : AdelicGL2 (𝓞 F) F → ℂ}
    (h₀ : IsIsotypicCuspFormAt F (pinsAt F D U gen) ξ N S Φ φ₀) :
    IsIsotypicCuspFormAt F (pinsAt F D U gen) ξ N S Φ 0 := by
  have h := isIsotypicCuspFormAt_smul h₀ 0
  rwa [zero_smul] at h

private theorem isIsotypicCuspFormAt_of_mem_isotypicCuspSubmodule {φ₀ : AdelicGL2 (𝓞 F) F → ℂ}
    (h₀ : IsIsotypicCuspFormAt F (pinsAt F D U gen) ξ N S Φ φ₀) {ψ : AdelicGL2 (𝓞 F) F → ℂ}
    (hψ : ψ ∈ isotypicCuspSubmodule F (pinsAt F D U gen) ξ N S Φ) :
    IsIsotypicCuspFormAt F (pinsAt F D U gen) ξ N S Φ ψ := by
  refine Submodule.span_induction (p := fun ψ _ => IsIsotypicCuspFormAt F (pinsAt F D U gen) ξ N S Φ ψ) ?_
    (isIsotypicCuspFormAt_zero_of h₀) ?_ ?_ hψ
  · intro ψ hψ
    exact hψ
  · intro ψ₁ ψ₂ _ _ h₁ h₂
    exact isIsotypicCuspFormAt_add h₁ h₂
  · intro c ψ₁ _ h₁
    exact isIsotypicCuspFormAt_smul h₁ c

end

end PredicateClosure

namespace WeightPiece

open IsDedekindDomain NumberField
open NumberField.AdelicLevel NumberField.AdelicBox
p2m_open "AutomorphicForm~continuous_unipotentGL2~isIsotypicCuspFormAt_of_mem_isotypicCuspSubmodule AutomorphicForm.CuspidalConstituent AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering"

section

variable {K : Type} [Field K] [NumberField K]

private theorem tensor_add (fa fb : GL (Fin 2) (InfiniteAdeleRing K) → ℂ)
    (ff : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K) → ℂ) :
    (fun g : AdelicGL2 (𝓞 K) K => (fa + fb) (glArch (𝓞 K) K g) * ff (glFin (𝓞 K) K g)) =
      (fun g => fa (glArch (𝓞 K) K g) * ff (glFin (𝓞 K) K g)) +
        fun g => fb (glArch (𝓞 K) K g) * ff (glFin (𝓞 K) K g) := by
  funext g
  simp only [Pi.add_apply, add_mul]

private theorem tensor_smul (c : ℂ) (fa : GL (Fin 2) (InfiniteAdeleRing K) → ℂ)
    (ff : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K) → ℂ) :
    (fun g : AdelicGL2 (𝓞 K) K => (c • fa) (glArch (𝓞 K) K g) * ff (glFin (𝓞 K) K g)) =
      c • fun g => fa (glArch (𝓞 K) K g) * ff (glFin (𝓞 K) K g) := by
  funext g
  simp only [Pi.smul_apply, smul_eq_mul, mul_assoc]

private theorem tensor_zero (ff : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K) → ℂ) :
    (fun g : AdelicGL2 (𝓞 K) K => (0 : GL (Fin 2) (InfiniteAdeleRing K) → ℂ) (glArch (𝓞 K) K g) *
      ff (glFin (𝓞 K) K g)) = 0 := by
  funext g
  simp only [Pi.zero_apply, zero_mul]

private theorem isArchBiFinite_add {tys : ArchTypeFamily K} {t₁ t₂ : AdelicGL2 (𝓞 K) K → ℂ}
    (h₁ : IsArchBiFinite K tys t₁) (h₂ : IsArchBiFinite K tys t₂) : IsArchBiFinite K tys (t₁ + t₂) :=
  ⟨(archCutSubmodule K tys).add_mem h₁.1 h₂.1, (archDualCutSubmodule K tys).add_mem h₁.2 h₂.2⟩

private theorem isArchBiFinite_smul {tys : ArchTypeFamily K} (c : ℂ) {t : AdelicGL2 (𝓞 K) K → ℂ}
    (h : IsArchBiFinite K tys t) : IsArchBiFinite K tys (c • t) :=
  ⟨(archCutSubmodule K tys).smul_mem c h.1, (archDualCutSubmodule K tys).smul_mem c h.2⟩

private theorem _root_.WeightPiece.isArchBiFinite_tensor_zero (tys : ArchTypeFamily K) (ff : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K) → ℂ) :
    IsArchBiFinite K tys fun g : AdelicGL2 (𝓞 K) K =>
      (0 : GL (Fin 2) (InfiniteAdeleRing K) → ℂ) (glArch (𝓞 K) K g) * ff (glFin (𝓞 K) K g) := by
  rw [tensor_zero]
  exact isArchBiFinite_zero K tys

p2m_export "WeightPiece" "isArchBiFinite_tensor_zero"
private theorem _root_.WeightPiece.isArchBiFinite_tensor_add {tys : ArchTypeFamily K} {ff : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K) → ℂ}
    {fa fb : GL (Fin 2) (InfiniteAdeleRing K) → ℂ}
    (ha : IsArchBiFinite K tys fun g : AdelicGL2 (𝓞 K) K => fa (glArch (𝓞 K) K g) * ff (glFin (𝓞 K) K g))
    (hb : IsArchBiFinite K tys fun g : AdelicGL2 (𝓞 K) K => fb (glArch (𝓞 K) K g) * ff (glFin (𝓞 K) K g)) :
    IsArchBiFinite K tys fun g : AdelicGL2 (𝓞 K) K => (fa + fb) (glArch (𝓞 K) K g) * ff (glFin (𝓞 K) K g) := by
  rw [tensor_add]
  exact isArchBiFinite_add ha hb

p2m_export "WeightPiece" "isArchBiFinite_tensor_add"
private theorem _root_.WeightPiece.isArchBiFinite_tensor_smul {tys : ArchTypeFamily K} {ff : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K) → ℂ}
    (c : ℂ) {fa : GL (Fin 2) (InfiniteAdeleRing K) → ℂ}
    (ha : IsArchBiFinite K tys fun g : AdelicGL2 (𝓞 K) K => fa (glArch (𝓞 K) K g) * ff (glFin (𝓞 K) K g)) :
    IsArchBiFinite K tys fun g : AdelicGL2 (𝓞 K) K => (c • fa) (glArch (𝓞 K) K g) * ff (glFin (𝓞 K) K g) := by
  rw [tensor_smul]
  exact isArchBiFinite_smul c ha

p2m_export "WeightPiece" "isArchBiFinite_tensor_smul"
private theorem _root_.WeightPiece.isFactorizableTestFn_tensor {fa : GL (Fin 2) (InfiniteAdeleRing K) → ℂ} (hfa : IsArchTestFactor K fa)
    {ff : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K) → ℂ} (hff : IsFinTestFactor K ff) :
    IsFactorizableTestFn K fun g : AdelicGL2 (𝓞 K) K => fa (glArch (𝓞 K) K g) * ff (glFin (𝓞 K) K g) :=
  ⟨fa, ff, hfa, hff, fun _ => rfl⟩

p2m_export "WeightPiece" "isFactorizableTestFn_tensor"
end

section

variable {K : Type} [Field K] [NumberField K]

private theorem mem_archCutSubmodule_ofChar_of_forall
    (χ : ∀ w : InfinitePlace K, rowIsometrySubgroup₀ w.Completion →* ℂˣ) {f : AdelicGL2 (𝓞 K) K → ℂ}
    (h : ∀ w : InfinitePlace K, f ∈ archTypeSubmoduleAt K w (ArchRepAt.ofChar K (χ w))) :
    f ∈ archCutSubmodule K (ArchTypeFamily.ofChar K χ) := by
  show f ∈ ⨅ w : InfinitePlace K, ⨆ _ : Fin 1, archTypeSubmoduleAt K w (ArchRepAt.ofChar K (χ w))
  simp only [iSup_const, Submodule.mem_iInf]
  exact h

private theorem forall_of_mem_archCutSubmodule_ofChar
    (χ : ∀ w : InfinitePlace K, rowIsometrySubgroup₀ w.Completion →* ℂˣ) {f : AdelicGL2 (𝓞 K) K → ℂ}
    (h : f ∈ archCutSubmodule K (ArchTypeFamily.ofChar K χ)) (w : InfinitePlace K) :
    f ∈ archTypeSubmoduleAt K w (ArchRepAt.ofChar K (χ w)) := by
  have h' : f ∈ ⨅ w : InfinitePlace K, ⨆ _ : Fin 1, archTypeSubmoduleAt K w (ArchRepAt.ofChar K (χ w)) := h
  simp only [iSup_const, Submodule.mem_iInf] at h'
  exact h' w

private theorem rightConv_mem_archCutSubmodule_ofChar
    (χ : ∀ w : InfinitePlace K, rowIsometrySubgroup₀ w.Completion →* ℂˣ) (φ : AdelicGL2 (𝓞 K) K → ℂ)
    {t : AdelicGL2 (𝓞 K) K → ℂ} (ht : IsArchBiFinite K (ArchTypeFamily.ofChar K χ) t) :
    rightConv K φ t ∈ archCutSubmodule K (ArchTypeFamily.ofChar K χ) :=
  mem_archCutSubmodule_ofChar_of_forall χ fun w =>
    rightConv_mem_archTypeSubmoduleAt_ofChar K w (χ w) φ t (forall_of_mem_archCutSubmodule_ofChar χ ht.1 w)

end

section

variable {K : Type} [Field K] [NumberField K]

private theorem rightConv_zero_left' (t : AdelicGL2 (𝓞 K) K → ℂ) : rightConv K (0 : AdelicGL2 (𝓞 K) K → ℂ) t = 0 :=
  rightConv_zero_left K t

private theorem rightConv_smul_left (c : ℂ) (u t : AdelicGL2 (𝓞 K) K → ℂ) :
    rightConv K (c • u) t = c • rightConv K u t := by
  rw [← convOp_apply, ← convOp_apply, convOp_smul]

end

section

variable {K : Type} [Field K] [NumberField K]

private def weightPiece (pins : CarrierPins K) (ξ : pins.Z →* ℂˣ) (N : Ideal (𝓞 K))
    (S : Finset (HeightOneSpectrum (𝓞 K))) (Φ : HeckeEigensystem K ℂ) (V : Submodule ℂ (AdelicGL2 (𝓞 K) K → ℂ))
    (χ : ∀ w : InfinitePlace K, rowIsometrySubgroup₀ w.Completion →* ℂˣ) : Submodule ℂ (AdelicGL2 (𝓞 K) K → ℂ) :=
  V ⊓ isotypicCuspSubmodule K pins ξ N S Φ ⊓ archCutSubmodule K (ArchTypeFamily.ofChar K χ)

private theorem mem_weightPiece_iff {pins : CarrierPins K} {ξ : pins.Z →* ℂˣ} {N : Ideal (𝓞 K)}
    {S : Finset (HeightOneSpectrum (𝓞 K))} {Φ : HeckeEigensystem K ℂ} {V : Submodule ℂ (AdelicGL2 (𝓞 K) K → ℂ)}
    {χ : ∀ w : InfinitePlace K, rowIsometrySubgroup₀ w.Completion →* ℂˣ} {f : AdelicGL2 (𝓞 K) K → ℂ} :
    f ∈ weightPiece pins ξ N S Φ V χ ↔
      f ∈ V ∧ f ∈ isotypicCuspSubmodule K pins ξ N S Φ ∧ f ∈ archCutSubmodule K (ArchTypeFamily.ofChar K χ) := by
  simp only [weightPiece, Submodule.mem_inf, and_assoc]

private theorem isotypicCuspSubmodule_le_levelInvariantSubmodule (pins : CarrierPins K) (ξ : pins.Z →* ℂˣ)
    (N : Ideal (𝓞 K)) (S : Finset (HeightOneSpectrum (𝓞 K))) (Φ : HeckeEigensystem K ℂ) :
    isotypicCuspSubmodule K pins ξ N S Φ ≤ levelInvariantSubmodule K pins N :=
  Submodule.span_le.2 fun _ hφ => hφ.level_invariant

private theorem weightPiece_le (pins : CarrierPins K) (ξ : pins.Z →* ℂˣ) (N : Ideal (𝓞 K))
    (S : Finset (HeightOneSpectrum (𝓞 K))) (Φ : HeckeEigensystem K ℂ) (V : Submodule ℂ (AdelicGL2 (𝓞 K) K → ℂ))
    (χ : ∀ w : InfinitePlace K, rowIsometrySubgroup₀ w.Completion →* ℂˣ) :
    weightPiece pins ξ N S Φ V χ ≤
      V ⊓ levelInvariantSubmodule K pins N ⊓ archCutSubmodule K (ArchTypeFamily.ofChar K χ) :=
  inf_le_inf_right _ (inf_le_inf_left _ (isotypicCuspSubmodule_le_levelInvariantSubmodule pins ξ N S Φ))

private theorem finiteDimensional_weightPiece (pins : CarrierPins K) (ξ : pins.Z →* ℂˣ) (N : Ideal (𝓞 K))
    (S : Finset (HeightOneSpectrum (𝓞 K))) (Φ : HeckeEigensystem K ℂ) (V : Submodule ℂ (AdelicGL2 (𝓞 K) K → ℂ))
    (χ : ∀ w : InfinitePlace K, rowIsometrySubgroup₀ w.Completion →* ℂˣ)
    (hfin : FiniteDimensional ℂ
      ↥(V ⊓ levelInvariantSubmodule K pins N ⊓ archCutSubmodule K (ArchTypeFamily.ofChar K χ))) :
    FiniteDimensional ℂ ↥(weightPiece pins ξ N S Φ V χ) :=
  Submodule.finiteDimensional_of_le (weightPiece_le pins ξ N S Φ V χ)

private theorem rightConv_mem_isotypicCuspSubmodule {pins : CarrierPins K} {ξ : pins.Z →* ℂˣ} {N : Ideal (𝓞 K)}
    {S : Finset (HeightOneSpectrum (𝓞 K))} {Φ : HeckeEigensystem K ℂ} {t : AdelicGL2 (𝓞 K) K → ℂ}
    (htc : Continuous t) (hts : HasCompactSupport t)
    (hgen : ∀ u : AdelicGL2 (𝓞 K) K → ℂ, IsIsotypicCuspFormAt K pins ξ N S Φ u →
      rightConv K u t ∈ isotypicCuspSubmodule K pins ξ N S Φ)
    {f : AdelicGL2 (𝓞 K) K → ℂ} (hf : f ∈ isotypicCuspSubmodule K pins ξ N S Φ) :
    rightConv K f t ∈ isotypicCuspSubmodule K pins ξ N S Φ := by
  refine Submodule.span_induction (p := fun u _ => rightConv K u t ∈ isotypicCuspSubmodule K pins ξ N S Φ)
    (fun u hu => hgen u hu) ?_ ?_ ?_ hf
  · show rightConv K 0 t ∈ isotypicCuspSubmodule K pins ξ N S Φ
    rw [rightConv_zero_left']
    exact Submodule.zero_mem _
  · intro u w hu hw hu' hw'
    rw [rightConv_add_left K (continuous_of_mem_isotypicCuspSubmodule hu) (continuous_of_mem_isotypicCuspSubmodule hw)
      htc hts]
    exact Submodule.add_mem _ hu' hw'
  · intro c u _ hu'
    rw [rightConv_smul_left]
    exact Submodule.smul_mem _ c hu'

end

section

private abbrev windowPins (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 ℚ) ℚ)) : CarrierPins ℚ :=
  productionPinsOf ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂)
    (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ)

variable (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 ℚ) ℚ))

private theorem finiteDimensional_weightPiece_window (hd : d₁ < d₂)
    (hcov : CoversModCentre ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂))
    (ξ : (windowPins c u d₁ d₂ T).Z →* ℂˣ) (N : Ideal (𝓞 ℚ)) (hN : N ≠ ⊥)
    (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (Φ : HeckeEigensystem ℚ ℂ) (V : Submodule ℂ (AdelicGL2 (𝓞 ℚ) ℚ → ℂ))
    (hV : IsCuspConstituent ℚ (windowPins c u d₁ d₂ T) ξ V)
    (χ : ∀ w : InfinitePlace ℚ, rowIsometrySubgroup₀ w.Completion →* ℂˣ) :
    FiniteDimensional ℂ ↥(weightPiece (windowPins c u d₁ d₂ T) ξ N S Φ V χ) :=
  finiteDimensional_weightPiece _ ξ N S Φ V χ
    (AutomorphicForm.finiteDimensional_inf_levelInvariantSubmodule_inf_archCutSubmodule_of_isCuspConstituent ℚ
      c u d₁ d₂ T hd hcov ξ N hN (ArchTypeFamily.ofChar ℚ χ) V hV)

variable {c u d₁ d₂ T}

private theorem rightConv_tensor_mem_weightPiece (ξ : (windowPins c u d₁ d₂ T).Z →* ℂˣ)
    (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (Φ : HeckeEigensystem ℚ ℂ) {V : Submodule ℂ (AdelicGL2 (𝓞 ℚ) ℚ → ℂ)}
    (hV : IsCuspConstituent ℚ (windowPins c u d₁ d₂ T) ξ V)
    (χ : ∀ w : InfinitePlace ℚ, rowIsometrySubgroup₀ w.Completion →* ℂˣ)
    {ff : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ) → ℂ} (hff : IsFinTestFactor ℚ ff)
    (hsupp : ∀ x : AdelicGL2 (𝓞 ℚ) ℚ, ff (glFin (𝓞 ℚ) ℚ x) ≠ 0 → ∃ a k : AdelicGL2 (𝓞 ℚ) ℚ,
      glFin (𝓞 ℚ) ℚ a = 1 ∧ k ∈ levelOne (𝓞 ℚ) ℚ Φ.level ⊓ finiteAdelicGL2Subgroup ℚ ∧ x = a * k)
    (hconv : ∀ R : SmoothCuspRealizationAt ℚ (windowPins c u d₁ d₂ T) Φ.toRawCentral, Continuous R.toFun →
      ∀ t : AdelicGL2 (𝓞 ℚ) ℚ → ℂ, IsFactorizableTestFn ℚ t →
        (∀ x : AdelicGL2 (𝓞 ℚ) ℚ, t x ≠ 0 → ∃ a k : AdelicGL2 (𝓞 ℚ) ℚ,
          glFin (𝓞 ℚ) ℚ a = 1 ∧ k ∈ levelOne (𝓞 ℚ) ℚ Φ.level ⊓ finiteAdelicGL2Subgroup ℚ ∧ x = a * k) →
        IsIsotypicCuspFormAt ℚ (windowPins c u d₁ d₂ T) R.centralChar Φ.level R.exceptionalSet Φ
          (rightConv ℚ R.toFun t))
    (a : GL (Fin 2) (InfiniteAdeleRing ℚ) → ℂ) (ha : IsArchTestFactor ℚ a)
    (hbi : IsArchBiFinite ℚ (ArchTypeFamily.ofChar ℚ χ) fun g => a (glArch (𝓞 ℚ) ℚ g) * ff (glFin (𝓞 ℚ) ℚ g))
    (f : AdelicGL2 (𝓞 ℚ) ℚ → ℂ) (hf : f ∈ weightPiece (windowPins c u d₁ d₂ T) ξ Φ.level S Φ V χ) :
    rightConv ℚ f (fun g => a (glArch (𝓞 ℚ) ℚ g) * ff (glFin (𝓞 ℚ) ℚ g)) ∈
      weightPiece (windowPins c u d₁ d₂ T) ξ Φ.level S Φ V χ := by
  obtain ⟨hfV, hfiso, -⟩ := mem_weightPiece_iff.1 hf
  have ht : IsFactorizableTestFn ℚ fun g => a (glArch (𝓞 ℚ) ℚ g) * ff (glFin (𝓞 ℚ) ℚ g) :=
    isFactorizableTestFn_tensor ha hff
  obtain ⟨htc, htcs⟩ := AutomorphicForm.continuous_and_hasCompactSupport_of_isFactorizableTestFn ℚ _ ht
  have hts : ∀ x : AdelicGL2 (𝓞 ℚ) ℚ, a (glArch (𝓞 ℚ) ℚ x) * ff (glFin (𝓞 ℚ) ℚ x) ≠ 0 →
      ∃ a' k : AdelicGL2 (𝓞 ℚ) ℚ,
        glFin (𝓞 ℚ) ℚ a' = 1 ∧ k ∈ levelOne (𝓞 ℚ) ℚ Φ.level ⊓ finiteAdelicGL2Subgroup ℚ ∧ x = a' * k :=
    fun x hx => hsupp x (right_ne_zero_of_mul hx)
  refine mem_weightPiece_iff.2 ⟨hV.1.rightConv_mem _ _ ht hbi f hfV, ?_, rightConv_mem_archCutSubmodule_ofChar χ f hbi⟩
  refine rightConv_mem_isotypicCuspSubmodule htc htcs (fun v hv => ?_) hfiso
  by_cases hv0 : v = 0
  · subst hv0
    rw [rightConv_zero_left']
    exact Submodule.zero_mem _
  · exact (hconv (hv.toRealization hv0) hv.continuous _ ht hts).mem_isotypicCuspSubmodule

end

end WeightPiece

namespace StableSubspace

variable {M : Type} [AddCommGroup M] [Module ℂ M]

private def restrictToSubspace (E : Submodule ℂ M) (T : M → M) (hadd : ∀ x ∈ E, ∀ y ∈ E, T (x + y) = T x + T y)
    (hsmul : ∀ (c : ℂ), ∀ x ∈ E, T (c • x) = c • T x) (hmap : ∀ x ∈ E, T x ∈ E) : Module.End ℂ E where
  toFun x := ⟨T x, hmap x x.2⟩
  map_add' x y := Subtype.ext (hadd x x.2 y y.2)
  map_smul' c x := Subtype.ext (hsmul c x x.2)

private theorem exists_mem_ne_zero_apply_eq_smul (E : Submodule ℂ M) [FiniteDimensional ℂ E] (hE : E ≠ ⊥)
    (T : M → M) (hadd : ∀ x ∈ E, ∀ y ∈ E, T (x + y) = T x + T y)
    (hsmul : ∀ (c : ℂ), ∀ x ∈ E, T (c • x) = c • T x) (hmap : ∀ x ∈ E, T x ∈ E) :
    ∃ (μ : ℂ) (ψ : M), ψ ∈ E ∧ ψ ≠ 0 ∧ T ψ = μ • ψ := by
  haveI : Nontrivial E := Submodule.nontrivial_iff_ne_bot.2 hE
  obtain ⟨μ, hμ⟩ := Module.End.exists_eigenvalue (restrictToSubspace E T hadd hsmul hmap)
  obtain ⟨v, hv⟩ := hμ.exists_hasEigenvector
  refine ⟨μ, v, v.2, fun h => (Module.End.hasEigenvector_iff.1 hv).2 (Subtype.ext h), ?_⟩
  exact congrArg Subtype.val hv.apply_eq_smul

end StableSubspace

namespace InvertedFactor

p2m_open "NumberField AutomorphicForm~continuous_unipotentGL2~isIsotypicCuspFormAt_of_mem_isotypicCuspSubmodule NumberField.AdelicLevel"
open NumberField.InfinitePlace.Completion (ringEquivRealOfIsReal isometryEquivRealOfIsReal)
open scoped Topology

private abbrev Ent : Type := Fin 2 → Fin 2 → ℝ

private abbrev tcDetSet : Set Ent := {e : Ent | (Matrix.of e).det ≠ 0}

section

private def tcInv (e : Ent) : Ent := fun i j => !![e 1 1, -e 0 1; -e 1 0, e 0 0] i j / (Matrix.of e).det

private theorem tc_of_tcInv {e : Ent} : Matrix.of (tcInv e) = (Matrix.of e)⁻¹ := by
  rw [Matrix.inv_def, Matrix.adjugate_fin_two, Ring.inverse_eq_inv]
  ext i j
  simp only [tcInv, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul, div_eq_inv_mul]

private theorem tc_det_tcInv {e : Ent} (he : (Matrix.of e).det ≠ 0) : (Matrix.of (tcInv e)).det ≠ 0 := by
  rw [tc_of_tcInv, Matrix.det_nonsing_inv, Ring.inverse_eq_inv]
  exact inv_ne_zero he

private theorem tc_contDiff_entry (i j : Fin 2) : ContDiff ℝ (⊤ : ℕ∞) fun e : Ent => e i j :=
  (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) j).contDiff.comp
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => Fin 2 → ℝ) i).contDiff

private theorem tc_contDiff_det : ContDiff ℝ (⊤ : ℕ∞) fun e : Ent => (Matrix.of e).det := by
  simp only [Matrix.det_fin_two, Matrix.of_apply]
  exact ((tc_contDiff_entry 0 0).mul (tc_contDiff_entry 1 1)).sub ((tc_contDiff_entry 0 1).mul (tc_contDiff_entry 1 0))

private theorem tc_contDiff_adj (i j : Fin 2) :
    ContDiff ℝ (⊤ : ℕ∞) fun e : Ent => !![e 1 1, -e 0 1; -e 1 0, e 0 0] i j := by
  fin_cases i <;> fin_cases j <;> simp <;> first | exact tc_contDiff_entry _ _ | exact (tc_contDiff_entry _ _).neg

private theorem tc_contDiffOn_tcInv : ContDiffOn ℝ (⊤ : ℕ∞) tcInv tcDetSet :=
  contDiffOn_pi.2 fun i => contDiffOn_pi.2 fun j =>
    (tc_contDiff_adj i j).contDiffOn.div tc_contDiff_det.contDiffOn fun _ he => he

variable {K : Type} [Field K] [NumberField K] {w : InfinitePlace K}

private theorem cv_lift_inv (hw : w.IsReal) {e : Ent} (he : (Matrix.of e).det ≠ 0) :
    (archRealLiftAt hw e : AdelicGL2 (𝓞 K) K)⁻¹ = archRealLiftAt hw (tcInv e) := by
  rw [archRealLiftAt_of_det_ne_zero hw he, archRealLiftAt_of_det_ne_zero hw (tc_det_tcInv he), ← map_inv]
  congr 1
  apply Units.ext
  rw [Matrix.coe_units_inv]
  exact tc_of_tcInv.symm

end

section

open scoped Classical

section

variable (K : Type) [Field K]

private abbrev cvEnt : Type := Fin 2 → Fin 2 → mixedEmbedding.mixedSpace K

private theorem cv_continuous_ringEquiv : Continuous (InfiniteAdeleRing.ringEquiv_mixedSpace K) := by
  refine continuous_prodMk.2 ⟨continuous_pi fun v => ?_, continuous_pi fun v => ?_⟩
  · exact (NumberField.InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal v.2).continuous.comp
      (continuous_apply _)
  · exact (NumberField.InfinitePlace.Completion.isometry_extensionEmbedding v.1).continuous.comp (continuous_apply _)

private theorem cv_archEntries_eq_mapMatrix (g : GL (Fin 2) (InfiniteAdeleRing K)) :
    (archEntries K g : Matrix (Fin 2) (Fin 2) (mixedEmbedding.mixedSpace K)) =
      (InfiniteAdeleRing.ringEquiv_mixedSpace K).toRingHom.mapMatrix
        (g : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) := by
  funext i j
  rfl

private theorem cv_of_archEntries (g : GL (Fin 2) (InfiniteAdeleRing K)) :
    Matrix.of (archEntries K g) = (InfiniteAdeleRing.ringEquiv_mixedSpace K).toRingHom.mapMatrix
      (g : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) :=
  cv_archEntries_eq_mapMatrix K g

private theorem cv_archEntries_mul (a z : GL (Fin 2) (InfiniteAdeleRing K)) :
    Matrix.of (archEntries K (a * z)) = Matrix.of (archEntries K a) * Matrix.of (archEntries K z) := by
  simp only [cv_of_archEntries, Units.val_mul, map_mul]

variable {K}

private def cvsingle (w : InfinitePlace K) (x : w.Completion) : InfiniteAdeleRing K :=
  Pi.single (M := fun v : InfinitePlace K => v.Completion) w x

private theorem cv_archMatrixUpdate_entry (w : InfinitePlace K) (m : Matrix (Fin 2) (Fin 2) w.Completion)
    (i j : Fin 2) :
    archMatrixUpdate K w m i j = archMatrixUpdate K w 0 i j + cvsingle w (m i j) := by
  funext v
  show archMatrixUpdate K w m i j v =
    archMatrixUpdate K w 0 i j v + Pi.single (M := fun v : InfinitePlace K => v.Completion) w (m i j) v
  by_cases hv : v = w
  · subst hv
    rw [archMatrixUpdate_apply_self, archMatrixUpdate_apply_self, Pi.single_eq_same, Matrix.zero_apply, zero_add]
  · rw [archMatrixUpdate_apply_of_ne K w m i j hv, archMatrixUpdate_apply_of_ne K w 0 i j hv, Pi.single_eq_of_ne hv,
      add_zero]

private def cvConst (w : InfinitePlace K) : cvEnt K :=
  fun i j => InfiniteAdeleRing.ringEquiv_mixedSpace K (archMatrixUpdate K w 0 i j)

private theorem cv_archEntries_archGLIncl (w : InfinitePlace K) (k : GL (Fin 2) w.Completion) (i j : Fin 2) :
    archEntries K (archGLIncl K w k) i j =
      cvConst w i j +
        InfiniteAdeleRing.ringEquiv_mixedSpace K (cvsingle w ((k : Matrix (Fin 2) (Fin 2) w.Completion) i j)) := by
  rw [archEntries_apply]
  show InfiniteAdeleRing.ringEquiv_mixedSpace K
    (archMatrixUpdate K w (k : Matrix (Fin 2) (Fin 2) w.Completion) i j) = _
  rw [cv_archMatrixUpdate_entry, map_add]
  rfl

private def cvAddHom {w : InfinitePlace K} (hw : w.IsReal) : ℝ →+ mixedEmbedding.mixedSpace K :=
  (InfiniteAdeleRing.ringEquiv_mixedSpace K).toAddMonoidHom.comp
    ((AddMonoidHom.single (f := fun v : InfinitePlace K => v.Completion) w).comp
      (ringEquivRealOfIsReal hw).symm.toAddMonoidHom)

private theorem cvAddHom_apply {w : InfinitePlace K} (hw : w.IsReal) (r : ℝ) :
    cvAddHom hw r = InfiniteAdeleRing.ringEquiv_mixedSpace K (cvsingle w ((ringEquivRealOfIsReal hw).symm r)) :=
  rfl

private theorem cv_continuous_addHom {w : InfinitePlace K} (hw : w.IsReal) : Continuous (cvAddHom hw) := by
  have h1 : Continuous fun x : w.Completion => cvsingle w x := continuous_single w
  have h2 : Continuous fun r : ℝ => (ringEquivRealOfIsReal hw).symm r :=
    (isometryEquivRealOfIsReal hw).symm.continuous
  have h3 : ⇑(cvAddHom hw) = fun r : ℝ =>
      InfiniteAdeleRing.ringEquiv_mixedSpace K (cvsingle w ((ringEquivRealOfIsReal hw).symm r)) :=
    funext fun r => cvAddHom_apply hw r
  rw [h3]
  exact (cv_continuous_ringEquiv K).comp (h1.comp h2)

private def cvLin {w : InfinitePlace K} (hw : w.IsReal) : ℝ →L[ℝ] mixedEmbedding.mixedSpace K :=
  (cvAddHom hw).toRealLinearMap (cv_continuous_addHom hw)

private def cvLinMat {w : InfinitePlace K} (hw : w.IsReal) : (Fin 2 → Fin 2 → ℝ) →L[ℝ] cvEnt K :=
  ContinuousLinearMap.pi fun i => ContinuousLinearMap.pi fun j =>
    (cvLin hw).comp ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) j).comp
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => Fin 2 → ℝ) i))

private theorem cvLinMat_apply {w : InfinitePlace K} (hw : w.IsReal) (e : Fin 2 → Fin 2 → ℝ) (i j : Fin 2) :
    cvLinMat hw e i j = cvAddHom hw (e i j) :=
  rfl

end

section

variable {K : Type} [Field K] [NumberField K]

private theorem cv_archEntries_glArch_lift {w : InfinitePlace K} (hw : w.IsReal) {e : Fin 2 → Fin 2 → ℝ}
    (he : (Matrix.of e).det ≠ 0) :
    archEntries K (glArch (𝓞 K) K (archRealLiftAt hw e)) = cvConst w + cvLinMat hw e := by
  rw [archRealLiftAt_of_det_ne_zero hw he]
  have h1 : glArch (𝓞 K) K (archRealGLAt hw (Matrix.GeneralLinearGroup.mkOfDetNeZero (Matrix.of e) he)) =
      archGLIncl K w (glEquivOfRingEquiv (ringEquivRealOfIsReal hw).symm
        (Matrix.GeneralLinearGroup.mkOfDetNeZero (Matrix.of e) he)) :=
    glArch_adelicArchGLIncl K _
  rw [h1]
  funext i j
  rw [cv_archEntries_archGLIncl, glEquivOfRingEquiv_apply_entry, Pi.add_apply, Pi.add_apply, cvLinMat_apply,
    cvAddHom_apply]
  rfl

end

end

section

open MeasureTheory
open scoped Pointwise

variable {K : Type} [Field K] [NumberField K] {w : InfinitePlace K}

private theorem cv_glFin_lift (hw : w.IsReal) {e : Ent} (he : (Matrix.of e).det ≠ 0) :
    glFin (𝓞 K) K (archRealLiftAt hw e) = 1 := by
  rw [archRealLiftAt_of_det_ne_zero hw he]
  exact glFin_adelicArchGLIncl K _

private def cvMulRLin (M : cvEnt K) : cvEnt K →ₗ[ℝ] cvEnt K where
  toFun N := Matrix.of.symm (Matrix.of N * Matrix.of M)
  map_add' N₁ N₂ := by
    show Matrix.of.symm ((Matrix.of N₁ + Matrix.of N₂) * Matrix.of M) =
      Matrix.of.symm (Matrix.of N₁ * Matrix.of M) + Matrix.of.symm (Matrix.of N₂ * Matrix.of M)
    rw [Matrix.add_mul]
    rfl
  map_smul' t N := by
    show Matrix.of.symm ((t • Matrix.of N) * Matrix.of M) = t • Matrix.of.symm (Matrix.of N * Matrix.of M)
    rw [Matrix.smul_mul]
    rfl

private def cvMulR (M : cvEnt K) : cvEnt K →L[ℝ] cvEnt K := LinearMap.toContinuousLinearMap (cvMulRLin M)

private theorem cvMulR_apply (M N : cvEnt K) : cvMulR M N = Matrix.of.symm (Matrix.of N * Matrix.of M) := rfl

private theorem cv_archEntries_lift_mul (hw : w.IsReal) {e : Ent} (he : (Matrix.of e).det ≠ 0)
    (y : AdelicGL2 (𝓞 K) K) :
    archEntries K (glArch (𝓞 K) K (archRealLiftAt hw e * y)) =
      cvMulR (archEntries K (glArch (𝓞 K) K y)) (cvConst w) +
        cvMulR (archEntries K (glArch (𝓞 K) K y)) (cvLinMat hw e) := by
  rw [cvMulR_apply, cvMulR_apply,
    ← Matrix.of.symm_apply_apply (archEntries K (glArch (𝓞 K) K (archRealLiftAt hw e * y))), map_mul,
    cv_archEntries_mul, cv_archEntries_glArch_lift hw he]
  show Matrix.of.symm ((Matrix.of (cvConst w) + Matrix.of (cvLinMat hw e)) *
    Matrix.of (archEntries K (glArch (𝓞 K) K y))) = _
  rw [Matrix.add_mul]
  rfl

private theorem cv_factor_lift_mul (hw : w.IsReal) {α : AdelicGL2 (𝓞 K) K → ℂ}
    {fa : GL (Fin 2) (InfiniteAdeleRing K) → ℂ} {ff : GL (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 K) K) → ℂ}
    {Φ : cvEnt K → ℂ} (hfa : ∀ z, fa z = Φ (archEntries K z))
    (hα : ∀ g, α g = fa (glArch (𝓞 K) K g) * ff (glFin (𝓞 K) K g)) {e : Ent} (he : (Matrix.of e).det ≠ 0)
    (y : AdelicGL2 (𝓞 K) K) :
    α (archRealLiftAt hw e * y) =
      Φ (cvMulR (archEntries K (glArch (𝓞 K) K y)) (cvConst w) +
          cvMulR (archEntries K (glArch (𝓞 K) K y)) (cvLinMat hw e)) *
        ff (glFin (𝓞 K) K y) := by
  rw [hα, hfa, cv_archEntries_lift_mul hw he, map_mul, cv_glFin_lift hw he, one_mul]

end

section

open MeasureTheory Metric Set

section

variable {X : Type} [MeasurableSpace X] (ν : Measure X)
variable {Y : Type} [NormedAddCommGroup Y] [NormedSpace ℝ Y]

variable {ν}

end

section

variable {X : Type} [MeasurableSpace X] {ν : Measure X}
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]

end

end

section

open MeasureTheory Metric Set
open scoped Classical

variable {K : Type} [Field K] [NumberField K] {w : InfinitePlace K}

private def _root_.InvertedFactor.leftDeriv (hw : w.IsReal) (d : ArchDir) (α : AdelicGL2 (𝓞 K) K → ℂ) : AdelicGL2 (𝓞 K) K → ℂ :=
  fun y => deriv (fun t : ℝ => α (archFlowAt hw d (-t) * y)) 0

p2m_export "InvertedFactor" "leftDeriv"
private theorem cv_archFlowAt_inv (hw : w.IsReal) (d : ArchDir) (t : ℝ) :
    (archFlowAt hw d t : AdelicGL2 (𝓞 K) K)⁻¹ = archFlowAt hw d (-t) :=
  inv_eq_of_mul_eq_one_right (by rw [← archFlowAt_add, add_neg_cancel, archFlowAt_zero])

private def cvM (y : AdelicGL2 (𝓞 K) K) : cvEnt K := archEntries K (glArch (𝓞 K) K y)

private def cvcD (w : InfinitePlace K) (y : AdelicGL2 (𝓞 K) K) : cvEnt K := cvMulR (cvM y) (cvConst w)

private def cvLD (hw : w.IsReal) (y : AdelicGL2 (𝓞 K) K) : Ent →L[ℝ] cvEnt K := (cvMulR (cvM y)).comp (cvLinMat hw)

private theorem cv_leftDeriv_inv (hw : w.IsReal) (d : ArchDir) (α : AdelicGL2 (𝓞 K) K → ℂ) (y : AdelicGL2 (𝓞 K) K) :
    leftDeriv hw d α y⁻¹ = archDerivAt hw d (fun z => α z⁻¹) y := by
  show deriv (fun t : ℝ => α (archFlowAt hw d (-t) * y⁻¹)) 0 = deriv (fun t : ℝ => α (y * archFlowAt hw d t)⁻¹) 0
  congr 1
  funext t
  rw [mul_inv_rev, cv_archFlowAt_inv]

private theorem cv_isArchSmoothAt_comp_inv (hw : w.IsReal) {α : AdelicGL2 (𝓞 K) K → ℂ}
    (hα : IsFactorizableTestFn K α) :
    IsArchSmoothAt hw fun z => α z⁻¹ := by
  obtain ⟨fa, ff, ⟨⟨Φ, hΦ, hfa⟩, -⟩, -, hαeq⟩ := hα
  intro g
  have hsm : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun e : Ent => Φ (cvcD w g⁻¹ + cvLD hw g⁻¹ (tcInv e)) * ff (glFin (𝓞 K) K g⁻¹)) tcDetSet :=
    (hΦ.comp_contDiffOn (contDiffOn_const.add ((cvLD hw g⁻¹).contDiff.comp_contDiffOn tc_contDiffOn_tcInv))).mul
      contDiffOn_const
  refine hsm.congr fun e he => ?_
  show α (g * archRealLiftAt hw e)⁻¹ = _
  rw [mul_inv_rev, cv_lift_inv hw he, cv_factor_lift_mul hw hfa hαeq (tc_det_tcInv he)]
  rfl

end

section

open scoped Classical

variable {K : Type} [Field K] [NumberField K] {w : InfinitePlace K}

end

section

open MeasureTheory Metric Set
open scoped Classical

variable {K : Type} [Field K] [NumberField K] {w : InfinitePlace K}

end

end InvertedFactor

namespace DerivedBiFinite

open IsDedekindDomain NumberField
p2m_open "AutomorphicForm~continuous_unipotentGL2~isIsotypicCuspFormAt_of_mem_isotypicCuspSubmodule"
open NumberField.InfinitePlace.Completion (ringEquivRealOfIsReal)

private def _root_.DerivedBiFinite.leftDeriv {w : InfinitePlace ℚ} (hw : w.IsReal) (d : ArchDir) (α : AdelicGL2 (𝓞 ℚ) ℚ → ℂ) :
    AdelicGL2 (𝓞 ℚ) ℚ → ℂ :=
  fun y => deriv (fun t : ℝ => α (archFlowAt hw d (-t) * y)) 0

p2m_export "DerivedBiFinite" "leftDeriv"
private def _root_.DerivedBiFinite.lowerOp {w : InfinitePlace ℚ} (hw : w.IsReal) (φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ) : AdelicGL2 (𝓞 ℚ) ℚ → ℂ :=
  archDerivAt hw .H φ - Complex.I • (archDerivAt hw .E φ + archDerivAt hw .Fm φ)

p2m_export "DerivedBiFinite" "lowerOp"
private def _root_.DerivedBiFinite.lowerTest {w : InfinitePlace ℚ} (hw : w.IsReal) (β : AdelicGL2 (𝓞 ℚ) ℚ → ℂ) : AdelicGL2 (𝓞 ℚ) ℚ → ℂ :=
  leftDeriv hw .H β - Complex.I • (leftDeriv hw .E β + leftDeriv hw .Fm β)

p2m_export "DerivedBiFinite" "lowerTest"
private def _root_.DerivedBiFinite.casimirTest {w : InfinitePlace ℚ} (hw : w.IsReal) (β : AdelicGL2 (𝓞 ℚ) ℚ → ℂ) :
    AdelicGL2 (𝓞 ℚ) ℚ → ℂ :=
  -((1 / 4 : ℂ) • leftDeriv hw .H (leftDeriv hw .H β) - (1 / 2 : ℂ) • leftDeriv hw .H β +
    leftDeriv hw .E (leftDeriv hw .Fm β))

p2m_export "DerivedBiFinite" "casimirTest"
private def catFamily (t₁ t₂ : ArchTypeFamily ℚ) : ArchTypeFamily ℚ where
  card w := t₁.card w + t₂.card w
  rep w i := Fin.addCases (t₁.rep w) (t₂.rep w) i

private theorem left_isContainedIn_catFamily (t₁ t₂ : ArchTypeFamily ℚ) :
    ArchTypeFamily.IsContainedIn ℚ t₁ (catFamily t₁ t₂) :=
  fun w i => ⟨Fin.castAdd (t₂.card w) i, by simp [catFamily]⟩

private theorem right_isContainedIn_catFamily (t₁ t₂ : ArchTypeFamily ℚ) :
    ArchTypeFamily.IsContainedIn ℚ t₂ (catFamily t₁ t₂) :=
  fun w i => ⟨Fin.natAdd (t₁.card w) i, by simp [catFamily]⟩

section

variable {w : InfinitePlace ℚ} (hw : w.IsReal)

private theorem leftDeriv_mul_right (d : ArchDir) {γ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ} {c : ℂ} {z : AdelicGL2 (𝓞 ℚ) ℚ}
    (h : ∀ g, γ (g * z) = c * γ g) (g : AdelicGL2 (𝓞 ℚ) ℚ) : leftDeriv hw d γ (g * z) = c * leftDeriv hw d γ g := by
  show deriv (fun t : ℝ => γ (archFlowAt hw d (-t) * (g * z))) 0
    = c * deriv (fun t : ℝ => γ (archFlowAt hw d (-t) * g)) 0
  simp_rw [← mul_assoc, h]
  exact deriv_const_mul_field c

private theorem lowerTest_mul_right {β : AdelicGL2 (𝓞 ℚ) ℚ → ℂ} {c : ℂ} {z : AdelicGL2 (𝓞 ℚ) ℚ}
    (h : ∀ g, β (g * z) = c * β g) (g : AdelicGL2 (𝓞 ℚ) ℚ) : lowerTest hw β (g * z) = c * lowerTest hw β g := by
  simp only [lowerTest, Pi.sub_apply, Pi.smul_apply, Pi.add_apply, smul_eq_mul, leftDeriv_mul_right hw _ h]
  ring

private theorem casimirTest_mul_right {β : AdelicGL2 (𝓞 ℚ) ℚ → ℂ} {c : ℂ} {z : AdelicGL2 (𝓞 ℚ) ℚ}
    (h : ∀ g, β (g * z) = c * β g) (g : AdelicGL2 (𝓞 ℚ) ℚ) : casimirTest hw β (g * z) = c * casimirTest hw β g := by
  have hH := leftDeriv_mul_right hw .H h
  have hF := leftDeriv_mul_right hw .Fm h
  simp only [casimirTest, Pi.neg_apply, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
    leftDeriv_mul_right hw .H hH, leftDeriv_mul_right hw .E hF, hH]
  ring

private theorem mem_archDualCutSubmodule_ofChar_iff
    (χ : ∀ w' : InfinitePlace ℚ, rowIsometrySubgroup₀ w'.Completion →* ℂˣ) (φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ) :
    φ ∈ archDualCutSubmodule ℚ (ArchTypeFamily.ofChar ℚ χ) ↔
      ∀ (w' : InfinitePlace ℚ) (k : rowIsometrySubgroup₀ w'.Completion) (g : AdelicGL2 (𝓞 ℚ) ℚ),
        φ (g * rowIsometryInclAt₀ ℚ w' k) = ((χ w' k⁻¹ : ℂˣ) : ℂ) * φ g := by
  show φ ∈ ⨅ w' : InfinitePlace ℚ,
      ⨆ _ : Fin 1, archDualTypeSubmoduleAt ℚ w' (ArchRepAt.ofChar ℚ (χ w')) ↔ _
  simp only [iSup_const, Submodule.mem_iInf]
  exact forall_congr' fun w' => mem_archDualTypeSubmoduleAt_ofChar_iff ℚ w' (χ w') φ

private theorem lowerTest_mem_archDualCut {χ : ∀ w' : InfinitePlace ℚ, rowIsometrySubgroup₀ w'.Completion →* ℂˣ}
    {β : AdelicGL2 (𝓞 ℚ) ℚ → ℂ} (hβ : β ∈ archDualCutSubmodule ℚ (ArchTypeFamily.ofChar ℚ χ)) :
    lowerTest hw β ∈ archDualCutSubmodule ℚ (ArchTypeFamily.ofChar ℚ χ) := by
  rw [mem_archDualCutSubmodule_ofChar_iff] at hβ ⊢
  intro w' k g
  exact lowerTest_mul_right hw (hβ w' k) g

private theorem casimirTest_mem_archDualCut {χ : ∀ w' : InfinitePlace ℚ, rowIsometrySubgroup₀ w'.Completion →* ℂˣ}
    {β : AdelicGL2 (𝓞 ℚ) ℚ → ℂ} (hβ : β ∈ archDualCutSubmodule ℚ (ArchTypeFamily.ofChar ℚ χ)) :
    casimirTest hw β ∈ archDualCutSubmodule ℚ (ArchTypeFamily.ofChar ℚ χ) := by
  rw [mem_archDualCutSubmodule_ofChar_iff] at hβ ⊢
  intro w' k g
  exact casimirTest_mul_right hw (hβ w' k) g

end

section

variable {w : InfinitePlace ℚ} {hw : w.IsReal}
  (hd₁ : ∀ (d : ArchDir) (γ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ) (y : AdelicGL2 (𝓞 ℚ) ℚ),
    leftDeriv hw d γ y⁻¹ = archDerivAt hw d (fun z => γ z⁻¹) y)

include hd₁ in

private theorem inv_lowerTest (β : AdelicGL2 (𝓞 ℚ) ℚ → ℂ) :
    (fun x => lowerTest hw β x⁻¹) = lowerOp hw (fun z => β z⁻¹) := by
  funext x
  simp only [lowerTest, lowerOp, Pi.sub_apply, Pi.smul_apply, Pi.add_apply, hd₁]

include hd₁ in

private theorem inv_casimirTest (β : AdelicGL2 (𝓞 ℚ) ℚ → ℂ) :
    (fun x => casimirTest hw β x⁻¹) = archCasimirAt hw (fun z => β z⁻¹) := by
  funext x
  simp only [casimirTest, archCasimirAt, Pi.neg_apply, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, hd₁]

end

section

variable {w : InfinitePlace ℚ} {hw : w.IsReal}

private theorem hasArchCharacterAt₀_archCasimirAt
    (hAd : ∀ φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ, IsArchSmoothAt hw φ → ∀ m : GL (Fin 2) ℝ,
      archCasimirAt hw (fun x => φ (x * archRealGLAt hw m)) = fun x => archCasimirAt hw φ (x * archRealGLAt hw m))
    {χ : rowIsometrySubgroup₀ w.Completion →* ℂˣ} {ψ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ} (hψ : IsArchSmoothAt hw ψ)
    (hχ : HasArchCharacterAt₀ ℚ w χ ψ) : HasArchCharacterAt₀ ℚ w χ (archCasimirAt hw ψ) := by
  intro k g
  have hι := archRealGLAt_glEquivOfRingEquiv hw (k : GL (Fin 2) w.Completion)
  have hfun : (fun x => ψ (x * archRealGLAt hw (glEquivOfRingEquiv (ringEquivRealOfIsReal hw)
      (k : GL (Fin 2) w.Completion)))) = ((χ k : ℂˣ) : ℂ) • ψ := by
    funext x
    rw [hι, Pi.smul_apply, smul_eq_mul]
    exact hχ k x
  have h := hAd ψ hψ (glEquivOfRingEquiv (ringEquivRealOfIsReal hw) (k : GL (Fin 2) w.Completion))
  rw [hfun, archCasimirAt_smul] at h
  have h' := congrFun h g
  rw [hι] at h'
  rw [← h', Pi.smul_apply, smul_eq_mul]

private theorem isArchBiFinite_casimirTest
    (hd₁ : ∀ (d : ArchDir) (γ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ) (y : AdelicGL2 (𝓞 ℚ) ℚ),
      leftDeriv hw d γ y⁻¹ = archDerivAt hw d (fun z => γ z⁻¹) y)
    (hd₂ : ∀ γ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ, IsFactorizableTestFn ℚ γ → IsArchSmoothAt hw fun z => γ z⁻¹)
    (hAd : ∀ φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ, IsArchSmoothAt hw φ → ∀ m : GL (Fin 2) ℝ,
      archCasimirAt hw (fun x => φ (x * archRealGLAt hw m)) = fun x => archCasimirAt hw φ (x * archRealGLAt hw m))
    {χ : ∀ w' : InfinitePlace ℚ, rowIsometrySubgroup₀ w'.Completion →* ℂˣ} {β : AdelicGL2 (𝓞 ℚ) ℚ → ℂ}
    (hβ : IsFactorizableTestFn ℚ β) (hbi : IsArchBiFinite ℚ (ArchTypeFamily.ofChar ℚ χ) β) :
    IsArchBiFinite ℚ (ArchTypeFamily.ofChar ℚ χ) (casimirTest hw β) := by
  refine ⟨?_, casimirTest_mem_archDualCut hw hbi.2⟩
  have hinv := (mem_archCutSubmodule_ofChar_iff ℚ χ _).mp hbi.1
  rw [inv_casimirTest hd₁, mem_archCutSubmodule_ofChar_iff]
  intro w'
  obtain rfl : w = w' := Subsingleton.elim w w'
  exact hasArchCharacterAt₀_archCasimirAt hAd (hd₂ β hβ) (hinv w)

private theorem exists_isArchBiFinite_lowerTest
    (hd₁ : ∀ (d : ArchDir) (γ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ) (y : AdelicGL2 (𝓞 ℚ) ℚ),
      leftDeriv hw d γ y⁻¹ = archDerivAt hw d (fun z => γ z⁻¹) y)
    (hd₂ : ∀ γ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ, IsFactorizableTestFn ℚ γ → IsArchSmoothAt hw fun z => γ z⁻¹)
    (hW : ∀ (m : ℤ) (ψ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ), IsArchSmoothAt hw ψ →
      HasArchCharacterAt₀ ℚ w (archWeightCharAt hw m) ψ →
        HasArchCharacterAt₀ ℚ w (archWeightCharAt hw (m - 2)) (lowerOp hw ψ))
    {χ : ∀ w' : InfinitePlace ℚ, rowIsometrySubgroup₀ w'.Completion →* ℂˣ} {m : ℤ} (hχ : χ w = archWeightCharAt hw m)
    {β : AdelicGL2 (𝓞 ℚ) ℚ → ℂ} (hβ : IsFactorizableTestFn ℚ β)
    (hbi : IsArchBiFinite ℚ (ArchTypeFamily.ofChar ℚ χ) β) :
    ∃ tys : ArchTypeFamily ℚ, IsArchBiFinite ℚ tys (lowerTest hw β) := by
  let χ' : ∀ w' : InfinitePlace ℚ, rowIsometrySubgroup₀ w'.Completion →* ℂˣ :=
    fun w' => (Subsingleton.elim w w') ▸ archWeightCharAt hw (m - 2)
  refine ⟨catFamily (ArchTypeFamily.ofChar ℚ χ) (ArchTypeFamily.ofChar ℚ χ'), ?_, ?_⟩
  · refine archCutSubmodule_mono ℚ (right_isContainedIn_catFamily _ _) ?_
    have hinv := (mem_archCutSubmodule_ofChar_iff ℚ χ _).mp hbi.1
    rw [inv_lowerTest hd₁, mem_archCutSubmodule_ofChar_iff]
    intro w'
    obtain rfl : w = w' := Subsingleton.elim w w'
    have h := hinv w
    rw [hχ] at h
    exact hW m _ (hd₂ β hβ) h
  · exact archDualCutSubmodule_mono ℚ (left_isContainedIn_catFamily _ _) (lowerTest_mem_archDualCut hw hbi.2)

end

section

variable {w : InfinitePlace ℚ}

private def _root_.DerivedBiFinite.raiseOp (hw : w.IsReal) (φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ) : AdelicGL2 (𝓞 ℚ) ℚ → ℂ :=
  archDerivAt hw .H φ + Complex.I • (archDerivAt hw .E φ + archDerivAt hw .Fm φ)

p2m_export "DerivedBiFinite" "raiseOp"
private def _root_.DerivedBiFinite.raiseTest (hw : w.IsReal) (β : AdelicGL2 (𝓞 ℚ) ℚ → ℂ) : AdelicGL2 (𝓞 ℚ) ℚ → ℂ :=
  leftDeriv hw .H β + Complex.I • (leftDeriv hw .E β + leftDeriv hw .Fm β)

p2m_export "DerivedBiFinite" "raiseTest"
private theorem raiseTest_mul_right (hw : w.IsReal) {β : AdelicGL2 (𝓞 ℚ) ℚ → ℂ} {c : ℂ} {z : AdelicGL2 (𝓞 ℚ) ℚ}
    (h : ∀ g, β (g * z) = c * β g) (g : AdelicGL2 (𝓞 ℚ) ℚ) : raiseTest hw β (g * z) = c * raiseTest hw β g := by
  simp only [raiseTest, Pi.add_apply, Pi.smul_apply, smul_eq_mul, leftDeriv_mul_right hw _ h]
  ring

private theorem raiseTest_mem_archDualCut (hw : w.IsReal)
    {χ : ∀ w' : InfinitePlace ℚ, rowIsometrySubgroup₀ w'.Completion →* ℂˣ}
    {β : AdelicGL2 (𝓞 ℚ) ℚ → ℂ} (hβ : β ∈ archDualCutSubmodule ℚ (ArchTypeFamily.ofChar ℚ χ)) :
    raiseTest hw β ∈ archDualCutSubmodule ℚ (ArchTypeFamily.ofChar ℚ χ) := by
  rw [mem_archDualCutSubmodule_ofChar_iff] at hβ ⊢
  intro w' k g
  exact raiseTest_mul_right hw (hβ w' k) g

private theorem inv_raiseTest {hw : w.IsReal}
    (hd₁ : ∀ (d : ArchDir) (γ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ) (y : AdelicGL2 (𝓞 ℚ) ℚ),
      leftDeriv hw d γ y⁻¹ = archDerivAt hw d (fun z => γ z⁻¹) y)
    (β : AdelicGL2 (𝓞 ℚ) ℚ → ℂ) : (fun x => raiseTest hw β x⁻¹) = raiseOp hw (fun z => β z⁻¹) := by
  funext x
  simp only [raiseTest, raiseOp, Pi.add_apply, Pi.smul_apply, hd₁]

private theorem exists_isArchBiFinite_raiseTest {hw : w.IsReal}
    (hd₁ : ∀ (d : ArchDir) (γ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ) (y : AdelicGL2 (𝓞 ℚ) ℚ),
      leftDeriv hw d γ y⁻¹ = archDerivAt hw d (fun z => γ z⁻¹) y)
    (hd₂ : ∀ γ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ, IsFactorizableTestFn ℚ γ → IsArchSmoothAt hw fun z => γ z⁻¹)
    (hW : ∀ (m : ℤ) (ψ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ), IsArchSmoothAt hw ψ →
      HasArchCharacterAt₀ ℚ w (archWeightCharAt hw m) ψ →
        HasArchCharacterAt₀ ℚ w (archWeightCharAt hw (m + 2)) (raiseOp hw ψ))
    {χ : ∀ w' : InfinitePlace ℚ, rowIsometrySubgroup₀ w'.Completion →* ℂˣ} {m : ℤ} (hχ : χ w = archWeightCharAt hw m)
    {β : AdelicGL2 (𝓞 ℚ) ℚ → ℂ} (hβ : IsFactorizableTestFn ℚ β)
    (hbi : IsArchBiFinite ℚ (ArchTypeFamily.ofChar ℚ χ) β) :
    ∃ tys : ArchTypeFamily ℚ, IsArchBiFinite ℚ tys (raiseTest hw β) := by
  let χ' : ∀ w' : InfinitePlace ℚ, rowIsometrySubgroup₀ w'.Completion →* ℂˣ :=
    fun w' => (Subsingleton.elim w w') ▸ archWeightCharAt hw (m + 2)
  refine ⟨catFamily (ArchTypeFamily.ofChar ℚ χ) (ArchTypeFamily.ofChar ℚ χ'), ?_, ?_⟩
  · refine archCutSubmodule_mono ℚ (right_isContainedIn_catFamily _ _) ?_
    have hinv := (mem_archCutSubmodule_ofChar_iff ℚ χ _).mp hbi.1
    rw [inv_raiseTest hd₁, mem_archCutSubmodule_ofChar_iff]
    intro w'
    obtain rfl : w = w' := Subsingleton.elim w w'
    have h := hinv w
    rw [hχ] at h
    exact hW m _ (hd₂ β hβ) h
  · exact archDualCutSubmodule_mono ℚ (left_isContainedIn_catFamily _ _) (raiseTest_mem_archDualCut hw hbi.2)

end

end DerivedBiFinite

namespace CalculusAtPins

p2m_open "NumberField AutomorphicForm~continuous_unipotentGL2~isIsotypicCuspFormAt_of_mem_isotypicCuspSubmodule NumberField.AdelicLevel IsDedekindDomain MeasureTheory"
open scoped Topology

section

variable {K : Type} [Field K] [NumberField K]

private theorem cv_integrable_conv_integrand {φ α : AdelicGL2 (𝓞 K) K → ℂ} (hφ : Continuous φ) (hαc : Continuous α)
    (hαs : HasCompactSupport α) (g : AdelicGL2 (𝓞 K) K) :
    letI := AdelicHaar.glBorel (Fin 2) (𝓞 K) K
    Integrable (fun y => φ (g * y) * α y) (AdelicHaar.adelicGLHaar (Fin 2) (𝓞 K) K) := by
  letI := AdelicHaar.glBorel (Fin 2) (𝓞 K) K
  haveI := AdelicHaar.borelSpace_glBorel (Fin 2) (𝓞 K) K
  haveI := AdelicHaar.isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 K) K
  refine ((hφ.comp (continuous_const.mul continuous_id)).mul hαc).integrable_of_hasCompactSupport (hαs.mono ?_)
  intro y hy
  simp only [Function.mem_support] at hy ⊢
  intro h0
  exact hy (by show φ (g * y) * α y = 0; rw [h0, mul_zero])

private theorem cv_rightConv_add_right {φ α₁ α₂ : AdelicGL2 (𝓞 K) K → ℂ} (hφ : Continuous φ) (hα₁c : Continuous α₁)
    (hα₁s : HasCompactSupport α₁) (hα₂c : Continuous α₂) (hα₂s : HasCompactSupport α₂) :
    rightConv K φ (α₁ + α₂) = rightConv K φ α₁ + rightConv K φ α₂ := by
  letI := AdelicHaar.glBorel (Fin 2) (𝓞 K) K
  funext g
  show (∫ y, φ (g * y) * (α₁ + α₂) y ∂(AdelicHaar.adelicGLHaar (Fin 2) (𝓞 K) K)) =
    (∫ y, φ (g * y) * α₁ y ∂(AdelicHaar.adelicGLHaar (Fin 2) (𝓞 K) K)) +
      ∫ y, φ (g * y) * α₂ y ∂(AdelicHaar.adelicGLHaar (Fin 2) (𝓞 K) K)
  rw [← integral_add (cv_integrable_conv_integrand hφ hα₁c hα₁s g) (cv_integrable_conv_integrand hφ hα₂c hα₂s g)]
  congr 1
  funext y
  rw [Pi.add_apply, mul_add]

private theorem cv_rightConv_smul_right (φ α : AdelicGL2 (𝓞 K) K → ℂ) (c : ℂ) :
    rightConv K φ (c • α) = c • rightConv K φ α := by
  letI := AdelicHaar.glBorel (Fin 2) (𝓞 K) K
  funext g
  show (∫ y, φ (g * y) * (c • α) y ∂(AdelicHaar.adelicGLHaar (Fin 2) (𝓞 K) K)) =
    c * ∫ y, φ (g * y) * α y ∂(AdelicHaar.adelicGLHaar (Fin 2) (𝓞 K) K)
  rw [← integral_const_mul]
  congr 1
  funext y
  rw [Pi.smul_apply, smul_eq_mul]
  ring

end

section

variable {K : Type} [Field K] [NumberField K] {w : InfinitePlace K}

private def convolutionCalculus (hw : w.IsReal) (d : ArchDir) :=
  AutomorphicForm.archDerivAt_rightConv_eq_rightConv_deriv_of_isFactorizableTestFn K hw d

private theorem leftDerivTensor (hw : w.IsReal) : TestCalculus.LeftDerivTensor hw :=
  fun d fa ff hfa => (convolutionCalculus hw d).2.1 fa ff hfa

private theorem isArchSmoothAt_rightConv (hw : w.IsReal) {φ : AdelicGL2 (𝓞 K) K → ℂ} (hφ : Continuous φ)
    {t : AdelicGL2 (𝓞 K) K → ℂ} (ht : IsFactorizableTestFn K t) : IsArchSmoothAt hw (rightConv K φ t) :=
  ((convolutionCalculus hw .H).1 φ t hφ ht).1

private theorem archDerivAt_rightConv (hw : w.IsReal) {φ : AdelicGL2 (𝓞 K) K → ℂ} (hφ : Continuous φ) :
    ∀ (d : ArchDir) (γ : AdelicGL2 (𝓞 K) K → ℂ), IsFactorizableTestFn K γ →
      archDerivAt hw d (rightConv K φ γ) = rightConv K φ (TestCalculus.leftDeriv hw d γ) :=
  fun d γ hγ => ((convolutionCalculus hw d).1 φ γ hφ hγ).2

private theorem archDerivAt_rightConv' (hw : w.IsReal) {φ : AdelicGL2 (𝓞 K) K → ℂ} (hφ : Continuous φ) :
    ∀ (d : ArchDir) (γ : AdelicGL2 (𝓞 K) K → ℂ), IsFactorizableTestFn K γ →
      archDerivAt hw d (rightConv K φ γ) = rightConv K φ (SkewAdjoint.leftDeriv hw d γ) :=
  fun d γ hγ => ((convolutionCalculus hw d).1 φ γ hφ hγ).2

private theorem rightConv_add_right' (φ : AdelicGL2 (𝓞 K) K → ℂ) (hφ : Continuous φ) :
    ∀ γ₁ γ₂ : AdelicGL2 (𝓞 K) K → ℂ, Continuous γ₁ → HasCompactSupport γ₁ → Continuous γ₂ →
      HasCompactSupport γ₂ → rightConv K φ (γ₁ + γ₂) = rightConv K φ γ₁ + rightConv K φ γ₂ :=
  fun _ _ h₁c h₁s h₂c h₂s => cv_rightConv_add_right hφ h₁c h₁s h₂c h₂s

private theorem rightConv_smul_right' (φ : AdelicGL2 (𝓞 K) K → ℂ) :
    ∀ (γ : AdelicGL2 (𝓞 K) K → ℂ) (c : ℂ), rightConv K φ (c • γ) = c • rightConv K φ γ :=
  fun γ c => cv_rightConv_smul_right φ γ c

private theorem rightConv_archDerivAt_mul (hw : w.IsReal) {φ : AdelicGL2 (𝓞 K) K → ℂ} (hφc : Continuous φ)
    (hφs : IsArchSmoothAt hw φ) (hDφ : ∀ d : ArchDir, Continuous (archDerivAt hw d φ)) :
    ∀ (d : ArchDir) (γ₀ wt : AdelicGL2 (𝓞 K) K → ℂ), Continuous γ₀ → HasCompactSupport γ₀ →
      IsArchSmoothAt hw γ₀ → Continuous (archDerivAt hw d γ₀) → Continuous wt →
      (∀ (y : AdelicGL2 (𝓞 K) K) (t : ℝ), wt (y * archFlowAt hw d t) = wt y) →
      rightConv K φ (fun y => archDerivAt hw d γ₀ y * wt y)
        = -rightConv K (archDerivAt hw d φ) (fun y => γ₀ y * wt y) :=
  fun d γ₀ wt hγc hγs hγsm hDγ hwt hinv =>
    (convolutionCalculus hw d).2.2 φ γ₀ wt hφc hφs (hDφ d) hγc hγs hγsm hDγ hwt
      hinv

end

section

variable {K : Type} [Field K] [NumberField K] {w : InfinitePlace K}

private theorem leftDeriv_inv (hw : w.IsReal) :
    ∀ (d : ArchDir) (γ : AdelicGL2 (𝓞 K) K → ℂ) (y : AdelicGL2 (𝓞 K) K),
      SkewAdjoint.leftDeriv hw d γ y⁻¹ = archDerivAt hw d (fun z => γ z⁻¹) y :=
  fun d γ y => InvertedFactor.cv_leftDeriv_inv hw d γ y

private theorem isArchSmoothAt_comp_inv (hw : w.IsReal) :
    ∀ γ : AdelicGL2 (𝓞 K) K → ℂ, IsFactorizableTestFn K γ → IsArchSmoothAt hw fun z => γ z⁻¹ :=
  fun _ hγ => InvertedFactor.cv_isArchSmoothAt_comp_inv hw hγ

end

section

variable {K : Type} [Field K] [NumberField K]

private theorem _root_.CalculusAtPins.isArchBiFinite_tensor_zero (tys : ArchTypeFamily K)
    (ff : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K) → ℂ) : IsArchBiFinite K tys (ReproducingClosure.tensor 0 ff) :=
  WeightPiece.isArchBiFinite_tensor_zero tys ff

p2m_export "CalculusAtPins" "isArchBiFinite_tensor_zero"
private theorem _root_.CalculusAtPins.isArchBiFinite_tensor_add (tys : ArchTypeFamily K)
    (ff : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K) → ℂ) :
    ∀ {fa fb : GL (Fin 2) (InfiniteAdeleRing K) → ℂ}, IsArchBiFinite K tys (ReproducingClosure.tensor fa ff) →
      IsArchBiFinite K tys (ReproducingClosure.tensor fb ff) →
        IsArchBiFinite K tys (ReproducingClosure.tensor (fa + fb) ff) :=
  fun ha hb => WeightPiece.isArchBiFinite_tensor_add ha hb

p2m_export "CalculusAtPins" "isArchBiFinite_tensor_add"
private theorem _root_.CalculusAtPins.isArchBiFinite_tensor_smul (tys : ArchTypeFamily K)
    (ff : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K) → ℂ) :
    ∀ (c : ℂ) {fa : GL (Fin 2) (InfiniteAdeleRing K) → ℂ}, IsArchBiFinite K tys (ReproducingClosure.tensor fa ff) →
      IsArchBiFinite K tys (ReproducingClosure.tensor (c • fa) ff) :=
  fun c _ ha => WeightPiece.isArchBiFinite_tensor_smul c ha

p2m_export "CalculusAtPins" "isArchBiFinite_tensor_smul"
end

section

variable {w : InfinitePlace ℚ}

private theorem hasArchCharacterAt₀_lowerOp (hw : w.IsReal) :
    ∀ (m : ℤ) (ψ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ), IsArchSmoothAt hw ψ →
      HasArchCharacterAt₀ ℚ w (archWeightCharAt hw m) ψ →
        HasArchCharacterAt₀ ℚ w (archWeightCharAt hw (m - 2)) (DerivedBiFinite.lowerOp hw ψ) :=
  fun m _ hψ h =>
    WeightShift.hasArchCharacterAt₀_of_hasRealWeight hw (m - 2)
      (WeightShift.hasRealWeight_lowerOp hψ (WeightShift.hasRealWeight_of_hasArchCharacterAt₀ hw m h))

private theorem hasArchCharacterAt₀_raiseOp (hw : w.IsReal) :
    ∀ (m : ℤ) (ψ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ), IsArchSmoothAt hw ψ →
      HasArchCharacterAt₀ ℚ w (archWeightCharAt hw m) ψ →
        HasArchCharacterAt₀ ℚ w (archWeightCharAt hw (m + 2)) (DerivedBiFinite.raiseOp hw ψ) :=
  fun m _ hψ h =>
    WeightShift.hasArchCharacterAt₀_of_hasRealWeight hw (m + 2)
      (WeightShift.hasRealWeight_raiseOp hψ (WeightShift.hasRealWeight_of_hasArchCharacterAt₀ hw m h))

end

section

open WeightPiece AutomorphicForm.CuspidalConstituent

variable {c u d₁ d₂ : ℝ} {T : Finset (AdelicGL2 (𝓞 ℚ) ℚ)}

private theorem rightConv_mem_isotypicCuspSubmodule_of_mem (ξ : (WeightPiece.windowPins c u d₁ d₂ T).Z →* ℂˣ)
    (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (Φ : HeckeEigensystem ℚ ℂ)
    (hconv : ∀ R : SmoothCuspRealizationAt ℚ (windowPins c u d₁ d₂ T) Φ.toRawCentral, Continuous R.toFun →
      ∀ t : AdelicGL2 (𝓞 ℚ) ℚ → ℂ, IsFactorizableTestFn ℚ t →
        (∀ x : AdelicGL2 (𝓞 ℚ) ℚ, t x ≠ 0 → ∃ a k : AdelicGL2 (𝓞 ℚ) ℚ,
          glFin (𝓞 ℚ) ℚ a = 1 ∧ k ∈ levelOne (𝓞 ℚ) ℚ Φ.level ⊓ finiteAdelicGL2Subgroup ℚ ∧ x = a * k) →
        IsIsotypicCuspFormAt ℚ (windowPins c u d₁ d₂ T) R.centralChar Φ.level R.exceptionalSet Φ
          (rightConv ℚ R.toFun t))
    {ψ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ}
    (hψ : ψ ∈ isotypicCuspSubmodule ℚ (WeightPiece.windowPins c u d₁ d₂ T) ξ Φ.level S Φ) :
    ∀ t : AdelicGL2 (𝓞 ℚ) ℚ → ℂ, IsFactorizableTestFn ℚ t →
      (∀ x : AdelicGL2 (𝓞 ℚ) ℚ, t x ≠ 0 → ∃ a k : AdelicGL2 (𝓞 ℚ) ℚ,
        glFin (𝓞 ℚ) ℚ a = 1 ∧ k ∈ levelOne (𝓞 ℚ) ℚ Φ.level ⊓ finiteAdelicGL2Subgroup ℚ ∧ x = a * k) →
      rightConv ℚ ψ t ∈ isotypicCuspSubmodule ℚ (WeightPiece.windowPins c u d₁ d₂ T) ξ Φ.level S Φ := by
  intro t ht hts
  obtain ⟨htc, htcs⟩ := AutomorphicForm.continuous_and_hasCompactSupport_of_isFactorizableTestFn ℚ _ ht
  refine WeightPiece.rightConv_mem_isotypicCuspSubmodule htc htcs (fun v hv => ?_) hψ
  by_cases hv0 : v = 0
  · subst hv0
    rw [WeightPiece.rightConv_zero_left']
    exact Submodule.zero_mem _
  · exact (hconv (hv.toRealization hv0) hv.continuous _ ht hts).mem_isotypicCuspSubmodule

private theorem rightConv_mem_weightPiece (ξ : (WeightPiece.windowPins c u d₁ d₂ T).Z →* ℂˣ)
    (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (Φ : HeckeEigensystem ℚ ℂ) {V : Submodule ℂ (AdelicGL2 (𝓞 ℚ) ℚ → ℂ)}
    (hV : IsCuspConstituent ℚ (WeightPiece.windowPins c u d₁ d₂ T) ξ V)
    (χ : ∀ w : InfinitePlace ℚ, rowIsometrySubgroup₀ w.Completion →* ℂˣ)
    (hconv : ∀ R : SmoothCuspRealizationAt ℚ (windowPins c u d₁ d₂ T) Φ.toRawCentral, Continuous R.toFun →
      ∀ t : AdelicGL2 (𝓞 ℚ) ℚ → ℂ, IsFactorizableTestFn ℚ t →
        (∀ x : AdelicGL2 (𝓞 ℚ) ℚ, t x ≠ 0 → ∃ a k : AdelicGL2 (𝓞 ℚ) ℚ,
          glFin (𝓞 ℚ) ℚ a = 1 ∧ k ∈ levelOne (𝓞 ℚ) ℚ Φ.level ⊓ finiteAdelicGL2Subgroup ℚ ∧ x = a * k) →
        IsIsotypicCuspFormAt ℚ (windowPins c u d₁ d₂ T) R.centralChar Φ.level R.exceptionalSet Φ
          (rightConv ℚ R.toFun t))
    {t : AdelicGL2 (𝓞 ℚ) ℚ → ℂ} (ht : IsFactorizableTestFn ℚ t)
    (hts : ∀ x : AdelicGL2 (𝓞 ℚ) ℚ, t x ≠ 0 → ∃ a k : AdelicGL2 (𝓞 ℚ) ℚ,
      glFin (𝓞 ℚ) ℚ a = 1 ∧ k ∈ levelOne (𝓞 ℚ) ℚ Φ.level ⊓ finiteAdelicGL2Subgroup ℚ ∧ x = a * k)
    (hbi : IsArchBiFinite ℚ (ArchTypeFamily.ofChar ℚ χ) t)
    {f : AdelicGL2 (𝓞 ℚ) ℚ → ℂ}
    (hf : f ∈ WeightPiece.weightPiece (WeightPiece.windowPins c u d₁ d₂ T) ξ Φ.level S Φ V χ) :
    rightConv ℚ f t ∈ WeightPiece.weightPiece (WeightPiece.windowPins c u d₁ d₂ T) ξ Φ.level S Φ V χ := by
  obtain ⟨hfV, hfiso, -⟩ := WeightPiece.mem_weightPiece_iff.1 hf
  exact WeightPiece.mem_weightPiece_iff.2
    ⟨hV.1.rightConv_mem _ _ ht hbi f hfV,
      rightConv_mem_isotypicCuspSubmodule_of_mem ξ S Φ hconv hfiso t ht hts,
      WeightPiece.rightConv_mem_archCutSubmodule_ofChar χ f hbi⟩

end

end CalculusAtPins

open IsDedekindDomain NumberField MeasureTheory Matrix
open NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open NumberField.InfinitePlace.Completion
p2m_open "AutomorphicForm~continuous_unipotentGL2~isIsotypicCuspFormAt_of_mem_isotypicCuspSubmodule AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering AutomorphicForm.CuspidalConstituent"
open LanglandsTunnell LanglandsTunnell.Converse NumberField.TateGlobal

namespace MinimalWeightVector

section

variable {w : InfinitePlace ℚ} (hw : w.IsReal)

private def wtFam (m : ℤ) : ∀ w' : InfinitePlace ℚ, rowIsometrySubgroup₀ w'.Completion →* ℂˣ :=
  fun w' => (Subsingleton.elim w w') ▸ archWeightCharAt hw m

private theorem mem_archCutSubmodule_wtFam_iff (m : ℤ) (f : AdelicGL2 (𝓞 ℚ) ℚ → ℂ) :
    f ∈ archCutSubmodule ℚ (ArchTypeFamily.ofChar ℚ (wtFam hw m)) ↔
      HasArchCharacterAt₀ ℚ w (archWeightCharAt hw m) f := by
  rw [mem_archCutSubmodule_ofChar_iff]
  constructor
  · intro h
    exact h w
  · intro h w'
    obtain rfl : w = w' := Subsingleton.elim w w'
    exact h

end

section

variable (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 ℚ) ℚ)) (Φ : HeckeEigensystem ℚ ℂ)

private def LevelSupported (t : AdelicGL2 (𝓞 ℚ) ℚ → ℂ) : Prop :=
  ∀ x : AdelicGL2 (𝓞 ℚ) ℚ, t x ≠ 0 → ∃ a k : AdelicGL2 (𝓞 ℚ) ℚ,
    glFin (𝓞 ℚ) ℚ a = 1 ∧ k ∈ levelOne (𝓞 ℚ) ℚ Φ.level ⊓ finiteAdelicGL2Subgroup ℚ ∧ x = a * k

private structure Inputs {w : InfinitePlace ℚ} (hw : w.IsReal) : Prop where
  conv_isotypic :
    ∀ R : SmoothCuspRealizationAt ℚ (WeightPiece.windowPins c u d₁ d₂ T) Φ.toRawCentral, Continuous R.toFun →
      ∀ t : AdelicGL2 (𝓞 ℚ) ℚ → ℂ, IsFactorizableTestFn ℚ t →
        (∀ x : AdelicGL2 (𝓞 ℚ) ℚ, t x ≠ 0 → ∃ a k : AdelicGL2 (𝓞 ℚ) ℚ,
          glFin (𝓞 ℚ) ℚ a = 1 ∧ k ∈ levelOne (𝓞 ℚ) ℚ Φ.level ⊓ finiteAdelicGL2Subgroup ℚ ∧ x = a * k) →
        IsIsotypicCuspFormAt ℚ (WeightPiece.windowPins c u d₁ d₂ T) R.centralChar Φ.level R.exceptionalSet Φ
          (rightConv ℚ R.toFun t)
  casimir_translate : ∀ φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ, IsArchSmoothAt hw φ → ∀ m : GL (Fin 2) ℝ,
      archCasimirAt hw (fun x => φ (x * archRealGLAt hw m)) = fun x => archCasimirAt hw φ (x * archRealGLAt hw m)
  approx : ∀ (tys : ArchTypeFamily ℚ) (f : AdelicGL2 (𝓞 ℚ) ℚ → ℂ), Continuous f →
      (∀ g : AdelicGL2 (𝓞 ℚ) ℚ, ∀ k ∈ levelOne (𝓞 ℚ) ℚ Φ.level ⊓ finiteAdelicGL2Subgroup ℚ, f (g * k) = f g) →
      f ∈ archCutSubmodule ℚ tys →
      ∃ (ff : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ) → ℂ) (fa : ℕ → (GL (Fin 2) (InfiniteAdeleRing ℚ) → ℂ)),
        IsFinTestFactor ℚ ff ∧
        (∀ x : AdelicGL2 (𝓞 ℚ) ℚ, ff (glFin (𝓞 ℚ) ℚ x) ≠ 0 → ∃ a k : AdelicGL2 (𝓞 ℚ) ℚ,
          glFin (𝓞 ℚ) ℚ a = 1 ∧ k ∈ levelOne (𝓞 ℚ) ℚ Φ.level ⊓ finiteAdelicGL2Subgroup ℚ ∧ x = a * k) ∧
        (∀ n, IsArchTestFactor ℚ (fa n)) ∧
        (∀ n, IsArchBiFinite ℚ tys fun g => fa n (glArch (𝓞 ℚ) ℚ g) * ff (glFin (𝓞 ℚ) ℚ g)) ∧
        ∀ g, Filter.Tendsto
          (fun n => rightConv ℚ f (fun x => fa n (glArch (𝓞 ℚ) ℚ x) * ff (glFin (𝓞 ℚ) ℚ x)) g)
          Filter.atTop (nhds (f g))

end

section

variable {c u d₁ d₂ : ℝ} {T : Finset (AdelicGL2 (𝓞 ℚ) ℚ)} {Φ : HeckeEigensystem ℚ ℂ} {w : InfinitePlace ℚ}
  {hw : w.IsReal} (hin : Inputs c u d₁ d₂ T Φ hw)

private theorem exists_finset_dvd_level (Φ : HeckeEigensystem ℚ ℂ) : ∃ SK : Finset (HeightOneSpectrum (𝓞 ℚ)),
    ∀ p : HeightOneSpectrum (𝓞 ℚ), p.asIdeal ∣ Φ.level → p ∈ SK := by
  have hfin : {p : HeightOneSpectrum (𝓞 ℚ) | p.asIdeal ∣ Φ.level}.Finite := Ideal.finite_factors Φ.level_ne_bot
  exact ⟨hfin.toFinset, fun p hp => hfin.mem_toFinset.2 hp⟩

private theorem ringHom_eq_id (f : 𝓞 ℚ →+* 𝓞 ℚ) : f = RingHom.id (𝓞 ℚ) := by
  have h : (Rat.ringOfIntegersEquiv.toRingHom.comp f).comp Rat.ringOfIntegersEquiv.symm.toRingHom
      = Rat.ringOfIntegersEquiv.toRingHom.comp Rat.ringOfIntegersEquiv.symm.toRingHom := Subsingleton.elim _ _
  ext x
  have hx := congrArg (fun g : ℤ →+* ℤ => g (Rat.ringOfIntegersEquiv x)) h
  simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, RingEquiv.symm_apply_apply]
    at hx
  simpa using Rat.ringOfIntegersEquiv.injective hx

private theorem ideal_map_self (f : 𝓞 ℚ →+* 𝓞 ℚ) (N : Ideal (𝓞 ℚ)) : Ideal.map f N = N := by
  rw [ringHom_eq_id f, Ideal.map_id]

private abbrev piece (hw : w.IsReal) (ξ : (WeightPiece.windowPins c u d₁ d₂ T).Z →* ℂˣ)
    (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (Φ : HeckeEigensystem ℚ ℂ) (V : Submodule ℂ (AdelicGL2 (𝓞 ℚ) ℚ → ℂ))
    (k : ℤ) : Submodule ℂ (AdelicGL2 (𝓞 ℚ) ℚ → ℂ) :=
  WeightPiece.weightPiece (WeightPiece.windowPins c u d₁ d₂ T) ξ Φ.level S Φ V (wtFam hw k)

private theorem mem_piece_iff {ξ : (WeightPiece.windowPins c u d₁ d₂ T).Z →* ℂˣ}
    {S : Finset (HeightOneSpectrum (𝓞 ℚ))} {V : Submodule ℂ (AdelicGL2 (𝓞 ℚ) ℚ → ℂ)} {k : ℤ}
    {f : AdelicGL2 (𝓞 ℚ) ℚ → ℂ} :
    f ∈ piece hw ξ S Φ V k ↔
      f ∈ V ∧ f ∈ isotypicCuspSubmodule ℚ (WeightPiece.windowPins c u d₁ d₂ T) ξ Φ.level S Φ ∧
        HasArchCharacterAt₀ ℚ w (archWeightCharAt hw k) f := by
  rw [piece, WeightPiece.mem_weightPiece_iff, mem_archCutSubmodule_wtFam_iff]

private theorem levelSupported_tensor {ff : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ) → ℂ}
    (hffs : ∀ x : AdelicGL2 (𝓞 ℚ) ℚ, ff (glFin (𝓞 ℚ) ℚ x) ≠ 0 → ∃ a k : AdelicGL2 (𝓞 ℚ) ℚ,
      glFin (𝓞 ℚ) ℚ a = 1 ∧ k ∈ levelOne (𝓞 ℚ) ℚ Φ.level ⊓ finiteAdelicGL2Subgroup ℚ ∧ x = a * k)
    (a : GL (Fin 2) (InfiniteAdeleRing ℚ) → ℂ) : LevelSupported Φ (ReproducingClosure.tensor a ff) :=
  fun x hx => hffs x (right_ne_zero_of_mul hx)

include hin in

private theorem exists_piece_ne_bot (hd : d₁ < d₂)
    (hcov : CoversModCentre ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂))
    (R : SmoothCuspRealizationAt ℚ (WeightPiece.windowPins c u d₁ d₂ T) Φ.toRawCentral) (hR : Continuous R.toFun) :
    ∃ (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (V : Submodule ℂ (AdelicGL2 (𝓞 ℚ) ℚ → ℂ)) (k : ℤ),
      R.exceptionalSet ⊆ S ∧ IsCuspConstituent ℚ (WeightPiece.windowPins c u d₁ d₂ T) R.centralChar V ∧
        (∃ ψ₀ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ,
          IsIsotypicCuspFormAt ℚ (WeightPiece.windowPins c u d₁ d₂ T) R.centralChar Φ.level S Φ ψ₀) ∧
        piece hw R.centralChar S Φ V k ≠ ⊥ := by
  obtain ⟨S, V, ψ, tys, hS, hV, hψV, hψ0, hψiso, hψtys⟩ :=
    ConstituentSupply.exists_isCuspConstituent_and_isIsotypicCuspFormAt_and_mem_archCutSubmodule c u d₁ d₂ T hd hcov Φ
      R hR
  refine ⟨S, V, ?_⟩
  obtain ⟨ff, fa, hff, hffs, hfa, hbi, hlim⟩ :=
    hin.approx tys ψ hψiso.continuous (fun g k hk => hψiso.level_invariant g k hk) hψtys
  obtain ⟨g₀, hg₀⟩ := Function.ne_iff.mp hψ0
  obtain ⟨n, hn⟩ := ((hlim g₀).eventually_ne hg₀).exists
  have hfact : IsFactorizableTestFn ℚ fun x => fa n (glArch (𝓞 ℚ) ℚ x) * ff (glFin (𝓞 ℚ) ℚ x) :=
    ReproducingClosure.isFactorizableTestFn_tensor (hfa n) hff
  have hne : rightConv ℚ ψ (fun x => fa n (glArch (𝓞 ℚ) ℚ x) * ff (glFin (𝓞 ℚ) ℚ x)) ≠ 0 :=
    fun h => hn (congrFun h g₀)
  have hsupp : ∀ x, (fun x => fa n (glArch (𝓞 ℚ) ℚ x) * ff (glFin (𝓞 ℚ) ℚ x)) x ≠ 0 → ∃ a k : AdelicGL2 (𝓞 ℚ) ℚ,
      glFin (𝓞 ℚ) ℚ a = 1 ∧ k ∈ levelOne (𝓞 ℚ) ℚ Φ.level ⊓ finiteAdelicGL2Subgroup ℚ ∧ x = a * k :=
    fun x hx => hffs x (right_ne_zero_of_mul hx)
  haveI := TranslateHull.finiteDimensional_span_leftTranslates_of_isArchBiFinite ℚ w (hbi n)
  obtain ⟨U, hUfin, hUne, hUI, hUV, hUsm, hUstab⟩ :=
    RotationSpan.exists_rotationSpan ℚ hw ψ hψiso.continuous _ hfact
      (levelOne (𝓞 ℚ) ℚ Φ.level ⊓ finiteAdelicGL2Subgroup ℚ) hsupp hne
      (isotypicCuspSubmodule ℚ (WeightPiece.windowPins c u d₁ d₂ T) R.centralChar Φ.level S Φ)
      (CalculusAtPins.rightConv_mem_isotypicCuspSubmodule_of_mem R.centralChar S Φ hin.conv_isotypic
        hψiso.mem_isotypicCuspSubmodule)
      V (hV.1.rightConv_mem _ tys hfact (hbi n) ψ hψV) (fun φ hφ r => hV.1.rightTranslate_arch_mem w r φ hφ)
      (fun t ht => CalculusAtPins.isArchSmoothAt_rightConv hw hψiso.continuous ht)
  haveI := hUfin
  obtain ⟨φ₁, hφ₁U, hφ₁0, k, hk⟩ := RotationWeight.exists_mem_ne_zero_hasArchCharacterAt₀ hw U hUne hUsm hUstab
  exact ⟨k, hS, hV, ⟨ψ, hψiso⟩, (Submodule.ne_bot_iff _).2 ⟨φ₁, mem_piece_iff.2 ⟨hUV hφ₁U, hUI hφ₁U, hk⟩, hφ₁0⟩⟩

variable {ξ : (WeightPiece.windowPins c u d₁ d₂ T).Z →* ℂˣ} {S : Finset (HeightOneSpectrum (𝓞 ℚ))}
  {V : Submodule ℂ (AdelicGL2 (𝓞 ℚ) ℚ → ℂ)} (hV : IsCuspConstituent ℚ (WeightPiece.windowPins c u d₁ d₂ T) ξ V)

include hin hV in

private theorem exists_reproducing (hd : d₁ < d₂)
    (hcov : CoversModCentre ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂)) {k : ℤ}
    {f : AdelicGL2 (𝓞 ℚ) ℚ → ℂ} (hf : f ∈ piece hw ξ S Φ V k) :
    ∃ β : AdelicGL2 (𝓞 ℚ) ℚ → ℂ, IsFactorizableTestFn ℚ β ∧ LevelSupported Φ β ∧
      IsArchBiFinite ℚ (ArchTypeFamily.ofChar ℚ (wtFam hw k)) β ∧ rightConv ℚ f β = f := by
  obtain ⟨hfV, hfiso, hfk⟩ := mem_piece_iff.1 hf
  have hfc : Continuous f := continuous_of_mem_isotypicCuspSubmodule hfiso
  have hlev := WeightPiece.isotypicCuspSubmodule_le_levelInvariantSubmodule _ ξ Φ.level S Φ hfiso
  obtain ⟨ff, fa, hff, hffs, hfa, hbi, hlim⟩ := hin.approx (ArchTypeFamily.ofChar ℚ (wtFam hw k)) f hfc
    (fun g k hk => hlev g k hk) ((mem_archCutSubmodule_wtFam_iff hw k f).2 hfk)
  haveI : FiniteDimensional ℂ (piece hw ξ S Φ V k) :=
    WeightPiece.finiteDimensional_weightPiece_window c u d₁ d₂ T hd hcov ξ Φ.level Φ.level_ne_bot S Φ V hV (wtFam hw k)
  obtain ⟨a, ha, hQa, hrepro⟩ := ReproducingClosure.exists_isFactorizableTestFn_rightConv_eq
    (fun a => IsArchBiFinite ℚ (ArchTypeFamily.ofChar ℚ (wtFam hw k)) (ReproducingClosure.tensor a ff))
    (CalculusAtPins.isArchBiFinite_tensor_zero (ArchTypeFamily.ofChar ℚ (wtFam hw k)) ff)
    (CalculusAtPins.isArchBiFinite_tensor_add (ArchTypeFamily.ofChar ℚ (wtFam hw k)) ff)
    (CalculusAtPins.isArchBiFinite_tensor_smul (ArchTypeFamily.ofChar ℚ (wtFam hw k)) ff) f hff
    (CalculusAtPins.rightConv_add_right' f hfc) (CalculusAtPins.rightConv_smul_right' f) (piece hw ξ S Φ V k)
    (fun a ha hQa => CalculusAtPins.rightConv_mem_weightPiece ξ S Φ hV _ hin.conv_isotypic
      (ReproducingClosure.isFactorizableTestFn_tensor ha hff) (levelSupported_tensor hffs a) hQa hf)
    fa hfa (fun n => hbi n) (fun g => hlim g)
  exact ⟨ReproducingClosure.tensor a ff, ReproducingClosure.isFactorizableTestFn_tensor ha hff,
    levelSupported_tensor hffs a, hQa, hrepro⟩

include hin hV in

private theorem isArchSmoothAt_of_mem_piece (hd : d₁ < d₂)
    (hcov : CoversModCentre ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂)) {k : ℤ}
    {f : AdelicGL2 (𝓞 ℚ) ℚ → ℂ} (hf : f ∈ piece hw ξ S Φ V k) : IsArchSmoothAt hw f := by
  obtain ⟨β, hβ, -, -, hrepro⟩ := exists_reproducing hin hV hd hcov hf
  rw [← hrepro]
  exact CalculusAtPins.isArchSmoothAt_rightConv hw
    (continuous_of_mem_isotypicCuspSubmodule (mem_piece_iff.1 hf).2.1) hβ

include hin hV in

private theorem archCasimirAt_mem_piece (hd : d₁ < d₂)
    (hcov : CoversModCentre ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂)) {k : ℤ}
    {f : AdelicGL2 (𝓞 ℚ) ℚ → ℂ} (hf : f ∈ piece hw ξ S Φ V k) : archCasimirAt hw f ∈ piece hw ξ S Φ V k := by
  obtain ⟨β, hβ, hβs, hβbi, hrepro⟩ := exists_reproducing hin hV hd hcov hf
  have hfc : Continuous f := continuous_of_mem_isotypicCuspSubmodule (mem_piece_iff.1 hf).2.1
  have hΩ : archCasimirAt hw f = rightConv ℚ f (TestCalculus.casimirTest hw β) := by
    conv_lhs => rw [← hrepro]
    exact TestCalculus.archCasimirAt_rightConv (CalculusAtPins.leftDerivTensor hw) f
      (CalculusAtPins.archDerivAt_rightConv hw hfc) (CalculusAtPins.rightConv_add_right' f hfc)
      (CalculusAtPins.rightConv_smul_right' f) hβ
  have hbi' : IsArchBiFinite ℚ (ArchTypeFamily.ofChar ℚ (wtFam hw k)) (TestCalculus.casimirTest hw β) :=
    DerivedBiFinite.isArchBiFinite_casimirTest (CalculusAtPins.leftDeriv_inv hw)
      (CalculusAtPins.isArchSmoothAt_comp_inv hw) hin.casimir_translate hβ hβbi
  rw [hΩ]
  exact CalculusAtPins.rightConv_mem_weightPiece ξ S Φ hV _ hin.conv_isotypic
    (TestCalculus.isFactorizableTestFn_casimirTest (CalculusAtPins.leftDerivTensor hw) hβ)
    (TestCalculus.exists_eq_mul_of_casimirTest_ne_zero hw (levelOne (𝓞 ℚ) ℚ Φ.level ⊓ finiteAdelicGL2Subgroup ℚ) hβs)
    hbi' hf

include hin hV in

private theorem lowerOp_mem_piece (hd : d₁ < d₂)
    (hcov : CoversModCentre ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂)) {k : ℤ}
    {f : AdelicGL2 (𝓞 ℚ) ℚ → ℂ} (hf : f ∈ piece hw ξ S Φ V k) :
    TestCalculus.lowerOp hw f ∈ piece hw ξ S Φ V (k - 2) := by
  obtain ⟨β, hβ, hβs, hβbi, hrepro⟩ := exists_reproducing hin hV hd hcov hf
  obtain ⟨hfV, hfiso, hfk⟩ := mem_piece_iff.1 hf
  have hfc : Continuous f := continuous_of_mem_isotypicCuspSubmodule hfiso
  have hX : TestCalculus.lowerOp hw f = rightConv ℚ f (TestCalculus.lowerTest hw β) := by
    conv_lhs => rw [← hrepro]
    exact TestCalculus.lowerOp_rightConv (CalculusAtPins.leftDerivTensor hw) f
      (CalculusAtPins.archDerivAt_rightConv hw hfc) (CalculusAtPins.rightConv_add_right' f hfc)
      (CalculusAtPins.rightConv_smul_right' f) hβ
  obtain ⟨tys, htys⟩ : ∃ tys : ArchTypeFamily ℚ, IsArchBiFinite ℚ tys (TestCalculus.lowerTest hw β) :=
    DerivedBiFinite.exists_isArchBiFinite_lowerTest (CalculusAtPins.leftDeriv_inv hw)
      (CalculusAtPins.isArchSmoothAt_comp_inv hw) (CalculusAtPins.hasArchCharacterAt₀_lowerOp hw) (m := k) rfl hβ hβbi
  have hweight : HasArchCharacterAt₀ ℚ w (archWeightCharAt hw (k - 2)) (TestCalculus.lowerOp hw f) :=
    CalculusAtPins.hasArchCharacterAt₀_lowerOp hw k f (isArchSmoothAt_of_mem_piece hin hV hd hcov hf) hfk
  refine mem_piece_iff.2 ⟨?_, ?_, hweight⟩
  · rw [hX]
    exact hV.1.rightConv_mem _ tys (TestCalculus.isFactorizableTestFn_lowerTest (CalculusAtPins.leftDerivTensor hw) hβ)
      htys f hfV
  · rw [hX]
    exact CalculusAtPins.rightConv_mem_isotypicCuspSubmodule_of_mem ξ S Φ hin.conv_isotypic hfiso _
      (TestCalculus.isFactorizableTestFn_lowerTest (CalculusAtPins.leftDerivTensor hw) hβ)
      (TestCalculus.exists_eq_mul_of_lowerTest_ne_zero hw (levelOne (𝓞 ℚ) ℚ Φ.level ⊓ finiteAdelicGL2Subgroup ℚ) hβs)

include hin hV in

private theorem raiseOp_mem_piece (hd : d₁ < d₂)
    (hcov : CoversModCentre ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂)) {k : ℤ}
    {f : AdelicGL2 (𝓞 ℚ) ℚ → ℂ} (hf : f ∈ piece hw ξ S Φ V k) :
    TestCalculus.raiseOp hw f ∈ piece hw ξ S Φ V (k + 2) := by
  obtain ⟨β, hβ, hβs, hβbi, hrepro⟩ := exists_reproducing hin hV hd hcov hf
  obtain ⟨hfV, hfiso, hfk⟩ := mem_piece_iff.1 hf
  have hfc : Continuous f := continuous_of_mem_isotypicCuspSubmodule hfiso
  have hX : TestCalculus.raiseOp hw f = rightConv ℚ f (TestCalculus.raiseTest hw β) := by
    conv_lhs => rw [← hrepro]
    exact TestCalculus.raiseOp_rightConv (CalculusAtPins.leftDerivTensor hw) f
      (CalculusAtPins.archDerivAt_rightConv hw hfc) (CalculusAtPins.rightConv_add_right' f hfc)
      (CalculusAtPins.rightConv_smul_right' f) hβ
  obtain ⟨tys, htys⟩ : ∃ tys : ArchTypeFamily ℚ, IsArchBiFinite ℚ tys (TestCalculus.raiseTest hw β) :=
    DerivedBiFinite.exists_isArchBiFinite_raiseTest (CalculusAtPins.leftDeriv_inv hw)
      (CalculusAtPins.isArchSmoothAt_comp_inv hw) (CalculusAtPins.hasArchCharacterAt₀_raiseOp hw) (m := k) rfl hβ hβbi
  have hweight : HasArchCharacterAt₀ ℚ w (archWeightCharAt hw (k + 2)) (TestCalculus.raiseOp hw f) :=
    CalculusAtPins.hasArchCharacterAt₀_raiseOp hw k f (isArchSmoothAt_of_mem_piece hin hV hd hcov hf) hfk
  refine mem_piece_iff.2 ⟨?_, ?_, hweight⟩
  · rw [hX]
    exact hV.1.rightConv_mem _ tys (TestCalculus.isFactorizableTestFn_raiseTest (CalculusAtPins.leftDerivTensor hw) hβ)
      htys f hfV
  · rw [hX]
    exact CalculusAtPins.rightConv_mem_isotypicCuspSubmodule_of_mem ξ S Φ hin.conv_isotypic hfiso _
      (TestCalculus.isFactorizableTestFn_raiseTest (CalculusAtPins.leftDerivTensor hw) hβ)
      (TestCalculus.exists_eq_mul_of_raiseTest_ne_zero hw (levelOne (𝓞 ℚ) ℚ Φ.level ⊓ finiteAdelicGL2Subgroup ℚ) hβs)

include hin hV in

private theorem reflectJ_mem_piece (hd : d₁ < d₂)
    (hcov : CoversModCentre ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂)) {k : ℤ}
    {f : AdelicGL2 (𝓞 ℚ) ℚ → ℂ} (hf : f ∈ piece hw ξ S Φ V k) : WeightShift.reflectJ hw f ∈ piece hw ξ S Φ V (-k) := by
  obtain ⟨β, hβ, hβs, hβbi, hrepro⟩ := exists_reproducing hin hV hd hcov hf
  obtain ⟨hfV, hfiso, hfk⟩ := mem_piece_iff.1 hf
  have hJ : glFin (𝓞 ℚ) ℚ (archRealGLAt hw UpperHalfPlane.J) = 1 := glFin_adelicArchGLIncl ℚ _
  have hR : WeightShift.reflectJ hw f = rightConv ℚ f fun y => β ((archRealGLAt hw UpperHalfPlane.J)⁻¹ * y) := by
    funext x
    calc WeightShift.reflectJ hw f x = rightConv ℚ f β (x * archRealGLAt hw UpperHalfPlane.J) := by
          rw [hrepro]
          rfl
      _ = _ := rightConv_apply_mul_eq_rightConv_comp_inv_mul_apply ℚ f β x _
  have hβ' : IsFactorizableTestFn ℚ fun y => β ((archRealGLAt hw UpperHalfPlane.J)⁻¹ * y) :=
    isFactorizableTestFn_comp_inv_mul_of_isFactorizableTestFn ℚ β hβ _
  have hβ's : LevelSupported Φ fun y => β ((archRealGLAt hw UpperHalfPlane.J)⁻¹ * y) := by
    intro y hy
    obtain ⟨a, k, ha, hk, hak⟩ := hβs _ hy
    refine ⟨archRealGLAt hw UpperHalfPlane.J * a, k, by rw [map_mul, hJ, ha, one_mul], hk, ?_⟩
    rw [mul_assoc, ← hak, mul_inv_cancel_left]
  have hinv : (fun x : AdelicGL2 (𝓞 ℚ) ℚ => β ((archRealGLAt hw UpperHalfPlane.J)⁻¹ * x⁻¹))
      = WeightShift.reflectJ hw fun z => β z⁻¹ := by
    funext x
    show β _ = β (x * archRealGLAt hw UpperHalfPlane.J)⁻¹
    rw [_root_.mul_inv_rev]
  have hbi' : IsArchBiFinite ℚ
      (DerivedBiFinite.catFamily (ArchTypeFamily.ofChar ℚ (wtFam hw (-k))) (ArchTypeFamily.ofChar ℚ (wtFam hw k)))
      fun y => β ((archRealGLAt hw UpperHalfPlane.J)⁻¹ * y) := by
    refine ⟨archCutSubmodule_mono ℚ (DerivedBiFinite.left_isContainedIn_catFamily _ _) ?_,
      archDualCutSubmodule_mono ℚ (DerivedBiFinite.right_isContainedIn_catFamily _ _) ?_⟩
    · show (fun x : AdelicGL2 (𝓞 ℚ) ℚ => β ((archRealGLAt hw UpperHalfPlane.J)⁻¹ * x⁻¹)) ∈ _
      rw [hinv, mem_archCutSubmodule_wtFam_iff]
      exact WeightShift.hasArchCharacterAt₀_of_hasRealWeight hw (-k) (WeightShift.hasRealWeight_reflectJ
        (WeightShift.hasRealWeight_of_hasArchCharacterAt₀ hw k ((mem_archCutSubmodule_wtFam_iff hw k _).1 hβbi.1)))
    · have hdual := (DerivedBiFinite.mem_archDualCutSubmodule_ofChar_iff _ β).1 hβbi.2
      refine (DerivedBiFinite.mem_archDualCutSubmodule_ofChar_iff _ _).2 fun w' r g => ?_
      show β (_ * (g * rowIsometryInclAt₀ ℚ w' r)) = _ * β (_ * g)
      rw [← mul_assoc]
      exact hdual w' r _
  refine mem_piece_iff.2 ⟨?_, ?_, ?_⟩
  · rw [hR]
    exact hV.1.rightConv_mem _ _ hβ' hbi' f hfV
  · rw [hR]
    exact CalculusAtPins.rightConv_mem_isotypicCuspSubmodule_of_mem ξ S Φ hin.conv_isotypic hfiso _ hβ' hβ's
  · exact WeightShift.hasArchCharacterAt₀_of_hasRealWeight hw (-k)
      (WeightShift.hasRealWeight_reflectJ (WeightShift.hasRealWeight_of_hasArchCharacterAt₀ hw k hfk))

include hin hV in

private theorem exists_minimalWeight_eigenvector (hd : d₁ < d₂)
    (hcov : CoversModCentre ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂)) {k : ℤ}
    (hk : piece hw ξ S Φ V k ≠ ⊥) :
    ∃ k₀ : ℕ, (∀ m : ℤ, m.natAbs < k₀ → piece hw ξ S Φ V m = ⊥) ∧
      ∃ (lam : ℂ) (ψ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ),
        ψ ∈ piece hw ξ S Φ V (k₀ : ℤ) ∧ ψ ≠ 0 ∧ archCasimirAt hw ψ = lam • ψ := by
  obtain ⟨k₀, hk₀, hmin⟩ := MinimalWeight.exists_minimal_natAbs (P := fun m => piece hw ξ S Φ V m ≠ ⊥) hk
  refine ⟨k₀, fun m hm => by simpa using hmin m hm, ?_⟩
  have hE : piece hw ξ S Φ V (k₀ : ℤ) ≠ ⊥ := by
    rcases hk₀ with h | h
    · exact h
    · obtain ⟨χ, hχ, hχ0⟩ := (Submodule.ne_bot_iff _).1 h
      refine (Submodule.ne_bot_iff _).2 ⟨WeightShift.reflectJ hw χ, ?_, ?_⟩
      · simpa using reflectJ_mem_piece hin hV hd hcov hχ
      · intro h0
        apply hχ0
        funext x
        rw [← WeightShift.reflectJ_apply_mul_J hw χ x, h0]
        rfl
  haveI : FiniteDimensional ℂ (piece hw ξ S Φ V (k₀ : ℤ)) :=
    WeightPiece.finiteDimensional_weightPiece_window c u d₁ d₂ T hd hcov ξ Φ.level Φ.level_ne_bot S Φ V hV
      (wtFam hw k₀)
  obtain ⟨lam, ψ, hψ, hψ0, hΩ⟩ := StableSubspace.exists_mem_ne_zero_apply_eq_smul (piece hw ξ S Φ V (k₀ : ℤ)) hE
    (archCasimirAt hw)
    (fun x hx y hy => archCasimirAt_add (isArchSmoothAt_of_mem_piece hin hV hd hcov hx)
      (isArchSmoothAt_of_mem_piece hin hV hd hcov hy))
    (fun a x _ => archCasimirAt_smul hw a x) (fun x hx => archCasimirAt_mem_piece hin hV hd hcov hx)
  exact ⟨lam, ψ, hψ, hψ0, hΩ⟩

end

section

variable {c u d₁ d₂ : ℝ} {T : Finset (AdelicGL2 (𝓞 ℚ) ℚ)} {Φ : HeckeEigensystem ℚ ℂ} {w : InfinitePlace ℚ}
  {hw : w.IsReal} (hin : Inputs c u d₁ d₂ T Φ hw)
  {ξ : (WeightPiece.windowPins c u d₁ d₂ T).Z →* ℂˣ} {S : Finset (HeightOneSpectrum (𝓞 ℚ))}
  {V : Submodule ℂ (AdelicGL2 (𝓞 ℚ) ℚ → ℂ)} (hV : IsCuspConstituent ℚ (WeightPiece.windowPins c u d₁ d₂ T) ξ V)
  {ψ₀ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ}
  (hψ₀ : IsIsotypicCuspFormAt ℚ (WeightPiece.windowPins c u d₁ d₂ T) ξ Φ.level S Φ ψ₀)

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

include hψ₀ in

private theorem pred_of_mem {f : AdelicGL2 (𝓞 ℚ) ℚ → ℂ}
    (hf : f ∈ isotypicCuspSubmodule ℚ (WeightPiece.windowPins c u d₁ d₂ T) ξ Φ.level S Φ) :
    IsIsotypicCuspFormAt ℚ (WeightPiece.windowPins c u d₁ d₂ T) ξ Φ.level S Φ f :=
  PredicateClosure.isIsotypicCuspFormAt_of_mem_isotypicCuspSubmodule hψ₀ hf

private theorem lsXi_of_pred {f : AdelicGL2 (𝓞 ℚ) ℚ → ℂ}
    (hf : IsIsotypicCuspFormAt ℚ (WeightPiece.windowPins c u d₁ d₂ T) ξ Φ.level S Φ f) :
    IsLsXiFunction (𝓞 ℚ) ℚ ⊤ ξ f ∧
      MemLp f 2 ((adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ).restrict (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂)) :=
  (@lsXiMemberAt_iff (𝓞 ℚ) ℚ _ _ _ _ _ (glBorel (Fin 2) (𝓞 ℚ) ℚ) (adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ) ⊤ ξ
    (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂) f).mp hf.smoothCusp.1.1

include hin hV hψ₀ in

private theorem deriv_data (hd : d₁ < d₂)
    (hcov : CoversModCentre ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂)) {k : ℤ}
    {f : AdelicGL2 (𝓞 ℚ) ℚ → ℂ} (hf : f ∈ piece hw ξ S Φ V k) (dd : ArchDir) :
    IsLsXiFunction (𝓞 ℚ) ℚ ⊤ ξ (archDerivAt hw dd f) ∧ Continuous (archDerivAt hw dd f) := by
  obtain ⟨β, hβ, hβs, -, hrepro⟩ := exists_reproducing hin hV hd hcov hf
  have hfiso := (mem_piece_iff.1 hf).2.1
  have hfc : Continuous f := continuous_of_mem_isotypicCuspSubmodule hfiso
  have hD : archDerivAt hw dd f = rightConv ℚ f (TestCalculus.leftDeriv hw dd β) := by
    conv_lhs => rw [← hrepro]
    exact CalculusAtPins.archDerivAt_rightConv hw hfc dd β hβ
  have hiso : archDerivAt hw dd f ∈ isotypicCuspSubmodule ℚ (WeightPiece.windowPins c u d₁ d₂ T) ξ Φ.level S Φ := by
    rw [hD]
    exact CalculusAtPins.rightConv_mem_isotypicCuspSubmodule_of_mem ξ S Φ hin.conv_isotypic hfiso _
      (TestCalculus.isFactorizableTestFn_leftDeriv (CalculusAtPins.leftDerivTensor hw) dd hβ)
      (TestCalculus.exists_eq_mul_of_leftDeriv_ne_zero hw (levelOne (𝓞 ℚ) ℚ Φ.level ⊓ finiteAdelicGL2Subgroup ℚ) dd
        hβs)
  exact ⟨(lsXi_of_pred (pred_of_mem hψ₀ hiso)).1, continuous_of_mem_isotypicCuspSubmodule hiso⟩

private theorem exists_slab (g₀ g₁ : AdelicGL2 (𝓞 ℚ) ℚ) :
    ∃ (α β : ℝ) (Φ₀ : Set (AdelicGL2 (𝓞 ℚ) ℚ)), 0 < α ∧
      α < ideleNorm ℚ (Matrix.GeneralLinearGroup.det g₀) ∧ ideleNorm ℚ (Matrix.GeneralLinearGroup.det g₀) < β ∧
      α < ideleNorm ℚ (Matrix.GeneralLinearGroup.det g₁) ∧ ideleNorm ℚ (Matrix.GeneralLinearGroup.det g₁) < β ∧
      Φ₀ ⊆ {g | ideleNorm ℚ (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β} ∧
      IsFundamentalDomain (globalPoints (𝓞 ℚ) ℚ).range Φ₀
        ((adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ).restrict
          {g | ideleNorm ℚ (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}) := by
  have h₀ : 0 < ideleNorm ℚ (Matrix.GeneralLinearGroup.det g₀) := ideleNorm_pos _
  have h₁ : 0 < ideleNorm ℚ (Matrix.GeneralLinearGroup.det g₁) := ideleNorm_pos _
  generalize ideleNorm ℚ (Matrix.GeneralLinearGroup.det g₀) = n₀ at h₀ ⊢
  generalize ideleNorm ℚ (Matrix.GeneralLinearGroup.det g₁) = n₁ at h₁ ⊢
  have hmin := lt_min h₀ h₁
  obtain ⟨Φ₀, hΦ₀, hFD⟩ :=
    exists_isFundamentalDomain_globalPoints_range_restrict_ideleNorm_det_Icc ℚ (min n₀ n₁ / 2) (2 * max n₀ n₁)
  refine ⟨_, _, Φ₀, half_pos hmin, ?_, ?_, ?_, ?_, hΦ₀, hFD⟩
  · linarith [min_le_left n₀ n₁]
  · linarith [le_max_left n₀ n₁]
  · linarith [min_le_right n₀ n₁]
  · linarith [le_max_right n₀ n₁]

include hin hV hψ₀ in

private theorem exists_pos_of_ladder (hd : d₁ < d₂)
    (hcov : CoversModCentre ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂)) {σ : ℝ}
    (hσ : ∀ z : (⊤ : Subgroup (AdeleRing (𝓞 ℚ) ℚ)ˣ),
      ‖((ξ z : ℂˣ) : ℂ)‖ = ideleNorm ℚ (z : (AdeleRing (𝓞 ℚ) ℚ)ˣ) ^ σ)
    {k kb : ℤ} {φ b a : AdelicGL2 (𝓞 ℚ) ℚ → ℂ} (hφ : φ ∈ piece hw ξ S Φ V k) (hφ0 : φ ≠ 0)
    (hb : b ∈ piece hw ξ S Φ V kb) (hb0 : b ≠ 0) {lam cc : ℂ} (heig : archCasimirAt hw φ = lam • φ)
    (hlad : archCasimirAt hw φ = (-(1 / 4 : ℂ)) • a + cc • φ)
    (ha₂ : ∀ Φ₀ : Set (AdelicGL2 (𝓞 ℚ) ℚ),
      (∀ dd : ArchDir, MemLp (archDerivAt hw dd b) 2 ((adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ).restrict Φ₀)) →
        MemLp a 2 ((adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ).restrict Φ₀))
    (hor : ∀ {α β : ℝ} {Φ₀ : Set (AdelicGL2 (𝓞 ℚ) ℚ)}, SkewAdjoint.SlabData σ α β Φ₀ →
      MemLp φ 2 ((adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ).restrict Φ₀) → MemLp b 2 ((adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ).restrict Φ₀) →
      (∀ dd : ArchDir, MemLp (archDerivAt hw dd b) 2 ((adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ).restrict Φ₀)) →
      (∀ dd : ArchDir, MemLp (archDerivAt hw dd φ) 2 ((adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ).restrict Φ₀)) →
      (∀ dd : ArchDir,
        SkewAdjoint.pair σ Φ₀ (archDerivAt hw dd b) φ = -SkewAdjoint.pair σ Φ₀ b (archDerivAt hw dd φ)) →
      SkewAdjoint.pair σ Φ₀ a φ = -SkewAdjoint.pair σ Φ₀ b b) :
    ∃ t : ℝ, 0 < t ∧ lam = cc + t := by
  obtain ⟨βφ, hβφ, -, -, hreproφ⟩ := exists_reproducing hin hV hd hcov hφ
  obtain ⟨βb, hβb, -, -, hreprob⟩ := exists_reproducing hin hV hd hcov hb
  have hφiso := (mem_piece_iff.1 hφ).2.1
  have hbiso := (mem_piece_iff.1 hb).2.1
  obtain ⟨hφL, hφwin⟩ := lsXi_of_pred (pred_of_mem hψ₀ hφiso)
  obtain ⟨hbL, hbwin⟩ := lsXi_of_pred (pred_of_mem hψ₀ hbiso)
  have hφc : Continuous φ := continuous_of_mem_isotypicCuspSubmodule hφiso
  have hbc : Continuous b := continuous_of_mem_isotypicCuspSubmodule hbiso
  obtain ⟨g₀, hg₀⟩ := Function.ne_iff.mp hφ0
  obtain ⟨g₁, hg₁⟩ := Function.ne_iff.mp hb0
  obtain ⟨α, β, Φ₀, hα, h₀α, h₀β, h₁α, h₁β, hΦ₀, hFD⟩ := exists_slab g₀ g₁
  have hnm : NullMeasurableSet Φ₀ (adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ) :=
    (nullMeasurableSet_restrict_of_subset hΦ₀).1 hFD.nullMeasurableSet
  have hS : SlabPairing.SlabData σ α β Φ₀ := ⟨hα, hΦ₀, hnm, NumberField.TateGlobal.continuous_ideleNorm_det ℚ⟩
  have hS' : SkewAdjoint.SlabData σ α β Φ₀ := ⟨hα, hΦ₀, hnm, NumberField.TateGlobal.continuous_ideleNorm_det ℚ⟩
  have hφ₂ : MemLp φ 2 ((adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ).restrict Φ₀) :=
    SlabGeometry.memLp_fd ℚ c u d₁ d₂ T hd hcov ξ φ hφL hφc hφwin α β hα Φ₀ hΦ₀ hFD
  have hb₂ : MemLp b 2 ((adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ).restrict Φ₀) :=
    SlabGeometry.memLp_fd ℚ c u d₁ d₂ T hd hcov ξ b hbL hbc hbwin α β hα Φ₀ hΦ₀ hFD
  have hφmass : 0 < ∫⁻ x in Φ₀, ‖φ x‖ₑ ^ 2 ∂(adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ) :=
    SlabGeometry.lintegral_fd_pos ℚ ξ φ hφL hφc g₀ hg₀ α β h₀α h₀β Φ₀ hFD
  have hbmass : 0 < ∫⁻ x in Φ₀, ‖b x‖ₑ ^ 2 ∂(adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ) :=
    SlabGeometry.lintegral_fd_pos ℚ ξ b hbL hbc g₁ hg₁ α β h₁α h₁β Φ₀ hFD
  have hc : ∀ (dd : ArchDir) (γ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ), IsFactorizableTestFn ℚ γ →
      IsFactorizableTestFn ℚ (SkewAdjoint.leftDeriv hw dd γ) :=
    fun dd γ hγ => TestCalculus.isFactorizableTestFn_leftDeriv (CalculusAtPins.leftDerivTensor hw) dd hγ
  have hDφ₂ : ∀ dd : ArchDir, MemLp (archDerivAt hw dd φ) 2 ((adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ).restrict Φ₀) := fun dd =>
    SkewAdjoint.memLp_archDerivAt_of_repro hS' hFD ξ hσ dd hφL hφc hφ₂ (CalculusAtPins.archDerivAt_rightConv' hw hφc)
      hc hβφ hreproφ
  have hDb₂ : ∀ dd : ArchDir, MemLp (archDerivAt hw dd b) 2 ((adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ).restrict Φ₀) := fun dd =>
    SkewAdjoint.memLp_archDerivAt_of_repro hS' hFD ξ hσ dd hbL hbc hb₂ (CalculusAtPins.archDerivAt_rightConv' hw hbc)
      hc hβb hreprob
  have hskew : ∀ dd : ArchDir,
      SkewAdjoint.pair σ Φ₀ (archDerivAt hw dd b) φ = -SkewAdjoint.pair σ Φ₀ b (archDerivAt hw dd φ) := fun dd =>
    SkewAdjoint.pair_archDerivAt_left hS' hFD ξ hσ dd hφL hφc hφ₂ hbL hbc hb₂ (deriv_data hin hV hψ₀ hd hcov hφ dd).1
      (deriv_data hin hV hψ₀ hd hcov hφ dd).2 hβφ hreproφ hβb hreprob (CalculusAtPins.archDerivAt_rightConv' hw hφc)
      (CalculusAtPins.archDerivAt_rightConv' hw hbc) hc (CalculusAtPins.leftDeriv_inv hw)
      (CalculusAtPins.isArchSmoothAt_comp_inv hw)
      (CalculusAtPins.rightConv_archDerivAt_mul hw hφc (isArchSmoothAt_of_mem_piece hin hV hd hcov hφ)
        fun dd => (deriv_data hin hV hψ₀ hd hcov hφ dd).2)
  have hadj : SkewAdjoint.pair σ Φ₀ a φ = -SkewAdjoint.pair σ Φ₀ b b := hor hS' hφ₂ hb₂ hDb₂ hDφ₂ hskew
  obtain ⟨t, ht0, hlam, hdiag⟩ :=
    SlabPairing.eigenvalue_eq_const_add hS hφ₂ (ha₂ Φ₀ hDb₂) hφmass lam cc heig hlad hadj
  refine ⟨t, ?_, hlam⟩
  rcases ht0.lt_or_eq with h | h
  · exact h
  · exact absurd (hdiag h.symm) (SlabPairing.diag_pos hS hb₂ hbmass).ne'

private theorem pair_lowerOp_eq_neg_pair_raiseOp {σ α β : ℝ} {Φ₀ : Set (AdelicGL2 (𝓞 ℚ) ℚ)}
    (hS : SkewAdjoint.SlabData σ α β Φ₀) {φ b : AdelicGL2 (𝓞 ℚ) ℚ → ℂ}
    (hφ₂ : MemLp φ 2 ((adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ).restrict Φ₀))
    (hb₂ : MemLp b 2 ((adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ).restrict Φ₀))
    (hDb₂ : ∀ dd : ArchDir, MemLp (archDerivAt hw dd b) 2 ((adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ).restrict Φ₀))
    (hDφ₂ : ∀ dd : ArchDir, MemLp (archDerivAt hw dd φ) 2 ((adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ).restrict Φ₀))
    (hskew : ∀ dd : ArchDir,
      SkewAdjoint.pair σ Φ₀ (archDerivAt hw dd b) φ = -SkewAdjoint.pair σ Φ₀ b (archDerivAt hw dd φ)) :
    SkewAdjoint.pair σ Φ₀ (SkewAdjoint.lowerOp hw b) φ = -SkewAdjoint.pair σ Φ₀ b (SkewAdjoint.raiseOp hw φ) := by
  have hb' : SkewAdjoint.lowerOp hw b
      = archDerivAt hw .H b + (-Complex.I) • (archDerivAt hw .E b + archDerivAt hw .Fm b) := by
    simp only [SkewAdjoint.lowerOp, sub_eq_add_neg, neg_smul]
  rw [hb', SkewAdjoint.pair_add_left hS (hDb₂ .H) (((hDb₂ .E).add (hDb₂ .Fm)).const_smul (-Complex.I)) hφ₂,
    SkewAdjoint.pair_smul_left, SkewAdjoint.pair_add_left hS (hDb₂ .E) (hDb₂ .Fm) hφ₂, hskew .H, hskew .E, hskew .Fm]
  unfold SkewAdjoint.raiseOp
  rw [SkewAdjoint.pair_add_right hS hb₂ (hDφ₂ .H) (((hDφ₂ .E).add (hDφ₂ .Fm)).const_smul Complex.I),
    SkewAdjoint.pair_smul_right, SkewAdjoint.pair_add_right hS hb₂ (hDφ₂ .E) (hDφ₂ .Fm), Complex.conj_I]
  ring

end

section

variable {c u d₁ d₂ : ℝ} {T : Finset (AdelicGL2 (𝓞 ℚ) ℚ)} {Φ : HeckeEigensystem ℚ ℂ} {w : InfinitePlace ℚ}
  {hw : w.IsReal} (hin : Inputs c u d₁ d₂ T Φ hw)
  {ξ : (WeightPiece.windowPins c u d₁ d₂ T).Z →* ℂˣ} {S : Finset (HeightOneSpectrum (𝓞 ℚ))}
  {V : Submodule ℂ (AdelicGL2 (𝓞 ℚ) ℚ → ℂ)} (hV : IsCuspConstituent ℚ (WeightPiece.windowPins c u d₁ d₂ T) ξ V)
  {ψ₀ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ} (hψ₀ : IsIsotypicCuspFormAt ℚ (WeightPiece.windowPins c u d₁ d₂ T) ξ Φ.level S Φ ψ₀)
  {σ : ℝ}
  (hσ : ∀ z : (⊤ : Subgroup (AdeleRing (𝓞 ℚ) ℚ)ˣ), ‖((ξ z : ℂˣ) : ℂ)‖ = ideleNorm ℚ (z : (AdeleRing (𝓞 ℚ) ℚ)ˣ) ^ σ)

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

include hψ₀ in

private theorem not_invariant {k : ℤ} {φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ} (hφ : φ ∈ piece hw ξ S Φ V k) (hφ0 : φ ≠ 0)
    (harch : ∀ m : GL (Fin 2) ℝ, (m : Matrix (Fin 2) (Fin 2) ℝ).det = 1 → ∀ x : AdelicGL2 (𝓞 ℚ) ℚ,
      φ (x * archRealGLAt hw m) = φ x) : False := by
  have hpred := pred_of_mem hψ₀ (mem_piece_iff.1 hφ).2.1
  have hL := (lsXi_of_pred hpred).1
  apply hφ0
  funext g
  exact AdelicExclusion.eq_zero_of_isCuspidalFn hw φ hL.left_invariant Φ.level Φ.level_ne_bot
    (fun x uu huu => hpred.level_invariant x uu huu) harch hpred.smoothCusp.1.2 g

include hin hV hψ₀ hσ in

private theorem lowerOp_ne_zero_of_weight_zero (hd : d₁ < d₂)
    (hcov : CoversModCentre ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂))
    {φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ} (hφ : φ ∈ piece hw ξ S Φ V 0) (hφ0 : φ ≠ 0) {lam : ℂ}
    (heig : archCasimirAt hw φ = lam • φ) : TestCalculus.lowerOp hw φ ≠ 0 := by
  intro hlow
  have hsm : IsArchSmoothAt hw φ := isArchSmoothAt_of_mem_piece hin hV hd hcov hφ
  have hk : HasArchCharacterAt₀ ℚ w (archWeightCharAt hw 0) φ := (mem_piece_iff.1 hφ).2.2
  have hlam : lam = (1 - (((0 : ℤ) : ℂ) - 1) ^ 2) / 4 := by
    have h1 := Ladder.archCasimirAt_eq_of_lowerOp_eq_zero 0 hsm hk hlow
    rw [heig] at h1
    exact smul_left_injective ℂ hφ0 h1
  have hraise : TestCalculus.raiseOp hw φ = 0 := by
    by_contra hne
    obtain ⟨t, ht, hlamt⟩ := exists_pos_of_ladder hin hV hψ₀ hd hcov hσ hφ hφ0
      (raiseOp_mem_piece hin hV hd hcov hφ) hne heig (Ladder.archCasimirAt_eq_lowerOp_raiseOp 0 hsm hk)
      (fun Φ₀ h => (h .H).sub (((h .E).add (h .Fm)).const_smul Complex.I))
      (fun hS hφ₂ hb₂ hDb₂ hDφ₂ hskew => pair_lowerOp_eq_neg_pair_raiseOp hS hφ₂ hb₂ hDb₂ hDφ₂ hskew)
    rw [hlam] at hlamt
    norm_num at hlamt
    exact ht.ne' (by first | exact hlamt | exact hlamt.symm | exact_mod_cast hlamt | exact_mod_cast hlamt.symm)
  have h0 : WeightShift.HasRealWeight hw 0 φ := WeightShift.hasRealWeight_of_hasArchCharacterAt₀ hw 0 hk
  exact not_invariant hψ₀ hφ hφ0 fun m hm x =>
    ArchExclusion.apply_mul_archRealGLAt_of_det_one hsm h0 hlow hraise m hm x

include hin hV hψ₀ hσ in

private theorem exists_t_of_low_weight (hd : d₁ < d₂)
    (hcov : CoversModCentre ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂)) {k₀ : ℤ}
    {φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ} (hφ : φ ∈ piece hw ξ S Φ V k₀) (hφ0 : φ ≠ 0) {lam : ℂ}
    (heig : archCasimirAt hw φ = lam • φ) :
    ∃ t : ℝ, 0 ≤ t ∧ lam = (1 - ((k₀ : ℂ) - 1) ^ 2) / 4 + t ∧ (k₀ = 0 → 0 < t) ∧
      (t = 0 → TestCalculus.lowerOp hw φ = 0) := by
  have hsm : IsArchSmoothAt hw φ := isArchSmoothAt_of_mem_piece hin hV hd hcov hφ
  have hk : HasArchCharacterAt₀ ℚ w (archWeightCharAt hw k₀) φ := (mem_piece_iff.1 hφ).2.2
  by_cases hlow : TestCalculus.lowerOp hw φ = 0
  · refine ⟨0, le_rfl, ?_, fun h0 => ?_, fun _ => hlow⟩
    · have h1 := Ladder.archCasimirAt_eq_of_lowerOp_eq_zero k₀ hsm hk hlow
      rw [heig] at h1
      rw [smul_left_injective ℂ hφ0 h1]
      simp
    · subst h0
      exact absurd hlow (lowerOp_ne_zero_of_weight_zero hin hV hψ₀ hσ hd hcov hφ hφ0 heig)
  · obtain ⟨t, ht, hlamt⟩ := exists_pos_of_ladder hin hV hψ₀ hd hcov hσ hφ hφ0
      (lowerOp_mem_piece hin hV hd hcov hφ) hlow heig (Ladder.archCasimirAt_eq_raiseOp_lowerOp k₀ hsm hk)
      (fun Φ₀ h => (h .H).add (((h .E).add (h .Fm)).const_smul Complex.I))
      (fun hS hφ₂ hb₂ hDb₂ hDφ₂ hskew => SkewAdjoint.pair_raiseOp_eq_neg_pair_lowerOp hS hφ₂ hb₂ hDb₂ hDφ₂ hskew)
    exact ⟨t, ht.le, hlamt, fun _ => ht, fun h0 => absurd h0 ht.ne'⟩

end

section

variable {c u d₁ d₂ : ℝ} {T : Finset (AdelicGL2 (𝓞 ℚ) ℚ)} {Φ : HeckeEigensystem ℚ ℂ}

private structure ParamData {w : InfinitePlace ℚ} (hw : w.IsReal)
    (R : SmoothCuspRealizationAt ℚ (WeightPiece.windowPins c u d₁ d₂ T) Φ.toRawCentral)
    (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (P : RealArchParam) (k₀ : ℤ) (φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ) : Prop where
  iso : IsIsotypicCuspFormAt ℚ (WeightPiece.windowPins c u d₁ d₂ T) R.centralChar Φ.level S Φ φ
  ne_zero : φ ≠ 0
  repro : ∃ α : AdelicGL2 (𝓞 ℚ) ℚ → ℂ, IsFactorizableTestFn ℚ α ∧ rightConv ℚ φ α = φ
  weight : HasArchCharacterAt₀ ℚ w (archWeightCharAt hw k₀) φ
  principal_bound : ∀ (u₁ u₂ : ℂ) (a₁ a₂ : ZMod 2), P = RealArchParam.principal u₁ a₁ u₂ a₂ → |(u₁ - u₂).re| < 1
  central : IsArchCompAt ℚ (R.centralChar.comp Subgroup.topEquiv.symm.toMonoidHom) w (P.centralExponent + 1)
    (P.centralSign.val : ℤ)
  principal_weight : ∀ (u₁ u₂ : ℂ) (a₁ a₂ : ZMod 2), P = RealArchParam.principal u₁ a₁ u₂ a₂ →
    (k₀ = 0 ∨ k₀ = 1) ∧ ((k₀ : ZMod 2) = a₁ + a₂)
  discrete_weight : ∀ (u₀ : ℂ) (n : ℕ) (hn : 1 ≤ n), P = RealArchParam.discrete u₀ n hn → k₀ = (n : ℤ) + 1
  smooth : IsArchSmoothAt hw φ
  eigen : archCasimirAt hw φ = P.laplaceEigenvalue • φ
  reflect : ∀ (u₁ u₂ : ℂ) (a₁ : ZMod 2), P = RealArchParam.principal u₁ a₁ u₂ a₁ →
    ∀ g : AdelicGL2 (𝓞 ℚ) ℚ, φ (g * archRealGLAt hw UpperHalfPlane.J) = (-1 : ℂ) ^ a₁.val * φ g
  lower_discrete : ∀ (u₀ : ℂ) (n : ℕ) (hn : 1 ≤ n), P = RealArchParam.discrete u₀ n hn →
    TestCalculus.lowerOp hw φ = 0
  lower_principal : ∀ (u₀ : ℂ) (a₁ a₂ : ZMod 2), P = RealArchParam.principal u₀ a₁ u₀ a₂ → a₁ ≠ a₂ →
    TestCalculus.lowerOp hw φ = 0

private theorem zmod_two_add_self : ∀ a : ZMod 2, a + a = 0 := by decide

variable {w : InfinitePlace ℚ} {hw : w.IsReal} (hin : Inputs c u d₁ d₂ T Φ hw)
  {R : SmoothCuspRealizationAt ℚ (WeightPiece.windowPins c u d₁ d₂ T) Φ.toRawCentral}
  {S : Finset (HeightOneSpectrum (𝓞 ℚ))} {V : Submodule ℂ (AdelicGL2 (𝓞 ℚ) ℚ → ℂ)}
  (hV : IsCuspConstituent ℚ (WeightPiece.windowPins c u d₁ d₂ T) R.centralChar V)
  {ψ₀ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ}
  (hψ₀ : IsIsotypicCuspFormAt ℚ (WeightPiece.windowPins c u d₁ d₂ T) R.centralChar Φ.level S Φ ψ₀)
  {σ : ℝ}
  (hσ : ∀ z : (⊤ : Subgroup (AdeleRing (𝓞 ℚ) ℚ)ˣ),
    ‖((R.centralChar z : ℂˣ) : ℂ)‖ = ideleNorm ℚ (z : (AdeleRing (𝓞 ℚ) ℚ)ˣ) ^ σ)
  {u₀ : ℂ} {a : ZMod 2}
  (hcomp : IsArchCompAt ℚ (R.centralChar.comp Subgroup.topEquiv.symm.toMonoidHom) w u₀ ((a.val : ℕ) : ℤ))

include hin hV hψ₀ hcomp in

private theorem common_data (hd : d₁ < d₂)
    (hcov : CoversModCentre ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂)) {k₀ : ℤ}
    {φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ} (hφ : φ ∈ piece hw R.centralChar S Φ V k₀) (hφ0 : φ ≠ 0) :
    IsIsotypicCuspFormAt ℚ (WeightPiece.windowPins c u d₁ d₂ T) R.centralChar Φ.level S Φ φ ∧
      (∃ α : AdelicGL2 (𝓞 ℚ) ℚ → ℂ, IsFactorizableTestFn ℚ α ∧ rightConv ℚ φ α = φ) ∧
      HasArchCharacterAt₀ ℚ w (archWeightCharAt hw k₀) φ ∧ IsArchSmoothAt hw φ ∧ ((k₀ : ZMod 2) = a) := by
  obtain ⟨-, hiso, hk⟩ := mem_piece_iff.1 hφ
  obtain ⟨β, hβ, -, -, hrepro⟩ := exists_reproducing hin hV hd hcov hφ
  obtain ⟨g₀, hg₀⟩ := Function.ne_iff.mp hφ0
  have hpred := pred_of_mem hψ₀ hiso
  refine ⟨hpred, ⟨β, hβ, hrepro⟩, hk, isArchSmoothAt_of_mem_piece hin hV hd hcov hφ, ?_⟩
  exact CentralParity.centralSign_eq_weight R.centralChar (lsXi_of_pred hpred).1 hw k₀ hk hg₀ u₀ a hcomp

include hin hV hψ₀ hcomp in

private theorem paramData_of_discrete (hd : d₁ < d₂)
    (hcov : CoversModCentre ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂)) {k₀ : ℤ} (hk₀ : 2 ≤ k₀)
    (hmin : piece hw R.centralChar S Φ V (k₀ - 2) = ⊥) {φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ}
    (hφ : φ ∈ piece hw R.centralChar S Φ V k₀) (hφ0 : φ ≠ 0) {lam : ℂ} (heig : archCasimirAt hw φ = lam • φ) :
    ∃ P : RealArchParam, ParamData hw R S P k₀ φ := by
  obtain ⟨hiso, hrepro, hk, hsm, hpar⟩ := common_data hin hV hψ₀ hcomp hd hcov hφ hφ0
  have hlow : TestCalculus.lowerOp hw φ = 0 :=
    (Submodule.eq_bot_iff _).1 hmin _ (lowerOp_mem_piece hin hV hd hcov hφ)
  have hlam : lam = (1 - ((k₀ : ℂ) - 1) ^ 2) / 4 := by
    have h1 := Ladder.archCasimirAt_eq_of_lowerOp_eq_zero k₀ hsm hk hlow
    rw [heig] at h1
    exact smul_left_injective ℂ hφ0 h1
  obtain ⟨P, hnp, hP, hexp, hsign, hdw⟩ := ArchParameter.exists_specD hk₀ hlam u₀ hpar
  refine ⟨P, hiso, hφ0, hrepro, hk, fun u₁ u₂ a₁ a₂ h => absurd h (hnp u₁ u₂ a₁ a₂), ?_,
    fun u₁ u₂ a₁ a₂ h => absurd h (hnp u₁ u₂ a₁ a₂), hdw, hsm, by rw [hP, heig],
    fun u₁ u₂ a₁ h => absurd h (hnp u₁ u₂ a₁ a₁), fun _ _ _ _ => hlow, fun u a₁ a₂ h _ => absurd h (hnp u u a₁ a₂)⟩
  rw [hexp, hsign]
  exact hcomp

include hin hV hψ₀ hσ hcomp in

private theorem paramData_of_low (hd : d₁ < d₂)
    (hcov : CoversModCentre ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂)) {k₀ : ℤ}
    (hk₀ : k₀ = 0 ∨ k₀ = 1) {φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ} (hφ : φ ∈ piece hw R.centralChar S Φ V k₀) (hφ0 : φ ≠ 0)
    {lam : ℂ} (heig : archCasimirAt hw φ = lam • φ) (j : ZMod 2)
    (hJ : k₀ = 0 → ∀ g : AdelicGL2 (𝓞 ℚ) ℚ, φ (g * archRealGLAt hw UpperHalfPlane.J) = (-1 : ℂ) ^ j.val * φ g) :
    ∃ P : RealArchParam, ParamData hw R S P k₀ φ := by
  obtain ⟨hiso, hrepro, hk, hsm, hpar⟩ := common_data hin hV hψ₀ hcomp hd hcov hφ hφ0
  obtain ⟨t, ht, hlam, ht0, hlow⟩ := exists_t_of_low_weight hin hV hψ₀ hσ hd hcov hφ hφ0 heig
  obtain ⟨P, hnd, hP, hexp, hsign, hbound, hpw, hj, hzero⟩ := ArchParameter.exists_spec hk₀ ht hlam ht0 u₀ hpar j
  refine ⟨P, hiso, hφ0, hrepro, hk, hbound, ?_, hpw, fun u n hn h => absurd h (hnd u n hn), hsm, by rw [hP, heig],
    ?_, fun u n hn h => absurd h (hnd u n hn), fun u a₁ a₂ h hne => hlow (hzero u a₁ a₂ h hne)⟩
  · rw [hexp, hsign]
    exact hcomp
  · intro u₁ u₂ a₁ h
    have haj := hj u₁ u₂ a₁ h
    obtain ⟨-, hpar2⟩ := hpw u₁ u₂ a₁ a₁ h
    rw [zmod_two_add_self] at hpar2
    rcases hk₀ with hk0 | hk1
    · rw [haj]
      exact hJ hk0
    · rw [hk1] at hpar2
      exact absurd hpar2 (by decide)

end

private theorem eigenvector_of_realization
    (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 ℚ) ℚ))
    (_hd : d₁ < d₂)
    (_hcov : CoversModCentre ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂))
    (Φ : HeckeEigensystem ℚ ℂ)
    (R : SmoothCuspRealizationAt ℚ
      (productionPinsOf ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂)
        (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v)
        (adelicBox ℚ))
      Φ.toRawCentral)
    (_hR : Continuous R.toFun)
    (hI : ∀
    (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 ℚ) ℚ))
    (_hd : d₁ < d₂)
    (_hcov : CoversModCentre ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂))
    (Φ : HeckeEigensystem ℚ ℂ)
    (R : SmoothCuspRealizationAt ℚ
      (productionPinsOf ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂)
        (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v)
        (adelicBox ℚ))
      Φ.toRawCentral)
    (_hR : Continuous R.toFun) (f : AdelicGL2 (𝓞 ℚ) ℚ → ℂ) (_hf : IsFactorizableTestFn ℚ f)
    (_hfs : ∀ x : AdelicGL2 (𝓞 ℚ) ℚ, f x ≠ 0 → ∃ a k : AdelicGL2 (𝓞 ℚ) ℚ,
      glFin (𝓞 ℚ) ℚ a = 1 ∧ k ∈ levelOne (𝓞 ℚ) ℚ Φ.level ⊓ finiteAdelicGL2Subgroup ℚ ∧ x = a * k),
    IsIsotypicCuspFormAt ℚ
      (productionPinsOf ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂)
        (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v)
        (adelicBox ℚ))
      R.centralChar Φ.level R.exceptionalSet Φ (rightConv ℚ R.toFun f))
    (hL4 : ∀
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (NK : Ideal (𝓞 K)) (SK : Finset (HeightOneSpectrum (𝓞 K)))
    (_hNS : ∀ p : HeightOneSpectrum (𝓞 K), p.asIdeal ∣ NK → p ∈ SK)
    (tys : ArchTypeFamily L) (f : AdelicGL2 (𝓞 L) L → ℂ) (_hf : Continuous f)
    (_hlev : ∀ g : AdelicGL2 (𝓞 L) L,
      ∀ k ∈ levelOne (𝓞 L) L (Ideal.map (algebraMap (𝓞 K) (𝓞 L)) NK) ⊓ finiteAdelicGL2Subgroup L,
        f (g * k) = f g)
    (_harch : f ∈ archCutSubmodule L tys),
    ∃ (ff : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L) → ℂ) (fa : ℕ → (GL (Fin 2) (InfiniteAdeleRing L) → ℂ)),
      IsFinTestFactor L ff ∧
      (∀ x : AdelicGL2 (𝓞 L) L, ff (glFin (𝓞 L) L x) ≠ 0 → ∃ a k : AdelicGL2 (𝓞 L) L,
        glFin (𝓞 L) L a = 1 ∧
        k ∈ levelOne (𝓞 L) L (Ideal.map (algebraMap (𝓞 K) (𝓞 L)) NK) ⊓ finiteAdelicGL2Subgroup L ∧ x = a * k) ∧
      (∀ n, IsArchTestFactor L (fa n)) ∧
      (∀ n, IsUnitFactorizableAboveOfType K L tys
        (levelOne (𝓞 L) L (Ideal.map (algebraMap (𝓞 K) (𝓞 L)) NK) ⊓ finiteAdelicGL2Subgroup L) SK
        (fun g => fa n (glArch (𝓞 L) L g) * ff (glFin (𝓞 L) L g))) ∧
      ∀ g, Filter.Tendsto
        (fun n => rightConv L f (fun x => fa n (glArch (𝓞 L) L x) * ff (glFin (𝓞 L) L x)) g)
        Filter.atTop (nhds (f g)))
    (hAd : ∀
    {K : Type} [Field K] [NumberField K] {w : InfinitePlace K} (hw : w.IsReal) (φ : AdelicGL2 (𝓞 K) K → ℂ)
    (_hφ : IsArchSmoothAt hw φ) (k : GL (Fin 2) ℝ),
    archCasimirAt hw (fun x => φ (x * archRealGLAt hw k)) = fun x => archCasimirAt hw φ (x * archRealGLAt hw k)) :
    ∃ (S : Finset (HeightOneSpectrum (𝓞 ℚ)))
      (archR : ∀ w : InfinitePlace ℚ, w.IsReal → RealArchParam),
      R.exceptionalSet ⊆ S ∧
      (∀ (w : InfinitePlace ℚ) (hw : w.IsReal) (u₁ u₂ : ℂ) (a₁ a₂ : ZMod 2),
        archR w hw = RealArchParam.principal u₁ a₁ u₂ a₂ → |(u₁ - u₂).re| < 1) ∧
      (∀ (w : InfinitePlace ℚ) (hw : w.IsReal),
        IsArchCompAt ℚ (R.centralChar.comp Subgroup.topEquiv.symm.toMonoidHom) w
          ((archR w hw).centralExponent + 1) ((archR w hw).centralSign.val : ℤ)) ∧
      ∃ (φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ) (k : InfinitePlace ℚ → ℤ),
        IsIsotypicCuspFormAt ℚ
            (productionPinsOf ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂)
              (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ)
              (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ))
            R.centralChar Φ.level S Φ φ ∧
        φ ≠ 0 ∧
        (∃ α : AdelicGL2 (𝓞 ℚ) ℚ → ℂ, IsFactorizableTestFn ℚ α ∧ rightConv ℚ φ α = φ) ∧
        (∀ (w : InfinitePlace ℚ) (hw : w.IsReal),
          HasArchCharacterAt₀ ℚ w (archWeightCharAt hw (k w)) φ) ∧
        (∀ (w : InfinitePlace ℚ) (hw : w.IsReal) (u₁ u₂ : ℂ) (a₁ a₂ : ZMod 2),
          archR w hw = RealArchParam.principal u₁ a₁ u₂ a₂ →
            (k w = 0 ∨ k w = 1) ∧ ((k w : ZMod 2) = a₁ + a₂)) ∧
        (∀ (w : InfinitePlace ℚ) (hw : w.IsReal) (u₀ : ℂ) (n : ℕ) (hn : 1 ≤ n),
          archR w hw = RealArchParam.discrete u₀ n hn → k w = (n : ℤ) + 1) ∧
        (∀ (w : InfinitePlace ℚ) (hw : w.IsReal),
          IsArchSmoothAt hw φ ∧ archCasimirAt hw φ = (archR w hw).laplaceEigenvalue • φ) ∧
        (∀ (w : InfinitePlace ℚ) (hw : w.IsReal) (u₁ u₂ : ℂ) (a₁ : ZMod 2),
          archR w hw = RealArchParam.principal u₁ a₁ u₂ a₁ →
            ∀ g : AdelicGL2 (𝓞 ℚ) ℚ, φ (g * archRealGLAt hw UpperHalfPlane.J) = (-1 : ℂ) ^ a₁.val * φ g) ∧
        (∀ (w : InfinitePlace ℚ) (hw : w.IsReal) (u₀ : ℂ) (n : ℕ) (hn : 1 ≤ n),
          archR w hw = RealArchParam.discrete u₀ n hn →
            archDerivAt hw ArchDir.H φ
                - Complex.I • (archDerivAt hw ArchDir.E φ + archDerivAt hw ArchDir.Fm φ) = 0) ∧
        (∀ (w : InfinitePlace ℚ) (hw : w.IsReal) (u₀ : ℂ) (a₁ a₂ : ZMod 2),
          archR w hw = RealArchParam.principal u₀ a₁ u₀ a₂ → a₁ ≠ a₂ →
            archDerivAt hw ArchDir.H φ
                - Complex.I • (archDerivAt hw ArchDir.E φ + archDerivAt hw ArchDir.Fm φ) = 0) := by
  have hw₀ : (default : InfinitePlace ℚ).IsReal := isReal_infinitePlace_rat default
  have hin : Inputs c u d₁ d₂ T Φ hw₀ :=
    { conv_isotypic := fun R' hR' t ht hts => hI c u d₁ d₂ T _hd _hcov Φ R' hR' t ht hts
      casimir_translate := fun φ hφ m => hAd hw₀ φ hφ m
      approx := by
        intro tys f hf hlev harch
        obtain ⟨SK, hNS⟩ := exists_finset_dvd_level Φ
        obtain ⟨ff, fa, hff, hffs, hfa, hbi, hlim⟩ :=
          hL4 ℚ ℚ Φ.level SK hNS tys f hf (by rw [ideal_map_self]; exact hlev) harch
        rw [ideal_map_self] at hffs
        exact ⟨ff, fa, hff, hffs, hfa, fun n => (hbi n).isArchBiFinite, hlim⟩ }
  obtain ⟨S, V, k, hS, hV, ⟨ψ₀, hψ₀⟩, hk⟩ := exists_piece_ne_bot hin _hd _hcov R _hR
  obtain ⟨k₀, hmin, lam, ψ, hψ, hψ0, hΩ⟩ := exists_minimalWeight_eigenvector hin hV _hd _hcov hk
  obtain ⟨u₀, a, hcomp⟩ := CentralData.exists_isArchCompAt R _hR default hw₀
  obtain ⟨σ, hσ'⟩ := CentralData.exists_norm_ideleChar_eq R _hR
  have hσ : ∀ z : (⊤ : Subgroup (AdeleRing (𝓞 ℚ) ℚ)ˣ),
      ‖((R.centralChar z : ℂˣ) : ℂ)‖ = ideleNorm ℚ (z : (AdeleRing (𝓞 ℚ) ℚ)ˣ) ^ σ :=
    fun z => hσ' z
  obtain ⟨φ, P, hD⟩ : ∃ (φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ) (P : RealArchParam), ParamData hw₀ R S P (k₀ : ℤ) φ := by
    obtain h0 | h1 | h2 : k₀ = 0 ∨ k₀ = 1 ∨ 2 ≤ k₀ := by omega
    · subst h0
      obtain ⟨φ, s, hφ0, hφdef, -, hφΩ, hJ⟩ := WeightShift.exists_reflectJ_eigen hin.casimir_translate hψ0
        (isArchSmoothAt_of_mem_piece hin hV _hd _hcov hψ) hΩ
      have hψJ : WeightShift.reflectJ hw₀ ψ ∈ piece hw₀ R.centralChar S Φ V ((0 : ℕ) : ℤ) := by
        have h := reflectJ_mem_piece hin hV _hd _hcov hψ
        rwa [show -(((0 : ℕ) : ℤ)) = ((0 : ℕ) : ℤ) by simp] at h
      have hφmem : φ ∈ piece hw₀ R.centralChar S Φ V ((0 : ℕ) : ℤ) := by
        rcases hφdef with rfl | rfl
        · exact Submodule.add_mem _ hψ hψJ
        · exact Submodule.sub_mem _ hψ hψJ
      obtain ⟨P, hP⟩ := paramData_of_low hin hV hψ₀ hσ hcomp _hd _hcov (Or.inl (by simp)) hφmem hφ0 hφΩ s fun _ => hJ
      exact ⟨φ, P, hP⟩
    · subst h1
      obtain ⟨P, hP⟩ := paramData_of_low hin hV hψ₀ hσ hcomp _hd _hcov (Or.inr (by simp)) hψ hψ0 hΩ 0
        fun h => by simp at h
      exact ⟨ψ, P, hP⟩
    · have hmin' : piece hw₀ R.centralChar S Φ V ((k₀ : ℤ) - 2) = ⊥ := hmin _ (by omega)
      obtain ⟨P, hP⟩ := paramData_of_discrete hin hV hψ₀ hcomp _hd _hcov (by omega) hmin' hψ hψ0 hΩ
      exact ⟨ψ, P, hP⟩
  refine ⟨S, fun _ _ => P, hS, fun _ _ u₁ u₂ a₁ a₂ h => hD.principal_bound u₁ u₂ a₁ a₂ h, ?_, φ, fun _ => (k₀ : ℤ),
    hD.iso, hD.ne_zero, hD.repro, ?_, fun _ _ u₁ u₂ a₁ a₂ h => hD.principal_weight u₁ u₂ a₁ a₂ h,
    fun _ _ u n hn h => hD.discrete_weight u n hn h, ?_, ?_, ?_, ?_⟩
  · intro w' hw'
    obtain rfl : (default : InfinitePlace ℚ) = w' := Subsingleton.elim _ _
    exact hD.central
  · intro w' hw'
    obtain rfl : (default : InfinitePlace ℚ) = w' := Subsingleton.elim _ _
    exact hD.weight
  · intro w' hw'
    obtain rfl : (default : InfinitePlace ℚ) = w' := Subsingleton.elim _ _
    exact ⟨hD.smooth, hD.eigen⟩
  · intro w' hw' u₁ u₂ a₁ h g
    obtain rfl : (default : InfinitePlace ℚ) = w' := Subsingleton.elim _ _
    exact hD.reflect u₁ u₂ a₁ h g
  · intro w' hw' u n hn h
    obtain rfl : (default : InfinitePlace ℚ) = w' := Subsingleton.elim _ _
    exact hD.lower_discrete u n hn h
  · intro w' hw' u a₁ a₂ h hne
    obtain rfl : (default : InfinitePlace ℚ) = w' := Subsingleton.elim _ _
    exact hD.lower_principal u a₁ a₂ h hne

end MinimalWeightVector

theorem solution
    (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 ℚ) ℚ))
    (_hd : d₁ < d₂)
    (_hcov : CoversModCentre ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂))
    (Φ : HeckeEigensystem ℚ ℂ)
    (R : SmoothCuspRealizationAt ℚ
      (productionPinsOf ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂)
        (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v)
        (adelicBox ℚ))
      Φ.toRawCentral)
    (_hR : Continuous R.toFun) :
    ∃ (S : Finset (HeightOneSpectrum (𝓞 ℚ)))
      (archR : ∀ w : InfinitePlace ℚ, w.IsReal → RealArchParam),
      R.exceptionalSet ⊆ S ∧
      (∀ (w : InfinitePlace ℚ) (hw : w.IsReal) (u₁ u₂ : ℂ) (a₁ a₂ : ZMod 2),
        archR w hw = RealArchParam.principal u₁ a₁ u₂ a₂ → |(u₁ - u₂).re| < 1) ∧
      (∀ (w : InfinitePlace ℚ) (hw : w.IsReal),
        IsArchCompAt ℚ (R.centralChar.comp Subgroup.topEquiv.symm.toMonoidHom) w
          ((archR w hw).centralExponent + 1) ((archR w hw).centralSign.val : ℤ)) ∧
      ∃ (φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ) (k : InfinitePlace ℚ → ℤ),
        IsIsotypicCuspFormAt ℚ
            (productionPinsOf ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂)
              (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ)
              (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ))
            R.centralChar Φ.level S Φ φ ∧
        φ ≠ 0 ∧
        (∃ α : AdelicGL2 (𝓞 ℚ) ℚ → ℂ, IsFactorizableTestFn ℚ α ∧ rightConv ℚ φ α = φ) ∧
        (∀ (w : InfinitePlace ℚ) (hw : w.IsReal),
          HasArchCharacterAt₀ ℚ w (archWeightCharAt hw (k w)) φ) ∧
        (∀ (w : InfinitePlace ℚ) (hw : w.IsReal) (u₁ u₂ : ℂ) (a₁ a₂ : ZMod 2),
          archR w hw = RealArchParam.principal u₁ a₁ u₂ a₂ →
            (k w = 0 ∨ k w = 1) ∧ ((k w : ZMod 2) = a₁ + a₂)) ∧
        (∀ (w : InfinitePlace ℚ) (hw : w.IsReal) (u₀ : ℂ) (n : ℕ) (hn : 1 ≤ n),
          archR w hw = RealArchParam.discrete u₀ n hn → k w = (n : ℤ) + 1) ∧
        (∀ (w : InfinitePlace ℚ) (hw : w.IsReal),
          IsArchSmoothAt hw φ ∧ archCasimirAt hw φ = (archR w hw).laplaceEigenvalue • φ) ∧
        (∀ (w : InfinitePlace ℚ) (hw : w.IsReal) (u₁ u₂ : ℂ) (a₁ : ZMod 2),
          archR w hw = RealArchParam.principal u₁ a₁ u₂ a₁ →
            ∀ g : AdelicGL2 (𝓞 ℚ) ℚ, φ (g * archRealGLAt hw UpperHalfPlane.J) = (-1 : ℂ) ^ a₁.val * φ g) ∧
        (∀ (w : InfinitePlace ℚ) (hw : w.IsReal) (u₀ : ℂ) (n : ℕ) (hn : 1 ≤ n),
          archR w hw = RealArchParam.discrete u₀ n hn →
            archDerivAt hw ArchDir.H φ
                - Complex.I • (archDerivAt hw ArchDir.E φ + archDerivAt hw ArchDir.Fm φ) = 0) ∧
        (∀ (w : InfinitePlace ℚ) (hw : w.IsReal) (u₀ : ℂ) (a₁ a₂ : ZMod 2),
          archR w hw = RealArchParam.principal u₀ a₁ u₀ a₂ → a₁ ≠ a₂ →
            archDerivAt hw ArchDir.H φ
                - Complex.I • (archDerivAt hw ArchDir.E φ + archDerivAt hw ArchDir.Fm φ) = 0) :=
  MinimalWeightVector.eigenvector_of_realization c u d₁ d₂ T _hd _hcov Φ R _hR
    AutomorphicForm.isIsotypicCuspFormAt_rightConv_of_isFactorizableTestFn_of_support_subset_of_coversModCentre
    AutomorphicForm.exists_finTestFactor_isUnitFactorizableAboveOfType_tendsto_rightConv_of_mem_archCutSubmodule
    AutomorphicForm.archCasimirAt_comp_mul_archRealGLAt

end

end S_LanglandsTunnell_exists_archCasimir_eigenvector_minimalWeight_of_continuous_realization
end P2MW
export P2MW.S_LanglandsTunnell_exists_archCasimir_eigenvector_minimalWeight_of_continuous_realization (solution)
