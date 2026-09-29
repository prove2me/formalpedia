-- Prove2me | solution 1 for LanglandsTunnell.ofReal_eq_laplaceEigenvalue_principal_of_archCasimirAt_eq_smul_of_mellin_eq_archFactor_principal
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/8f5c0fb2-2548-5ca9-a2eb-85b7befa9de3

import Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Definitions.Def_LanglandsTunnell_RankinSelbergEuler
import Definitions.Def_LanglandsTunnell_RS22GlobalIntegral
import Definitions.Def_AutomorphicForm_GodementSection
import Definitions.Def_LanglandsTunnell_RSCarrier
import Definitions.Def_LanglandsTunnell_RSCarrierSplit
import Definitions.Def_LanglandsTunnell_DeltaLift
import Definitions.Def_AutomorphicForm_WhittakerCoefficient
import Definitions.Def_AutomorphicForm_SiegelCoordinates
import Definitions.Def_AutomorphicForm_RowIsometryInvariance
import Definitions.Def_NumberField_StandardGlobalAddCharRat
import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Mathlib.MeasureTheory.Group.FundamentalDomain
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.MellinTransform
import Definitions.Def_LanglandsTunnell_ArchParam
import Definitions.Def_AutomorphicForm_IsotypicCuspSpace
import Definitions.Def_AutomorphicForm_CuspidalConstituent
import Definitions.Def_AutomorphicForm_RightConvolution
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_LanglandsTunnell_ConverseData
import Definitions.Def_AutomorphicForm_ArchWeightCharTransport

import Theorems.Thm_LanglandsTunnell_exists_torusSheets_whittakerODE_of_isIsotypicCuspFormAt_of_archCasimirAt_eq_of_whittaker_factorisation_rat
import Theorems.Thm_LanglandsTunnell_ArchBessel_sq_eq_sq_of_whittakerODE_pair_of_add_mul_eq_mul_cpow_mul_besselKernel
import Theorems.Thm_LanglandsTunnell_ArchBessel_sq_eq_sq_of_whittakerODE_pair_of_add_eq_mul_besselKernel_of_sub_eq_mul_besselKernel
import Theorems.Thm_LanglandsTunnell_ArchBessel_eq_mul_cpow_mul_besselKernel_of_continuousOn_of_mellin_eq_mul_GammaR_mul_GammaR
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_ofReal_eq_laplaceEigenvalue_principal_of_archCasimirAt_eq_smul_of_mellin_eq_archFactor_principal
p2m_attr_erase "instance" "IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_1 IsDedekindDomain.HeightOneSpectrum.instMulActionHomClassAlgHomTensorProductAdicCompletionForallValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteForallValEqUnderOfFiniteDimensional_definitions IsDedekindDomain.HeightOneSpectrum.instIsBiscalarSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersTensorProductCoeAlgHomTensorAdicCompletionIntegersTo IsDedekindDomain.HeightOneSpectrum.Extension.instContinuousSMulAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopology IsDedekindDomain.HeightOneSpectrum.Extension.instFiniteSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnderOfFiniteDimensional IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteValEqUnderOfFiniteDimensional_definitions instIsBiscalarTensorProductCoeAlgHomBaseChange_of_algebraMap IsDedekindDomain.HeightOneSpectrum.instIsScalarTowerSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopologyPi IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions Submodule.instIsTopologicalModuleSubtypeMem Pi.instTopologicalModule IsTopologicalModule.toContinuousSMul IsTopologicalModule.toContinuousAdd instFunLike SemialgHomClass.toSemilinearMapClass instCoeTCSemialgHom SemialgHomClass.toRingHomClass SemialgHomClass.instSemialgHom FLT.InfiniteAdeleBaseChange.uniqueSelfExtension NumberField.InfinitePlace.RamifiedExtension.instCoeExtension NumberField.InfinitePlace.UnramifiedExtension.instCoeExtension instCountableOfNumberField_definitions AutomorphicForm.compactSpace_maximalCompactAway AutomorphicForm.compactSpace_adelicMaximalCompact AutomorphicForm.isProbabilityMeasure_maximalCompactHaar AutomorphicForm.isHaarMeasure_maximalCompactHaar AutomorphicForm.compactSpace_maximalCompactAt AutomorphicForm.isProbabilityMeasure_maximalCompactAwayHaar AutomorphicForm.isHaarMeasure_maximalCompactAwayHaar AutomorphicForm.isProbabilityMeasure_maximalCompactAtHaar"
p2m_attr_erase "instance" "AutomorphicForm.isHaarMeasure_maximalCompactAtHaar instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions"
p2m_attr_erase "simp" "AutomorphicForm.mem_borelSubgroup_iff AutomorphicForm.borelDiagFst_apply_val AutomorphicForm.borelDiagSnd_apply_val SemialgHom.baseChange_of_algebraMap_tmul_left SemialgHom.baseChangeRightOfAlgebraMap_apply Pi.semialgHomPi_apply Pi.semialgHom_apply Module.Basis.rightBaseChange_apply LinearEquiv.coe_mulLeft LinearEquiv.coe_mulRight WithVal.semialgebraMap_toFun_ofVal Module.Basis.rightBaseChange_repr IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.tensorCoe_tmul IsDedekindDomain.HeightOneSpectrum.tensorAdicCompletionIntegersTo_tmul SemialgHom.baseChangeRightOfAlgebraMap_coe IsDedekindDomain.HeightOneSpectrum.adicCompletion.integerBaseChangeLinearEquiv_tmul_apply SemialgHom.baseChange_of_algebraMap_tmul_right IsLocalization.map_moduleTensorEquiv_symm_tmul IsLocalization.leftModuleTensorEquiv_apply IsLocalization.moduleLid_symm_apply IsLocalization.leftModuleTensorEquiv_symm_apply IsLocalization.map_moduleTensorEquiv_tmul IsModuleTopology.continuousLinearEquiv_apply AlgEquiv.extendScalars_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_apply IsModuleTopology.continuousAlgEquivOfIsBiscalar_apply AlgEquiv.extendScalars_apply IsModuleTopology.continuousLinearEquiv_symm_apply SemialgHom.restrictScalars_toFun SemialgHom.mk.sizeOf_spec SemialgHom.mk.injEq SemialgHom.coe_coe coe_mk TensorProduct.RightActions.smul_def TensorProduct.RightActions.Module.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.LinearMap.baseChange_id TensorProduct.RightActions.algebraMap_eval TensorProduct.RightActions.Module.TensorProduct.comm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_symm_apply_tmul"
p2m_attr_erase "simp" "TensorProduct.RightActions.Algebra.TensorProduct.comm_apply_tmul AutomorphicForm.mem_sigmaCentralizer_iff M4aHerbrand.ArchSemilocal.psiFactor_tmul M4aHerbrand.ArchSemilocal.psi_apply FLT.InfiniteAdeleBaseChange.evalAlgHom_apply FLT.InfiniteAdeleBaseChange.BaseChangeData.mk.sizeOf_spec FLT.InfiniteAdeleBaseChange.tensorPiAlgHom_tmul_apply FLT.InfiniteAdeleBaseChange.collapsePlaces_apply FLT.InfiniteAdeleBaseChange.tensorPiAlgEquiv_tmul_apply FLT.InfiniteAdeleBaseChange.InfinitePlaceData.mk.sizeOf_spec FLT.InfiniteAdeleBaseChange.InfinitePlaceData.mk.injEq FLT.InfiniteAdeleBaseChange.BaseChangeData.mk.injEq ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply"
p2m_attr_erase "simp" "RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply"

set_option autoImplicit false

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicFourier IsDedekindDomain
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering AutomorphicForm.SiegelCoordinates
open LanglandsTunnell LanglandsTunnell.RankinSelberg RSCarrier UnramifiedWhittaker AutomorphicForm.CuspidalConstituent

namespace ArchUnitaryBAux

theorem sqrt_cpow (t : ℝ) (ht : 0 < t) (z : ℂ) :
    ((Real.sqrt t : ℝ) : ℂ) ^ z = (t : ℂ) ^ (z / 2) := by
  rw [Real.sqrt_eq_rpow, Complex.ofReal_cpow ht.le, show z / 2 = ((1 / (2 : ℝ) : ℝ) : ℂ) * z by push_cast; ring,
    Complex.cpow_mul]
  · rw [← Complex.ofReal_log ht.le, ← Complex.ofReal_mul, Complex.ofReal_im]
    exact neg_lt_zero.mpr Real.pi_pos
  · rw [← Complex.ofReal_log ht.le, ← Complex.ofReal_mul, Complex.ofReal_im]
    exact Real.pi_pos.le

theorem zmod2_cases : ∀ x p : ZMod 2, x = p ∨ x = p + 1 := by decide

theorem zmod2_eq_add_one_of_ne : ∀ a₁ a₂ : ZMod 2, a₁ ≠ a₂ → a₂ = a₁ + 1 := by decide

theorem zmod2_add_self : ∀ a : ZMod 2, a + a = 0 := by decide
theorem zmod2_add_one_add_self : ∀ a : ZMod 2, a + 1 + a = 1 := by decide
theorem zmod2_add_add_one : ∀ a : ZMod 2, a + (a + 1) = 1 := by decide
theorem zmod2_add_one_add_add_one : ∀ a : ZMod 2, a + 1 + (a + 1) = 0 := by decide

theorem neg_one_pow_val_add_one (b : ZMod 2) :
    (-1 : ℂ) ^ (b + 1).val = -((-1 : ℂ) ^ b.val) := by
  rcases zmod2_cases b 0 with rfl | rfl
  · have h1 : ((0 : ZMod 2) + 1).val = 1 := by decide
    have h0 : (0 : ZMod 2).val = 0 := by decide
    rw [h1, h0]; norm_num
  · have h1 : ((0 : ZMod 2) + 1 + 1).val = 0 := by decide
    have h0 : ((0 : ZMod 2) + 1).val = 1 := by decide
    rw [h1, h0]; norm_num

theorem signShift_cases (a : ZMod 2) : signShift a = 0 ∨ signShift a = 1 := by
  unfold signShift; split_ifs <;> simp

end ArchUnitaryBAux

open ArchUnitaryBAux LanglandsTunnell.ArchBessel in
open _root_.LanglandsTunnell.RealArchParam in
theorem solution
    (ξ : (productionPinsGeneral ℚ).Z →* ℂˣ) (N : Ideal (𝓞 ℚ)) (S : Finset (HeightOneSpectrum (𝓞 ℚ)))
    (Θ : HeckeEigensystem ℚ ℂ)
    (φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ) (hφ : IsIsotypicCuspFormAt ℚ (productionPinsGeneral ℚ) ξ N S Θ φ)
    (hne0 : φ ≠ 0) (hconv : ∃ α : AdelicGL2 (𝓞 ℚ) ℚ → ℂ, IsFactorizableTestFn ℚ α ∧ rightConv ℚ φ α = φ)
    (hwt : ∀ (w : InfinitePlace ℚ) (hw : w.IsReal), ∃ n : ℤ, HasArchCharacterAt₀ ℚ w (archWeightCharAt hw n) φ)
    (WA : GL (Fin 2) ℝ → ℂ) (Wf : finiteAdelicGL2Subgroup ℚ → ℂ) (Wr : ℝ → ℂ)
    (hW : ∀ g : AdelicGL2 (𝓞 ℚ) ℚ,
      whittakerCoefficient ℚ (productionPinsGeneral ℚ) NumberField.StandardAddChar.psiQ φ 1 g = WA (ratArchGL2 g) * Wf (finFactor g))
    (hdiag : ∀ t : ℝˣ, WA (diagOne t) = Wr (t : ℝ))
    (hne : ∃ g : AdelicGL2 (𝓞 ℚ) ℚ,
      whittakerCoefficient ℚ (productionPinsGeneral ℚ) NumberField.StandardAddChar.psiQ φ 1 g ≠ 0)
    (u₁ u₂ : ℂ) (a₁ a₂ : ZMod 2) (par₀ : ZMod 2)
    (hcen : LanglandsTunnell.Converse.IsArchCompAt ℚ (ξ.comp Subgroup.topEquiv.symm.toMonoidHom) (default : InfinitePlace ℚ)
      ((RealArchParam.principal u₁ a₁ u₂ a₂).centralExponent + 1)
      (((RealArchParam.principal u₁ a₁ u₂ a₂).centralSign.val : ℕ) : ℤ))
    (hMel : ∀ b : ZMod 2, (b = par₀ ∨ b = par₀ + (RealArchParam.principal u₁ a₁ u₂ a₂).centralSign) →
      ∃ s₀ : ℝ, ∀ s : ℂ, s₀ < s.re →
        MellinConvergent (fun t : ℝ => (Wr t + (-1 : ℂ) ^ b.val * Wr (-t)) / (t : ℂ)) s ∧
          mellin (fun t : ℝ => (Wr t + (-1 : ℂ) ^ b.val * Wr (-t)) / (t : ℂ)) s =
            ((RealArchParam.principal u₁ a₁ u₂ a₂).twist 0 b).archFactor s)
    (lam : ℝ) (hsm : IsArchSmoothAt (IsTotallyReal.isReal (default : InfinitePlace ℚ)) φ)
    (hΩ : archCasimirAt (IsTotallyReal.isReal (default : InfinitePlace ℚ)) φ = (lam : ℂ) • φ) :
    (lam : ℂ) = (RealArchParam.principal u₁ a₁ u₂ a₂).laplaceEigenvalue := by
  classical
  have hw : (default : InfinitePlace ℚ).IsReal := IsTotallyReal.isReal _

  set ν : ℂ := ((1 / 4 : ℂ) - (lam : ℂ)) ^ ((2 : ℕ) : ℂ)⁻¹ with hνdef
  have hν : ν ^ 2 = 1 / 4 - (lam : ℂ) := by rw [hνdef]; exact Complex.cpow_nat_inv_pow _ two_ne_zero
  have hΩ' : archCasimirAt (IsTotallyReal.isReal (default : InfinitePlace ℚ)) φ = (1 / 4 - ν ^ 2) • φ := by
    rw [hν, sub_sub_cancel]; exact hΩ

  obtain ⟨n, c, P, Q, hc, hWrP, hWrQ, hPd, hPd', hPode, hQd, hQd', hQode⟩ :=
    LanglandsTunnell.exists_torusSheets_whittakerODE_of_isIsotypicCuspFormAt_of_archCasimirAt_eq_of_whittaker_factorisation_rat
      ξ N S Θ φ hφ hne0 hconv hwt WA Wf Wr hW hdiag hne _ _ hcen hsm ν hΩ'
  have huc : (RealArchParam.principal u₁ a₁ u₂ a₂).centralExponent + 1 = u₁ + u₂ + 1 := by
    simp [RealArchParam.centralExponent]
  have hQode' : ∀ y : ℝ, 0 < y →
      (y : ℂ) ^ 2 * deriv (deriv Q) y
        + (1 / 4 - ν ^ 2 - 2 * (Real.pi : ℂ) * ((n : ℝ) : ℂ) * (y : ℂ) - 4 * (Real.pi : ℂ) ^ 2 * (y : ℂ) ^ 2) * Q y = 0 := by
    intro y hy
    have h := hQode y hy
    push_cast at h
    linear_combination h

  have shape : ∀ b : ZMod 2, (b = par₀ ∨ b = par₀ + (RealArchParam.principal u₁ a₁ u₂ a₂).centralSign) →
      ∀ t : ℝ, 0 < t → P t + (-1 : ℂ) ^ b.val * Q t
        = (2 / c) * (t : ℂ) ^ ((1 + signShift (a₁ + b) + signShift (a₂ + b)) / 2)
            * besselKernel ((u₁ - u₂ + signShift (a₁ + b) - signShift (a₂ + b)) / 2) (2 * Real.pi * t) := by
    intro b hb t ht
    have ht0 : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht.ne'
    obtain ⟨s₀, hs₀⟩ := hMel b hb
    set ε : ℂ := (-1 : ℂ) ^ b.val with hε
    set f : ℝ → ℂ := fun t => (Wr t + (-1 : ℂ) ^ b.val * Wr (-t)) / (t : ℂ) with hfdef

    have hS : ContinuousOn (fun t : ℝ => ((Real.sqrt t : ℝ) : ℂ) ^ ((RealArchParam.principal u₁ a₁ u₂ a₂).centralExponent + 1)) (Set.Ioi 0) := by
      intro t ht
      have h1 : ContinuousAt (fun t : ℝ => ((Real.sqrt t : ℝ) : ℂ)) t :=
        (Complex.continuous_ofReal.comp Real.continuous_sqrt).continuousAt
      exact (h1.cpow continuousAt_const (Complex.ofReal_mem_slitPlane.mpr (Real.sqrt_pos.mpr ht))).continuousWithinAt
    have hcont : ContinuousOn f (Set.Ioi 0) := by
      have hg : ContinuousOn (fun t : ℝ => (c * ((Real.sqrt t : ℝ) : ℂ) ^ ((RealArchParam.principal u₁ a₁ u₂ a₂).centralExponent + 1) * P t
          + (-1 : ℂ) ^ b.val * (c * ((Real.sqrt t : ℝ) : ℂ) ^ ((RealArchParam.principal u₁ a₁ u₂ a₂).centralExponent + 1) * Q t)) / (t : ℂ)) (Set.Ioi 0) := by
        refine ContinuousOn.div ?_ Complex.continuous_ofReal.continuousOn fun t ht => Complex.ofReal_ne_zero.mpr (Set.mem_Ioi.mp ht).ne'
        exact ((continuousOn_const.mul hS).mul hPd.continuousOn).add
          (continuousOn_const.mul ((continuousOn_const.mul hS).mul hQd.continuousOn))
      refine hg.congr fun t ht => ?_
      rw [hfdef]
      show (Wr t + (-1 : ℂ) ^ b.val * Wr (-t)) / (t : ℂ) = _
      rw [hWrP t ht, hWrQ t ht]
    have hM : ∀ s : ℂ, s₀ < s.re → MellinConvergent f s ∧
        mellin f s = 1 * Complex.Gammaℝ (s + (u₁ + signShift (a₁ + b))) * Complex.Gammaℝ (s + (u₂ + signShift (a₂ + b))) := by
      intro s hs
      obtain ⟨h1, h2⟩ := hs₀ s hs
      refine ⟨h1, ?_⟩
      rw [h2]
      simp only [RealArchParam.archFactor, RealArchParam.gammaR, RealArchParam.gammaC, RealArchParam.twist,
        Multiset.map_zero, Multiset.prod_zero, mul_one, Multiset.insert_eq_cons, Multiset.map_cons,
        Multiset.map_singleton, Multiset.prod_cons, Multiset.prod_singleton, add_zero, one_mul]
    have hbes := LanglandsTunnell.ArchBessel.eq_mul_cpow_mul_besselKernel_of_continuousOn_of_mellin_eq_mul_GammaR_mul_GammaR f 1
      (u₁ + signShift (a₁ + b)) (u₂ + signShift (a₂ + b)) s₀ hcont hM t ht
    have hbes' : Wr t + ε * Wr (-t)
        = 2 * 1 * (t : ℂ) ^ ((u₁ + signShift (a₁ + b) + (u₂ + signShift (a₂ + b))) / 2)
          * besselKernel ((u₁ + signShift (a₁ + b) - (u₂ + signShift (a₂ + b))) / 2) (2 * Real.pi * t) * (t : ℂ) := by
      rw [← div_eq_iff ht0]; exact hbes
    have hsq : ((Real.sqrt t : ℝ) : ℂ) ^ ((RealArchParam.principal u₁ a₁ u₂ a₂).centralExponent + 1) = (t : ℂ) ^ ((u₁ + u₂ + 1) / 2) := by
      rw [sqrt_cpow t ht, huc]
    have hcB : c * (t : ℂ) ^ ((u₁ + u₂ + 1) / 2) ≠ 0 :=
      mul_ne_zero hc (fun h => ht0 (Complex.cpow_eq_zero_iff _ _ |>.mp h).1)
    have hexp : (t : ℂ) ^ ((1 + signShift (a₁ + b) + signShift (a₂ + b)) / 2) * (t : ℂ) ^ ((u₁ + u₂ + 1) / 2)
        = (t : ℂ) ^ ((u₁ + signShift (a₁ + b) + (u₂ + signShift (a₂ + b))) / 2) * (t : ℂ) := by
      rw [← Complex.cpow_add _ _ ht0,
        show (1 + signShift (a₁ + b) + signShift (a₂ + b)) / 2 + (u₁ + u₂ + 1) / 2
          = (u₁ + signShift (a₁ + b) + (u₂ + signShift (a₂ + b))) / 2 + 1 by ring,
        Complex.cpow_add _ _ ht0, Complex.cpow_one]
    apply mul_left_cancel₀ hcB
    have key1 : c * (t : ℂ) ^ ((u₁ + u₂ + 1) / 2) * (P t + (-1 : ℂ) ^ b.val * Q t) = Wr t + ε * Wr (-t) := by
      rw [hWrP t ht, hWrQ t ht, hsq, hε]; ring
    rw [key1, hbes']
    calc _ = 2 * ((t : ℂ) ^ ((u₁ + signShift (a₁ + b) + (u₂ + signShift (a₂ + b))) / 2) * (t : ℂ))
          * besselKernel ((u₁ + signShift (a₁ + b) - (u₂ + signShift (a₂ + b))) / 2) (2 * Real.pi * t) := by ring
      _ = 2 * ((t : ℂ) ^ ((1 + signShift (a₁ + b) + signShift (a₂ + b)) / 2) * (t : ℂ) ^ ((u₁ + u₂ + 1) / 2))
          * besselKernel ((u₁ - u₂ + signShift (a₁ + b) - signShift (a₂ + b)) / 2) (2 * Real.pi * t) := by
        rw [hexp]; congr 2; ring
      _ = _ := by field_simp

  have key : ((u₁ - u₂) / 2) ^ 2 = ν ^ 2 := by
    by_cases ha : a₁ = a₂
    ·
      have hsh := shape par₀ (Or.inl rfl)
      rw [← ha] at hsh
      have he : (1 + signShift (a₁ + par₀) + signShift (a₁ + par₀)) / 2 = (1 / 2 : ℂ)
          ∨ (1 + signShift (a₁ + par₀) + signShift (a₁ + par₀)) / 2 = (3 / 2 : ℂ) := by
        rcases signShift_cases (a₁ + par₀) with h | h <;> rw [h] <;> norm_num
      have h5 := LanglandsTunnell.ArchBessel.sq_eq_sq_of_whittakerODE_pair_of_add_mul_eq_mul_cpow_mul_besselKernel
        ν ((u₁ - u₂ + signShift (a₁ + par₀) - signShift (a₁ + par₀)) / 2) ((n : ℝ) : ℂ) ((-1 : ℂ) ^ par₀.val) (2 / c)
        ((1 + signShift (a₁ + par₀) + signShift (a₁ + par₀)) / 2) P Q hPd hPd' hPode hQd hQd' hQode'
        (div_ne_zero two_ne_zero hc) he hsh
      linear_combination h5
    ·
      have ha' : a₂ = a₁ + 1 := zmod2_eq_add_one_of_ne a₁ a₂ ha
      have hcs : (RealArchParam.principal u₁ a₁ u₂ a₂).centralSign = 1 := by
        show a₁ + a₂ = 1
        rw [ha']; exact zmod2_add_add_one a₁
      have hadm : ∀ b : ZMod 2, b = par₀ ∨ b = par₀ + (RealArchParam.principal u₁ a₁ u₂ a₂).centralSign := by
        intro b; rw [hcs]; exact zmod2_cases b par₀
      have e00 : a₁ + a₁ = 0 := zmod2_add_self a₁
      have e21 : a₂ + a₁ = 1 := by rw [ha']; exact zmod2_add_one_add_self a₁
      have e11 : a₁ + (a₁ + 1) = 1 := zmod2_add_add_one a₁
      have e20 : a₂ + (a₁ + 1) = 0 := by rw [ha']; exact zmod2_add_one_add_add_one a₁
      have h0 := shape a₁ (hadm a₁)
      have h1 := shape (a₁ + 1) (hadm (a₁ + 1))
      simp only [e00, e21, e11, e20, signShift_zero, signShift_one, neg_one_pow_val_add_one] at h0 h1
      set ε₀ : ℂ := (-1 : ℂ) ^ a₁.val with hε₀
      set Q' : ℝ → ℂ := fun y => ε₀ * Q y with hQ'def
      have hQ'd : DifferentiableOn ℝ Q' (Set.Ioi 0) := hQd.const_mul ε₀
      have hdQ' : deriv Q' = fun y => ε₀ * deriv Q y := by
        funext y; rw [hQ'def]; exact deriv_const_mul_field ε₀
      have hQ'd' : DifferentiableOn ℝ (deriv Q') (Set.Ioi 0) := by rw [hdQ']; exact hQd'.const_mul ε₀
      have hddQ' : ∀ y : ℝ, deriv (deriv Q') y = ε₀ * deriv (deriv Q) y := by
        intro y; rw [hdQ']; exact deriv_const_mul_field ε₀
      have hQ'ode : ∀ y : ℝ, 0 < y →
          (y : ℂ) ^ 2 * deriv (deriv Q') y
            + (1 / 4 - ν ^ 2 - 2 * (Real.pi : ℂ) * ((n : ℝ) : ℂ) * (y : ℂ) - 4 * (Real.pi : ℂ) ^ 2 * (y : ℂ) ^ 2) * Q' y = 0 := by
        intro y hy
        rw [hddQ', hQ'def]
        linear_combination ε₀ * hQode' y hy
      have hi0 : (u₁ - u₂ + 0 - 1) / 2 = (u₁ - u₂ - 1) / 2 := by ring
      have he0 : ((1 : ℂ) + 0 + 1) / 2 = 1 := by norm_num
      have hi1 : (u₁ - u₂ + 1 - 0) / 2 = (u₁ - u₂ - 1) / 2 + 1 := by ring
      have he1 : ((1 : ℂ) + 1 + 0) / 2 = 1 := by norm_num
      have hadd : ∀ y : ℝ, 0 < y → P y + Q' y = (2 / c) * (y : ℂ) * besselKernel ((u₁ - u₂ - 1) / 2) (2 * Real.pi * y) := by
        intro y hy
        have h := h0 y hy
        rw [hi0, he0, Complex.cpow_one] at h
        rw [hQ'def, hε₀]
        exact h
      have hsub : ∀ y : ℝ, 0 < y → P y - Q' y = (2 / c) * (y : ℂ) * besselKernel ((u₁ - u₂ - 1) / 2 + 1) (2 * Real.pi * y) := by
        intro y hy
        have h := h1 y hy
        rw [hi1, he1, Complex.cpow_one, neg_mul, ← sub_eq_add_neg] at h
        rw [hQ'def, hε₀]
        exact h
      have h5 := LanglandsTunnell.ArchBessel.sq_eq_sq_of_whittakerODE_pair_of_add_eq_mul_besselKernel_of_sub_eq_mul_besselKernel
        ν ((u₁ - u₂ - 1) / 2) ((n : ℝ) : ℂ) (2 / c) (2 / c) P Q' hPd hPd' hPode hQ'd hQ'd' hQ'ode
        (div_ne_zero two_ne_zero hc) (div_ne_zero two_ne_zero hc) hadd hsub
      linear_combination h5
  rw [RealArchParam.laplaceEigenvalue_principal]
  linear_combination key + hν

end S_LanglandsTunnell_ofReal_eq_laplaceEigenvalue_principal_of_archCasimirAt_eq_smul_of_mellin_eq_archFactor_principal
end P2MW
export P2MW.S_LanglandsTunnell_ofReal_eq_laplaceEigenvalue_principal_of_archCasimirAt_eq_smul_of_mellin_eq_archFactor_principal (solution)
