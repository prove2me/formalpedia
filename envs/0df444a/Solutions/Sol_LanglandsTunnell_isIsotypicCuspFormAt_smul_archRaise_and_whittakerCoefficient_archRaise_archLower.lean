-- Prove2me | solution 1 for LanglandsTunnell.isIsotypicCuspFormAt_smul_archRaise_and_whittakerCoefficient_archRaise_archLower
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/a0bc2bab-9237-5e4b-98c8-bbb07cf7ae5c

import Definitions.Def_AutomorphicForm_IsotypicCuspSpace
import Definitions.Def_AutomorphicForm_ArchWeightCharTransport
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_AutomorphicForm_WhittakerCoefficient
import Definitions.Def_LanglandsTunnell_ConverseData
import Definitions.Def_AutomorphicForm_ArchDerivCasimir
import Mathlib.Analysis.MellinTransform
import Mathlib.Tactic.Module
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Definitions.Def_AutomorphicForm_AdelicLsXi
import Definitions.Def_AutomorphicForm_CarrierPins
import Definitions.Def_AutomorphicForm_ArchType
import Definitions.Def_AutomorphicForm_SiegelCovering
import Definitions.Def_NumberField_AdelicVolume
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_AutomorphicForm_ArchWeightChar
import Definitions.Def_NumberField_AdelicTraceProducer
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_AutomorphicForm_BorelSubgroup
import Definitions.Def_AutomorphicForm_RowIsometryInvariance
import Definitions.Def_AutomorphicForm_ConstantTerm
import Definitions.Def_AutomorphicForm_GL2RealOrbitalTransforms
import Definitions.Def_AutomorphicForm_ArithCuspRealization
import Definitions.Def_AutomorphicForm_RightConvolution
import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_NumberField_AdelicHaar
import Theorems.Thm_LanglandsTunnell_isArchSmoothAt_whittakerCoefficient_and_archDerivAt_comm
import Theorems.Thm_AutomorphicForm_isKfSmooth_rightConv
import Theorems.Thm_AutomorphicForm_whittakerCoefficientIntegrable_and_summable_of_isKfSmooth_of_contDiff
import Theorems.Thm_AutomorphicForm_rightConv_apply_mul_eq_rightConv_comp_inv_mul_apply
import Theorems.Thm_AutomorphicForm_isIsotypicCuspFormAt_rightConv_of_isFactorizableTestFn_of_support_subset_of_coversModCentre
import Theorems.Thm_AutomorphicForm_exists_finTestFactor_isUnitFactorizableAboveOfType_tendsto_rightConv_of_mem_archCutSubmodule
import Theorems.Thm_AutomorphicForm_finiteDimensional_isotypicCuspSubmodule_inf_archCutSubmodule
import Theorems.Thm_AutomorphicForm_continuous_and_hasCompactSupport_of_isFactorizableTestFn
import Theorems.Thm_AutomorphicForm_archDerivAt_rightConv_eq_rightConv_deriv_of_isFactorizableTestFn
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_isIsotypicCuspFormAt_smul_archRaise_and_whittakerCoefficient_archRaise_archLower
p2m_attr_erase "instance" "RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions instCountableOfNumberField_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions AutomorphicForm.compactSpace_maximalCompactAway AutomorphicForm.compactSpace_adelicMaximalCompact AutomorphicForm.isProbabilityMeasure_maximalCompactHaar AutomorphicForm.isHaarMeasure_maximalCompactHaar AutomorphicForm.compactSpace_maximalCompactAt AutomorphicForm.isProbabilityMeasure_maximalCompactAwayHaar AutomorphicForm.isHaarMeasure_maximalCompactAwayHaar AutomorphicForm.isProbabilityMeasure_maximalCompactAtHaar AutomorphicForm.isHaarMeasure_maximalCompactAtHaar"
p2m_attr_erase "simp" "ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply AutomorphicForm.CuspidalConstituent.rightRegular_apply LocalGL2.coe_localRepSome"
p2m_attr_erase "simp" "LocalGL2.coe_diagPi LocalGL2.coe_localRepInf LocalGL2.coe_localRepSome_inv LocalGL2.coe_unipotentInt LocalGL2.coe_weylInt LocalGL2.coe_diagPi_inv LocalGL2.transposeGL_val LocalGL2.transposeGL_one LocalGL2.swapUnit_val AdelicDock.coe_finEmbed AdelicDock.splice_apply_self AdelicDock.coe_localEmbed AutomorphicForm.CuspidalSpectrum.fdPins_μ AutomorphicForm.CuspidalSpectrum.fdPins_nS AutomorphicForm.CuspidalSpectrum.fdPins_ν AutomorphicForm.CuspidalSpectrum.fdPins_gen AutomorphicForm.CuspidalSpectrum.fdPins_U AutomorphicForm.CuspidalSpectrum.fdPins_D AutomorphicForm.CuspidalSpectrum.fdPins_Z AutomorphicForm.CuspidalSpectrum.mem_detNormSlab AutomorphicForm.CuspidalSpectrum.fdPins_eq AutomorphicForm.CuspidalSpectrum.fdPins_mS AutomorphicForm.fnTwist_zero AutomorphicForm.fnTwist_apply AutomorphicForm.iotaZsqrtdNegTwo_apply"

set_option autoImplicit false
open IsDedekindDomain NumberField MeasureTheory Matrix
open NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open NumberField.InfinitePlace.Completion
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open LanglandsTunnell LanglandsTunnell.Converse NumberField.TateGlobal

namespace MinimalWeightWhittaker
open IsDedekindDomain NumberField MeasureTheory Matrix NumberField.AdelicHaar NumberField.AdelicLevel
open NumberField.AdelicBox NumberField.InfinitePlace.Completion AutomorphicForm AutomorphicForm.WindowedSiegel
open AutomorphicForm.SiegelCovering LanglandsTunnell LanglandsTunnell.Converse NumberField.TateGlobal
open NumberField.AdelicVolume
open scoped Real
section CoefficientFunction
variable (F : Type) [Field F] [NumberField F]
section RealUnipotent

private theorem archRealGLAt_unipotentGL2_eq {w : InfinitePlace F} (hw : w.IsReal) (x : ℝ) :
    ∃ X : InfiniteAdeleRing F, X w = (ringEquivRealOfIsReal hw).symm x ∧ (∀ v : InfinitePlace F, v ≠ w → X v = 0) ∧
      archRealGLAt hw (unipotentGL2 x) = unipotentGL2 ((⟨X, 0⟩ : AdeleRing (𝓞 F) F)) := by
  set m : GL (Fin 2) w.Completion := glEquivOfRingEquiv (ringEquivRealOfIsReal hw).symm (unipotentGL2 x) with hm
  refine ⟨archMatrixUpdate F w (m : Matrix (Fin 2) (Fin 2) w.Completion) 0 1, ?_, ?_, ?_⟩
  · rw [archMatrixUpdate_apply_self, hm, glEquivOfRingEquiv_apply_entry]
    simp [unipotentGL2_coe]
  · intro v hv
    rw [archMatrixUpdate_apply_of_ne F w _ 0 1 hv]
    simp [Matrix.one_apply]
  · refine eq_of_glArch_eq_of_glFin_eq ?_ ?_
    · have h1 : AdelicLevel.glArch (𝓞 F) F (archRealGLAt hw (unipotentGL2 x)) = archGLIncl F w m :=
        glArch_adelicArchGLIncl F _
      rw [h1]
      apply Units.ext
      ext i j
      rw [AdelicLevel.glArch_apply]
      change archMatrixUpdate F w (m : Matrix (Fin 2) (Fin 2) w.Completion) i j = _
      funext v
      by_cases hv : v = w
      · subst hv
        rw [archMatrixUpdate_apply_self, hm, glEquivOfRingEquiv_apply_entry]
        fin_cases i <;> fin_cases j <;>
          simp [unipotentGL2_coe, archMatrixUpdate_apply_self, glEquivOfRingEquiv_apply_entry] <;> rfl
      · rw [archMatrixUpdate_apply_of_ne F w _ i j hv]
        fin_cases i <;> fin_cases j <;>
          simp [unipotentGL2_coe, Matrix.one_apply,
            archMatrixUpdate_apply_of_ne F w (m : Matrix (Fin 2) (Fin 2) w.Completion) 0 1 hv] <;> rfl
    · have h2 : AdelicLevel.glFin (𝓞 F) F (archRealGLAt hw (unipotentGL2 x)) = 1 := glFin_adelicArchGLIncl F _
      rw [h2]
      apply Units.ext
      ext i j
      rw [AdelicLevel.glFin_apply]
      fin_cases i <;> fin_cases j <;> simp [unipotentGL2_coe, Matrix.one_apply]

end RealUnipotent
section Periodicity

private theorem globalPoints_unipotentGL2 (β : F) :
    globalPoints (𝓞 F) F (unipotentGL2 β) = unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) β) := by
  apply Units.ext
  ext i j
  change algebraMap F (AdeleRing (𝓞 F) F) ((unipotentGL2 β : Matrix (Fin 2) (Fin 2) F) i j)
    = (unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) β) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) i j
  fin_cases i <;> fin_cases j <;> simp [unipotentGL2_coe]

variable {F}

private theorem isLsXiFunction_of_isIsotypicCuspFormAt {pins : CarrierPins F} {ξ : pins.Z →* ℂˣ} {N : Ideal (𝓞 F)}
    {S : Finset (HeightOneSpectrum (𝓞 F))} {Φ : HeckeEigensystem F ℂ} {φ : AdelicGL2 (𝓞 F) F → ℂ}
    (h : IsIsotypicCuspFormAt F pins ξ N S Φ φ) : IsLsXiFunction (𝓞 F) F pins.Z ξ φ := by
  letI := pins.mS
  exact ((lsXiMemberAt_iff (𝓞 F) F pins.μ pins.Z ξ pins.D φ).mp h.smoothCusp.1.1).1

variable (F)
end Periodicity
section ReferenceDatum
variable {F}

private theorem apply_unipotentGL2_algebraMap_mul_of_isIsotypicCuspFormAt {pins : CarrierPins F} {ξ : pins.Z →* ℂˣ}
    {N : Ideal (𝓞 F)} {S : Finset (HeightOneSpectrum (𝓞 F))} {Φ : HeckeEigensystem F ℂ} {φ : AdelicGL2 (𝓞 F) F → ℂ}
    (h : IsIsotypicCuspFormAt F pins ξ N S Φ φ) (β : F) (g : AdelicGL2 (𝓞 F) F) :
    φ (unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) β) * g) = φ g := by
  rw [← globalPoints_unipotentGL2, (isLsXiFunction_of_isIsotypicCuspFormAt h).left_invariant]

end ReferenceDatum
section ReferenceDatumRat

private theorem glArch_archRealGLAt_archRealProjAt_rat {w : InfinitePlace ℚ} (hw : w.IsReal) (g : AdelicGL2 (𝓞 ℚ) ℚ) :
    AdelicLevel.glArch (𝓞 ℚ) ℚ (archRealGLAt hw (archRealProjAt hw g)) = AdelicLevel.glArch (𝓞 ℚ) ℚ g := by
  set m : GL (Fin 2) w.Completion := glEquivOfRingEquiv (ringEquivRealOfIsReal hw).symm (archRealProjAt hw g) with hm
  have h1 : AdelicLevel.glArch (𝓞 ℚ) ℚ (archRealGLAt hw (archRealProjAt hw g)) = archGLIncl ℚ w m :=
    glArch_adelicArchGLIncl ℚ _
  rw [h1]
  apply Units.ext
  ext i j
  change archMatrixUpdate ℚ w (m : Matrix (Fin 2) (Fin 2) w.Completion) i j = _
  funext v
  rw [Subsingleton.elim v w, archMatrixUpdate_apply_self, hm, glEquivOfRingEquiv_apply_entry]
  change (ringEquivRealOfIsReal hw).symm ((glEquivOfRingEquiv (ringEquivRealOfIsReal hw)
    (AdelicLevel.archComponent ℚ w (AdelicLevel.glArch (𝓞 ℚ) ℚ g)) : Matrix (Fin 2) (Fin 2) ℝ) i j) = _
  rw [glEquivOfRingEquiv_apply_entry, RingEquiv.symm_apply_apply, AdelicLevel.archComponent_apply]

private theorem glArch_inv_archRealGLAt_archRealProjAt_mul_rat
    {w : InfinitePlace ℚ} (hw : w.IsReal) (g : AdelicGL2 (𝓞 ℚ) ℚ) :
    AdelicLevel.glArch (𝓞 ℚ) ℚ ((archRealGLAt hw (archRealProjAt hw g))⁻¹ * g) = 1 := by
  rw [map_mul, map_inv, glArch_archRealGLAt_archRealProjAt_rat, inv_mul_cancel]

open NumberField.StandardAddChar in

private theorem unipotentGL2_ratArchLine_eq_archRealGLAt {w : InfinitePlace ℚ} (hw : w.IsReal) (t : ℝ) :
    unipotentGL2 (R := AdeleRing (𝓞 ℚ) ℚ) (ratArchLine t, 0) = archRealGLAt hw (unipotentGL2 t) := by
  obtain ⟨X, hXw, -, hX⟩ := archRealGLAt_unipotentGL2_eq ℚ hw t
  rw [hX]
  congr 2
  funext v
  rw [Subsingleton.elim v w, hXw]
  rfl

private theorem det_of_entries_ne_zero (m : GL (Fin 2) ℝ) :
    (Matrix.of fun i j => (m : Matrix (Fin 2) (Fin 2) ℝ) i j).det ≠ 0 :=
  (Matrix.isUnit_iff_isUnit_det (m : Matrix (Fin 2) (Fin 2) ℝ)).mp m.isUnit |>.ne_zero

private theorem archRealGLAt_eq_archRealLiftAt {w : InfinitePlace ℚ} (hw : w.IsReal) (m : GL (Fin 2) ℝ) :
    archRealGLAt hw m = archRealLiftAt hw fun i j => (m : Matrix (Fin 2) (Fin 2) ℝ) i j := by
  rw [archRealLiftAt_of_det_ne_zero hw (det_of_entries_ne_zero m)]
  congr 1
  exact Units.ext rfl

private theorem contDiff_unipotent_entries :
    ContDiff ℝ (⊤ : ℕ∞) fun t : ℝ => fun i j => ((unipotentGL2 t : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) i j := by
  refine contDiff_pi.2 fun i => contDiff_pi.2 fun j => ?_
  simp only [unipotentGL2_coe]
  fin_cases i <;> fin_cases j <;> simp <;> first | exact contDiff_const | exact contDiff_id

private theorem exists_eq_archRealGLAt_mul_of_glArch_eq_one_rat
    {w : InfinitePlace ℚ} (hw : w.IsReal) (g : AdelicGL2 (𝓞 ℚ) ℚ) :
    ∃ (p : GL (Fin 2) ℝ) (k : AdelicGL2 (𝓞 ℚ) ℚ), AdelicLevel.glArch (𝓞 ℚ) ℚ k = 1 ∧ g = archRealGLAt hw p * k :=
  ⟨archRealProjAt hw g, _, glArch_inv_archRealGLAt_archRealProjAt_mul_rat hw g, (mul_inv_cancel_left _ _).symm⟩

open NumberField.StandardAddChar in

private theorem contDiff_two_unipotentGL2_ratArchLine_mul_of_isArchSmoothAt {w : InfinitePlace ℚ} (hw : w.IsReal)
    {φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ} (hφ : IsArchSmoothAt hw φ) (g : AdelicGL2 (𝓞 ℚ) ℚ) :
    ContDiff ℝ 2 fun t : ℝ => φ (unipotentGL2 (R := AdeleRing (𝓞 ℚ) ℚ) (ratArchLine t, 0) * g) := by
  obtain ⟨p, k, hkarch, hg⟩ := exists_eq_archRealGLAt_mul_of_glArch_eq_one_rat hw g
  have hfun : (fun t : ℝ => φ (unipotentGL2 (R := AdeleRing (𝓞 ℚ) ℚ) (ratArchLine t, 0) * g))
      = (fun e : Fin 2 → Fin 2 → ℝ => φ (k * (1 * archRealLiftAt hw e))) ∘
          (fun t : ℝ => (Matrix.of.symm
            (Matrix.of (fun i j => ((unipotentGL2 t : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) i j)
              * (p : Matrix (Fin 2) (Fin 2) ℝ)) : Fin 2 → Fin 2 → ℝ)) := by
    funext t
    simp only [Function.comp, one_mul]
    rw [unipotentGL2_ratArchLine_eq_archRealGLAt hw t, hg, ← mul_assoc, ← map_mul,
      archRealGLAt_mul_comm_of_glArch_eq_one hw _ hkarch, archRealGLAt_eq_archRealLiftAt]
    rfl
  rw [hfun]
  have hcurve : ∀ t : ℝ, (Matrix.of (Matrix.of.symm
      (Matrix.of (fun i j => ((unipotentGL2 t : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) i j)
        * (p : Matrix (Fin 2) (Fin 2) ℝ)) : Fin 2 → Fin 2 → ℝ)).det ≠ 0 := by
    intro t
    rw [Equiv.apply_symm_apply]
    exact det_of_entries_ne_zero (unipotentGL2 t * p)
  exact (ContDiffOn.comp_contDiff (hφ.comp_mul_left k 1)
    ((contDiff_of_symm_mul_const _).comp contDiff_unipotent_entries) hcurve).of_le
    (WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤))

end ReferenceDatumRat
end CoefficientFunction
section WeightTransferAndCasimirEquation

private theorem whittakerCoefficient_smul_fn (F : Type) [Field F] [NumberField F]
    (pins : CarrierPins F) (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (c : ℂ) (φ : AdelicGL2 (𝓞 F) F → ℂ) (α : F) :
    whittakerCoefficient F pins ψ (c • φ) α = c • whittakerCoefficient F pins ψ φ α := by
  funext g
  unfold whittakerCoefficient
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [← integral_const_mul]
  congr 1
  funext x
  rw [mul_assoc]

private theorem isKfSmooth_of_exists_rightConv_eq (F : Type) [Field F] [NumberField F]
    (φ : AdelicGL2 (𝓞 F) F → ℂ)
    (hconv : ∃ α : AdelicGL2 (𝓞 F) F → ℂ, IsFactorizableTestFn F α ∧ rightConv F φ α = φ) :
    IsKfSmooth F φ := by
  obtain ⟨α, hα, hαφ⟩ := hconv
  have h := isKfSmooth_rightConv F φ α hα
  rwa [hαφ] at h

end WeightTransferAndCasimirEquation
section PolynomialGrowthOfCoefficients
section ArchCut

private noncomputable def weightTypeFamilyRat (k : InfinitePlace ℚ → ℤ) : ArchTypeFamily ℚ :=
  ArchTypeFamily.ofChar ℚ fun w => archWeightCharAt (isReal_infinitePlace_rat w) (k w)

private theorem mem_archCutSubmodule_weightTypeFamilyRat {k : InfinitePlace ℚ → ℤ} {φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ}
    (hk : ∀ (w : InfinitePlace ℚ) (hw : w.IsReal), HasArchCharacterAt₀ ℚ w (archWeightCharAt hw (k w)) φ) :
    φ ∈ archCutSubmodule ℚ (weightTypeFamilyRat k) :=
  (mem_archCutSubmodule_ofChar_iff ℚ _ φ).mpr fun w => hk w (isReal_infinitePlace_rat w)

end ArchCut
end PolynomialGrowthOfCoefficients
section ArchimedeanDerivations
noncomputable section
open NumberField NumberField.InfinitePlace.Completion Matrix
variable {F : Type} [Field F] [NumberField F]

private def mulRightArrayCLM (A : Matrix (Fin 2) (Fin 2) ℝ) : (Fin 2 → Fin 2 → ℝ) →L[ℝ] (Fin 2 → Fin 2 → ℝ) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun e => Matrix.of.symm (Matrix.of e * A)
      map_add' := by
        intro a b
        ext i j
        simp [Matrix.mul_apply, add_mul, Finset.sum_add_distrib]
      map_smul' := by
        intro c a
        ext i j
        simp [Matrix.mul_apply, mul_add, mul_assoc] }

private theorem mulRightArrayCLM_apply (A : Matrix (Fin 2) (Fin 2) ℝ) (e : Fin 2 → Fin 2 → ℝ) :
    mulRightArrayCLM A e = Matrix.of.symm (Matrix.of e * A) := rfl

private theorem isArchSmoothAt_archDerivAt_apply_mul_archRealLiftAt {w : InfinitePlace F} {hw : w.IsReal}
    {φ : AdelicGL2 (𝓞 F) F → ℂ} (hφ : IsArchSmoothAt hw φ) (d : ArchDir) (g : AdelicGL2 (𝓞 F) F)
    {e : Fin 2 → Fin 2 → ℝ} (he : (Matrix.of e).det ≠ 0) :
    archDerivAt hw d φ (g * archRealLiftAt hw e) =
      fderiv ℝ (fun e' => φ (g * archRealLiftAt hw e')) e (mulRightArrayCLM (archDirMatrix d) e) := by
  have hΦ := hφ g
  have hopen := isOpen_setOf_det_ne_zero
  have hdiff : HasFDerivAt (fun e' => φ (g * archRealLiftAt hw e'))
      (fderiv ℝ (fun e' => φ (g * archRealLiftAt hw e')) e)
      (Matrix.of.symm (Matrix.of e * (archFlowMatrix d 0 : Matrix (Fin 2) (Fin 2) ℝ))) := by
    rw [of_symm_mul_archFlowMatrix_zero]
    exact ((hΦ.contDiffAt (hopen.mem_nhds he)).differentiableAt (by simp)).hasFDerivAt
  have hfun : (fun t : ℝ => φ (g * archRealLiftAt hw e * archFlowAt hw d t)) =
      fun t : ℝ => φ (g * archRealLiftAt hw
        (Matrix.of.symm (Matrix.of e * (archFlowMatrix d t : Matrix (Fin 2) (Fin 2) ℝ)))) := by
    funext t
    rw [archFlowAt, mul_assoc, archRealLiftAt_mul_archRealGLAt hw he]
  rw [mulRightArrayCLM_apply]
  show deriv (fun t : ℝ => φ (g * archRealLiftAt hw e * archFlowAt hw d t)) 0 = _
  rw [hfun]
  simpa only [Function.comp_def] using
    (hdiff.comp_hasDerivAt (0 : ℝ) (hasDerivAt_of_symm_mul_archFlowMatrix e d)).deriv

private theorem det_of_of_symm_one : (Matrix.of (Matrix.of.symm (1 : Matrix (Fin 2) (Fin 2) ℝ))).det ≠ 0 := by
  rw [Equiv.apply_symm_apply, Matrix.det_one]
  exact one_ne_zero

private theorem isArchSmoothAt_archDerivAt_apply_eq_fderiv {w : InfinitePlace F} {hw : w.IsReal}
    {φ : AdelicGL2 (𝓞 F) F → ℂ} (hφ : IsArchSmoothAt hw φ) (d : ArchDir) (g : AdelicGL2 (𝓞 F) F) :
    archDerivAt hw d φ g =
      fderiv ℝ (fun e' => φ (g * archRealLiftAt hw e')) (Matrix.of.symm (1 : Matrix (Fin 2) (Fin 2) ℝ))
        (mulRightArrayCLM (archDirMatrix d) (Matrix.of.symm (1 : Matrix (Fin 2) (Fin 2) ℝ))) := by
  rw [← (isArchSmoothAt_archDerivAt_apply_mul_archRealLiftAt hφ) d g det_of_of_symm_one,
      archRealLiftAt_of_symm_one, mul_one]

private theorem isArchSmoothAt_archDerivAt_archDerivAt_apply {w : InfinitePlace F} {hw : w.IsReal}
    {φ : AdelicGL2 (𝓞 F) F → ℂ} (hφ : IsArchSmoothAt hw φ) (d d' : ArchDir) (g : AdelicGL2 (𝓞 F) F) :
    archDerivAt hw d' (archDerivAt hw d φ) g =
      fderiv ℝ (fun e' => φ (g * archRealLiftAt hw e')) (Matrix.of.symm (1 : Matrix (Fin 2) (Fin 2) ℝ))
          (mulRightArrayCLM (archDirMatrix d)
            (mulRightArrayCLM (archDirMatrix d') (Matrix.of.symm (1 : Matrix (Fin 2) (Fin 2) ℝ)))) +
        fderiv ℝ (fderiv ℝ (fun e' => φ (g * archRealLiftAt hw e')))
          (Matrix.of.symm (1 : Matrix (Fin 2) (Fin 2) ℝ))
          (mulRightArrayCLM (archDirMatrix d') (Matrix.of.symm (1 : Matrix (Fin 2) (Fin 2) ℝ)))
          (mulRightArrayCLM (archDirMatrix d) (Matrix.of.symm (1 : Matrix (Fin 2) (Fin 2) ℝ))) := by
  have hopen := isOpen_setOf_det_ne_zero
  have h1 : ContDiffOn ℝ 1 (fderiv ℝ (fun e'' => φ (g * archRealLiftAt hw e'')))
      {e : Fin 2 → Fin 2 → ℝ | (Matrix.of e).det ≠ 0} :=
    (hφ g).fderiv_of_isOpen hopen (by exact WithTop.coe_le_coe.mpr (le_top : ((1 + 1 : ℕ) : ℕ∞) ≤ ⊤))
  have hΦ' : HasFDerivAt (fderiv ℝ (fun e'' => φ (g * archRealLiftAt hw e'')))
      (fderiv ℝ (fderiv ℝ (fun e'' => φ (g * archRealLiftAt hw e'')))
        (Matrix.of.symm (1 : Matrix (Fin 2) (Fin 2) ℝ)))
      (Matrix.of.symm (1 : Matrix (Fin 2) (Fin 2) ℝ)) :=
    ((h1.contDiffAt (hopen.mem_nhds det_of_of_symm_one)).differentiableAt (by simp)).hasFDerivAt
  have hclm := hΦ'.clm_apply (mulRightArrayCLM (archDirMatrix d)).hasFDerivAt
  have hev : (fun e' => archDerivAt hw d φ (g * archRealLiftAt hw e')) =ᶠ[nhds
      (Matrix.of.symm (1 : Matrix (Fin 2) (Fin 2) ℝ))]
      fun e' => fderiv ℝ (fun e'' => φ (g * archRealLiftAt hw e'')) e' (mulRightArrayCLM (archDirMatrix d) e') :=
    Filter.eventuallyEq_of_mem (hopen.mem_nhds det_of_of_symm_one) fun e' he' =>
      (isArchSmoothAt_archDerivAt_apply_mul_archRealLiftAt hφ) d g he'
  rw [(isArchSmoothAt_archDerivAt_apply_eq_fderiv (hφ.archDerivAt d)) d' g, (hclm.congr_of_eventuallyEq hev).fderiv]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply]

private theorem isArchSmoothAt_isSymmSndFDerivAt_of_symm_one {w : InfinitePlace F} {hw : w.IsReal}
    {φ : AdelicGL2 (𝓞 F) F → ℂ} (hφ : IsArchSmoothAt hw φ) (g : AdelicGL2 (𝓞 F) F) :
    IsSymmSndFDerivAt ℝ (fun e' => φ (g * archRealLiftAt hw e')) (Matrix.of.symm (1 : Matrix (Fin 2) (Fin 2) ℝ)) :=
  ((hφ g).contDiffAt (isOpen_setOf_det_ne_zero.mem_nhds det_of_of_symm_one)).isSymmSndFDerivAt
    (by simp only [minSmoothness_of_isRCLikeNormedField]; exact WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤))

private theorem isArchSmoothAt_archDerivAt_E_Fm_sub_archDerivAt_Fm_E {w : InfinitePlace F} {hw : w.IsReal}
    {φ : AdelicGL2 (𝓞 F) F → ℂ} (hφ : IsArchSmoothAt hw φ) :
    archDerivAt hw .E (archDerivAt hw .Fm φ) - archDerivAt hw .Fm (archDerivAt hw .E φ) = archDerivAt hw .H φ := by
  funext g
  rw [Pi.sub_apply, (isArchSmoothAt_archDerivAt_archDerivAt_apply hφ) .Fm .E g,
      (isArchSmoothAt_archDerivAt_archDerivAt_apply hφ) .E .Fm g,
    (isArchSmoothAt_archDerivAt_apply_eq_fderiv hφ) .H g,
    ((isArchSmoothAt_isSymmSndFDerivAt_of_symm_one hφ) g).eq (mulRightArrayCLM (archDirMatrix .Fm) _)
      (mulRightArrayCLM (archDirMatrix .E) _),
    add_sub_add_right_eq_sub, ← _root_.map_sub]
  congr 1
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [mulRightArrayCLM_apply, archDirMatrix, Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply,
      Matrix.of_symm_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
      Matrix.cons_val_fin_one]

private theorem isArchSmoothAt_archDerivAt_H_E_sub_archDerivAt_E_H {w : InfinitePlace F} {hw : w.IsReal}
    {φ : AdelicGL2 (𝓞 F) F → ℂ} (hφ : IsArchSmoothAt hw φ) :
    archDerivAt hw .H (archDerivAt hw .E φ) - archDerivAt hw .E (archDerivAt hw .H φ) =
      archDerivAt hw .E φ + archDerivAt hw .E φ := by
  funext g
  rw [Pi.sub_apply, Pi.add_apply, (isArchSmoothAt_archDerivAt_archDerivAt_apply hφ) .E .H g,
      (isArchSmoothAt_archDerivAt_archDerivAt_apply hφ) .H .E g,
    (isArchSmoothAt_archDerivAt_apply_eq_fderiv hφ) .E g,
    ((isArchSmoothAt_isSymmSndFDerivAt_of_symm_one hφ) g).eq (mulRightArrayCLM (archDirMatrix .E) _)
      (mulRightArrayCLM (archDirMatrix .H) _),
    add_sub_add_right_eq_sub, ← _root_.map_sub, ← _root_.map_add]
  congr 1
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [mulRightArrayCLM_apply, archDirMatrix, Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply,
      Matrix.of_symm_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
      Matrix.cons_val_fin_one]

private theorem isArchSmoothAt_archDerivAt_H_Fm_sub_archDerivAt_Fm_H {w : InfinitePlace F} {hw : w.IsReal}
    {φ : AdelicGL2 (𝓞 F) F → ℂ} (hφ : IsArchSmoothAt hw φ) :
    archDerivAt hw .H (archDerivAt hw .Fm φ) - archDerivAt hw .Fm (archDerivAt hw .H φ) =
      -(archDerivAt hw .Fm φ + archDerivAt hw .Fm φ) := by
  funext g
  rw [Pi.sub_apply, Pi.neg_apply, Pi.add_apply, (isArchSmoothAt_archDerivAt_archDerivAt_apply hφ) .Fm .H g,
    (isArchSmoothAt_archDerivAt_archDerivAt_apply hφ) .H .Fm g, (isArchSmoothAt_archDerivAt_apply_eq_fderiv hφ) .Fm g,
    ((isArchSmoothAt_isSymmSndFDerivAt_of_symm_one hφ) g).eq (mulRightArrayCLM (archDirMatrix .Fm) _)
      (mulRightArrayCLM (archDirMatrix .H) _),
    add_sub_add_right_eq_sub, ← _root_.map_sub, ← _root_.map_add, ← _root_.map_neg]
  congr 1
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [mulRightArrayCLM_apply, archDirMatrix, Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply,
      Matrix.of_symm_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
      Matrix.cons_val_fin_one]

private theorem archDerivAt_sub {w : InfinitePlace F} {hw : w.IsReal} {φ ψ : AdelicGL2 (𝓞 F) F → ℂ}
    (hφ : IsArchSmoothAt hw φ) (hψ : IsArchSmoothAt hw ψ) (d : ArchDir) :
    archDerivAt hw d (φ - ψ) = archDerivAt hw d φ - archDerivAt hw d ψ := by
  rw [sub_eq_add_neg φ ψ, ← neg_one_smul ℂ ψ, archDerivAt_add hφ (hψ.smul (-1)) d, archDerivAt_smul, neg_one_smul ℂ]
  exact (sub_eq_add_neg _ _).symm

private def archRotDerivAt {w : InfinitePlace F} (hw : w.IsReal) (φ : AdelicGL2 (𝓞 F) F → ℂ) : AdelicGL2 (𝓞 F) F → ℂ :=
  archDerivAt hw .E φ - archDerivAt hw .Fm φ

private def archRaiseAt {w : InfinitePlace F} (hw : w.IsReal) (φ : AdelicGL2 (𝓞 F) F → ℂ) : AdelicGL2 (𝓞 F) F → ℂ :=
  archDerivAt hw .H φ + Complex.I • (archDerivAt hw .E φ + archDerivAt hw .Fm φ)

private theorem isArchSmoothAt_archRaiseAt {w : InfinitePlace F} {hw : w.IsReal} {φ : AdelicGL2 (𝓞 F) F → ℂ}
    (hφ : IsArchSmoothAt hw φ) : IsArchSmoothAt hw (archRaiseAt hw φ) :=
  (hφ.archDerivAt .H).add (((hφ.archDerivAt .E).add (hφ.archDerivAt .Fm)).smul Complex.I)

private def rotationArray (θ : ℝ) : Fin 2 → Fin 2 → ℝ :=
  ![![Real.cos θ, Real.sin θ], ![-Real.sin θ, Real.cos θ]]

private theorem of_rotationArray (θ : ℝ) :
    Matrix.of (rotationArray θ) = !![Real.cos θ, Real.sin θ; -Real.sin θ, Real.cos θ] := rfl

private theorem det_of_rotationArray (θ : ℝ) : (Matrix.of (rotationArray θ)).det ≠ 0 := by
  rw [of_rotationArray, Matrix.det_fin_two_of]
  nlinarith [Real.cos_sq_add_sin_sq θ]

private theorem rotationArray_zero : rotationArray 0 = Matrix.of.symm (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [rotationArray, Matrix.one_fin_two]

private theorem hasDerivAt_rotationArray :
    HasDerivAt rotationArray (![![0, 1], ![-1, 0]] : Fin 2 → Fin 2 → ℝ) 0 := by
  rw [hasDerivAt_pi]
  intro i
  rw [hasDerivAt_pi]
  intro j
  fin_cases i <;> fin_cases j <;> simp only [rotationArray] <;>
    first
      | simpa using Real.hasDerivAt_cos 0
      | simpa using Real.hasDerivAt_sin 0
      | simpa using (Real.hasDerivAt_sin 0).fun_neg
      | simpa using (Real.hasDerivAt_sin 0).neg

private theorem archRealLiftAt_rotationArray {w : InfinitePlace F} (hw : w.IsReal) (θ : ℝ) :
    archRealLiftAt hw (rotationArray θ) = archRealGLAt hw (GL2Real.rotation θ) := by
  rw [archRealLiftAt_of_det_ne_zero hw (det_of_rotationArray θ)]
  rfl

private theorem rotation_mem_rowIsometrySubgroup₀ (θ : ℝ) : GL2Real.rotation θ ∈ rowIsometrySubgroup₀ ℝ := by
  rw [mem_rowIsometrySubgroup₀_iff]
  have hc : ((GL2Real.rotation θ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
      !![Real.cos θ, Real.sin θ; -Real.sin θ, Real.cos θ] := by
    simp [GL2Real.rotation, Matrix.GeneralLinearGroup.mkOfDetNeZero]
  have h1 : Real.cos θ * Real.cos θ - Real.sin θ * -Real.sin θ = 1 := by
    linear_combination Real.cos_sq_add_sin_sq θ
  refine ⟨?_, ?_, ?_⟩
  · rw [hc, Matrix.det_fin_two_of]
    exact h1
  · rw [hc, Matrix.det_fin_two_of, h1, norm_one]
  · intro x y
    rw [hc]
    simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one, Real.norm_eq_abs, sq_abs]
    linear_combination (x ^ 2 + y ^ 2) * Real.cos_sq_add_sin_sq θ

omit [NumberField F] in
private theorem norm_ringEquivRealOfIsReal_symm {w : InfinitePlace F} (hw : w.IsReal) (x : ℝ) :
    ‖(ringEquivRealOfIsReal hw).symm x‖ = ‖x‖ := by
  rw [← norm_ringEquivRealOfIsReal hw ((ringEquivRealOfIsReal hw).symm x), RingEquiv.apply_symm_apply]

private def rotationAt {w : InfinitePlace F} (hw : w.IsReal) (θ : ℝ) : rowIsometrySubgroup₀ w.Completion :=
  rowIsometrySubgroup₀Map (ringEquivRealOfIsReal hw).symm (norm_ringEquivRealOfIsReal_symm hw)
    ⟨GL2Real.rotation θ, rotation_mem_rowIsometrySubgroup₀ θ⟩

private theorem archRealGLAt_rotation {w : InfinitePlace F} (hw : w.IsReal) (θ : ℝ) :
    archRealGLAt hw (GL2Real.rotation θ) =
      adelicArchGLInclAt F w ((rotationAt hw θ : rowIsometrySubgroup₀ w.Completion) : GL (Fin 2) w.Completion) := rfl

omit [NumberField F] in

private theorem archWeightCharAt_one_rotationAt {w : InfinitePlace F} (hw : w.IsReal) (θ : ℝ) :
    ((archWeightCharAt hw 1 (rotationAt hw θ) : ℂˣ) : ℂ) = ⟨Real.cos θ, Real.sin θ⟩ := by
  have hentry : ∀ i j : Fin 2,
      ((glEquivOfRingEquiv (ringEquivRealOfIsReal hw)
          (glEquivOfRingEquiv (ringEquivRealOfIsReal hw).symm (GL2Real.rotation θ)) : GL (Fin 2) ℝ) :
            Matrix (Fin 2) (Fin 2) ℝ) i j =
        ((GL2Real.rotation θ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) i j := by
    intro i j
    rw [glEquivOfRingEquiv_apply_entry, glEquivOfRingEquiv_apply_entry, RingEquiv.apply_symm_apply]
  show ((archWeightOneℝ (rowIsometrySubgroup₀Map (ringEquivRealOfIsReal hw) (norm_ringEquivRealOfIsReal hw)
      (rotationAt hw θ)) ^ (1 : ℤ) : ℂˣ) : ℂ) = _
  rw [zpow_one]
  show firstRowℂ _ = _
  unfold firstRowℂ
  refine Complex.ext ?_ ?_
  · exact hentry 0 0
  · exact hentry 0 1

private theorem isArchSmoothAt_archDerivAt_Fm_E {w : InfinitePlace F} {hw : w.IsReal} {φ : AdelicGL2 (𝓞 F) F → ℂ}
    (hφ : IsArchSmoothAt hw φ) :
    archDerivAt hw .Fm (archDerivAt hw .E φ) = archDerivAt hw .E (archDerivAt hw .Fm φ) - archDerivAt hw .H φ := by
  rw [← (isArchSmoothAt_archDerivAt_E_Fm_sub_archDerivAt_Fm_E hφ)]
  abel

private theorem isArchSmoothAt_archDerivAt_E_H {w : InfinitePlace F} {hw : w.IsReal} {φ : AdelicGL2 (𝓞 F) F → ℂ}
    (hφ : IsArchSmoothAt hw φ) :
    archDerivAt hw .E (archDerivAt hw .H φ) =
      archDerivAt hw .H (archDerivAt hw .E φ) - (archDerivAt hw .E φ + archDerivAt hw .E φ) := by
  rw [← (isArchSmoothAt_archDerivAt_H_E_sub_archDerivAt_E_H hφ)]
  abel

private theorem isArchSmoothAt_archDerivAt_Fm_H {w : InfinitePlace F} {hw : w.IsReal} {φ : AdelicGL2 (𝓞 F) F → ℂ}
    (hφ : IsArchSmoothAt hw φ) :
    archDerivAt hw .Fm (archDerivAt hw .H φ) =
      archDerivAt hw .H (archDerivAt hw .Fm φ) + (archDerivAt hw .Fm φ + archDerivAt hw .Fm φ) := by
  rw [sub_eq_iff_eq_add.mp (isArchSmoothAt_archDerivAt_H_Fm_sub_archDerivAt_Fm_H hφ)]
  abel

private theorem hasDerivAt_rotationArray' (θ : ℝ) :
    HasDerivAt rotationArray
      (![![-Real.sin θ, Real.cos θ], ![-Real.cos θ, -Real.sin θ]] : Fin 2 → Fin 2 → ℝ) θ := by
  rw [hasDerivAt_pi]
  intro i
  rw [hasDerivAt_pi]
  intro j
  fin_cases i <;> fin_cases j <;> simp only [rotationArray] <;>
    first
      | simpa using Real.hasDerivAt_cos θ
      | simpa using Real.hasDerivAt_sin θ
      | simpa using (Real.hasDerivAt_sin θ).fun_neg
      | simpa using (Real.hasDerivAt_sin θ).neg

private theorem mulRightArrayCLM_E_sub_Fm_rotationArray (θ : ℝ) :
    mulRightArrayCLM (archDirMatrix .E) (rotationArray θ) - mulRightArrayCLM (archDirMatrix .Fm) (rotationArray θ) =
      (![![-Real.sin θ, Real.cos θ], ![-Real.cos θ, -Real.sin θ]] : Fin 2 → Fin 2 → ℝ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [mulRightArrayCLM_apply, archDirMatrix, rotationArray, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.of_apply, Matrix.of_symm_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one]

private theorem rotation_coe (θ : ℝ) :
    ((GL2Real.rotation θ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
      !![Real.cos θ, Real.sin θ; -Real.sin θ, Real.cos θ] := by
  simp [GL2Real.rotation, Matrix.GeneralLinearGroup.mkOfDetNeZero]

private theorem exists_rotation_eq_of_mem {m : GL (Fin 2) ℝ} (hm : m ∈ rowIsometrySubgroup₀ ℝ) :
    ∃ θ : ℝ, GL2Real.rotation θ = m := by
  have hk := entries_of_mem_rowIsometrySubgroup₀ hm
  dsimp only at hk
  obtain ⟨h10, h11, hab⟩ := hk
  set a : ℝ := (m : Matrix (Fin 2) (Fin 2) ℝ) 0 0 with ha
  set b : ℝ := (m : Matrix (Fin 2) (Fin 2) ℝ) 0 1 with hb
  set z : ℂ := ⟨a, b⟩ with hz
  have hnorm : ‖z‖ = 1 := by
    have h2 : ‖z‖ ^ 2 = 1 := by
      rw [← Complex.normSq_eq_norm_sq, hz, Complex.normSq_mk]
      nlinarith [hab]
    nlinarith [norm_nonneg z, h2]
  have hz0 : z ≠ 0 := by
    intro h
    rw [h, norm_zero] at hnorm
    exact zero_ne_one hnorm
  have hcos : Real.cos (Complex.arg z) = a := by
    rw [Complex.cos_arg hz0, hnorm, div_one]
  have hsin : Real.sin (Complex.arg z) = b := by
    rw [Complex.sin_arg, hnorm, div_one]
  refine ⟨Complex.arg z, Units.ext ?_⟩
  rw [rotation_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [hcos, hsin, h10, h11, ← ha, ← hb]

omit [NumberField F] in

private theorem exists_rotationAt_eq {w : InfinitePlace F} (hw : w.IsReal) (k : rowIsometrySubgroup₀ w.Completion) :
    ∃ θ : ℝ, rotationAt hw θ = k := by
  obtain ⟨θ, hθ⟩ := exists_rotation_eq_of_mem
    (map_mem_rowIsometrySubgroup₀_of_normPreserving (ringEquivRealOfIsReal hw) (norm_ringEquivRealOfIsReal hw)
      (k : GL (Fin 2) w.Completion) k.2)
  refine ⟨θ, Subtype.ext ?_⟩
  show glEquivOfRingEquiv (ringEquivRealOfIsReal hw).symm (GL2Real.rotation θ) = (k : GL (Fin 2) w.Completion)
  rw [hθ]
  refine Units.ext ?_
  ext i j
  rw [glEquivOfRingEquiv_apply_entry, glEquivOfRingEquiv_apply_entry, RingEquiv.symm_apply_apply]

section Eigenvectors
variable {w : InfinitePlace F} {hw : w.IsReal} {φ : AdelicGL2 (𝓞 F) F → ℂ}
private theorem hasArchCharacterAt₀_smul {χ : rowIsometrySubgroup₀ w.Completion →* ℂˣ} {φ : AdelicGL2 (𝓞 F) F →
    ℂ} (c : ℂ)
    (h : HasArchCharacterAt₀ F w χ φ) : HasArchCharacterAt₀ F w χ (c • φ) := by
  intro k g
  rw [Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul, h k g]
  ring

end Eigenvectors
section CoefficientIdentities
open MeasureTheory
private theorem whittakerCoefficient_add (pins : CarrierPins F) (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ)
    {φ₁ φ₂ : AdelicGL2 (𝓞 F) F → ℂ} {α : F} {g : AdelicGL2 (𝓞 F) F}
    (h₁ : WhittakerCoefficientIntegrable F pins ψ φ₁ α g) (h₂ : WhittakerCoefficientIntegrable F pins ψ φ₂ α g) :
    whittakerCoefficient F pins ψ (φ₁ + φ₂) α g =
      whittakerCoefficient F pins ψ φ₁ α g + whittakerCoefficient F pins ψ φ₂ α g := by
  unfold WhittakerCoefficientIntegrable at h₁ h₂
  unfold whittakerCoefficient
  simp only [Pi.add_apply, add_mul]
  exact integral_add h₁ h₂

private theorem whittakerCoefficient_sub (pins : CarrierPins F) (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ)
    {φ₁ φ₂ : AdelicGL2 (𝓞 F) F → ℂ} {α : F} {g : AdelicGL2 (𝓞 F) F}
    (h₁ : WhittakerCoefficientIntegrable F pins ψ φ₁ α g) (h₂ : WhittakerCoefficientIntegrable F pins ψ φ₂ α g) :
    whittakerCoefficient F pins ψ (φ₁ - φ₂) α g =
      whittakerCoefficient F pins ψ φ₁ α g - whittakerCoefficient F pins ψ φ₂ α g := by
  unfold WhittakerCoefficientIntegrable at h₁ h₂
  unfold whittakerCoefficient
  simp only [Pi.sub_apply, sub_mul]
  exact integral_sub h₁ h₂

end CoefficientIdentities
end
end ArchimedeanDerivations
section IsotypicReproduction
open NumberField IsDedekindDomain NumberField.AdelicLevel
noncomputable section
variable {F : Type} [Field F] [NumberField F]

private def realizationOfIsIsotypicCuspFormAt {pins : CarrierPins F} {ξ : pins.Z →* ℂˣ} {S : Finset
    (HeightOneSpectrum (𝓞 F))}
    {Φ : HeckeEigensystem F ℂ} {φ : AdelicGL2 (𝓞 F) F → ℂ} (hφ : IsIsotypicCuspFormAt F pins ξ Φ.level S Φ φ)
    (hne : φ ≠ 0) : SmoothCuspRealizationAt F pins Φ.toRawCentral where
  toFun := φ
  exists_ne_zero := by
    obtain ⟨g, hg⟩ := Function.ne_iff.mp hne
    exact ⟨g, hg⟩
  centralChar := ξ
  smoothCusp := hφ.smoothCusp
  level_invariant := hφ.level_invariant
  exceptionalSet := S
  hecke_eigen := hφ.hecke_eigen
  central_eigen := hφ.central_eigen

@[scoped simp] private theorem realizationOfIsIsotypicCuspFormAt_toFun {pins : CarrierPins F} {ξ : pins.Z →* ℂˣ}
    {S : Finset (HeightOneSpectrum (𝓞 F))} {Φ : HeckeEigensystem F ℂ} {φ : AdelicGL2 (𝓞 F) F → ℂ}
    (hφ : IsIsotypicCuspFormAt F pins ξ Φ.level S Φ φ) (hne : φ ≠ 0) :
    (realizationOfIsIsotypicCuspFormAt hφ hne).toFun = φ := rfl

@[scoped simp] private theorem realizationOfIsIsotypicCuspFormAt_centralChar {pins : CarrierPins F} {ξ : pins.Z →* ℂˣ}
    {S : Finset (HeightOneSpectrum (𝓞 F))} {Φ : HeckeEigensystem F ℂ} {φ : AdelicGL2 (𝓞 F) F → ℂ}
    (hφ : IsIsotypicCuspFormAt F pins ξ Φ.level S Φ φ) (hne : φ ≠ 0) :
    (realizationOfIsIsotypicCuspFormAt hφ hne).centralChar = ξ := rfl

@[scoped simp] private theorem realizationOfIsIsotypicCuspFormAt_exceptionalSet {pins : CarrierPins F} {ξ : pins.Z →* ℂˣ}
    {S : Finset (HeightOneSpectrum (𝓞 F))} {Φ : HeckeEigensystem F ℂ} {φ : AdelicGL2 (𝓞 F) F → ℂ}
    (hφ : IsIsotypicCuspFormAt F pins ξ Φ.level S Φ φ) (hne : φ ≠ 0) :
    (realizationOfIsIsotypicCuspFormAt hφ hne).exceptionalSet = S := rfl

open scoped Classical in
private theorem isArchTestFactor_add {fa₁ fa₂ : GL (Fin 2) (InfiniteAdeleRing F) → ℂ} (h₁ : IsArchTestFactor F fa₁)
    (h₂ : IsArchTestFactor F fa₂) : IsArchTestFactor F (fa₁ + fa₂) := by
  obtain ⟨⟨Φ₁, hΦ₁, hfa₁⟩, hc₁⟩ := h₁
  obtain ⟨⟨Φ₂, hΦ₂, hfa₂⟩, hc₂⟩ := h₂
  refine ⟨⟨Φ₁ + Φ₂, hΦ₁.add hΦ₂, fun g => ?_⟩, hc₁.add hc₂⟩
  simp only [Pi.add_apply, hfa₁ g, hfa₂ g]

open scoped Classical in
private theorem isArchTestFactor_smul {fa : GL (Fin 2) (InfiniteAdeleRing F) → ℂ} (h : IsArchTestFactor F fa) (c : ℂ) :
    IsArchTestFactor F (c • fa) := by
  obtain ⟨⟨Φ, hΦ, hfa⟩, hc⟩ := h
  refine ⟨⟨c • Φ, hΦ.const_smul c, fun g => ?_⟩, hc.mono fun g hg => ?_⟩
  · simp only [Pi.smul_apply, hfa g]
  · intro h0
    exact hg (by simp only [Pi.smul_apply, h0, smul_zero])

private def tensorTestFn (fa : GL (Fin 2) (InfiniteAdeleRing F) → ℂ) (ff : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F) → ℂ) :
    GL (Fin 2) (AdeleRing (𝓞 F) F) → ℂ :=
  fun g => fa (glArch (𝓞 F) F g) * ff (glFin (𝓞 F) F g)

private theorem tensorTestFn_apply (fa : GL (Fin 2) (InfiniteAdeleRing F) → ℂ) (ff : GL (Fin 2) (FiniteAdeleRing
    (𝓞 F) F) → ℂ)
    (g : GL (Fin 2) (AdeleRing (𝓞 F) F)) : tensorTestFn fa ff g = fa (glArch (𝓞 F) F g) * ff (glFin (𝓞 F) F g) := rfl

private theorem isFactorizableTestFn_tensorTestFn {fa : GL (Fin 2) (InfiniteAdeleRing F) → ℂ}
    {ff : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F) → ℂ} (hfa : IsArchTestFactor F fa) (hff : IsFinTestFactor F ff) :
    IsFactorizableTestFn F (tensorTestFn fa ff) :=
  ⟨fa, ff, hfa, hff, fun _ => rfl⟩

private theorem isFactorizableTestFn_exists_eq_tensorTestFn {f : GL (Fin 2) (AdeleRing (𝓞 F) F) → ℂ}
    (hf : IsFactorizableTestFn F f) :
    ∃ (fa : GL (Fin 2) (InfiniteAdeleRing F) → ℂ) (ff : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F) → ℂ),
      IsArchTestFactor F fa ∧ IsFinTestFactor F ff ∧ f = tensorTestFn fa ff := by
  obtain ⟨fa, ff, hfa, hff, hf⟩ := hf
  exact ⟨fa, ff, hfa, hff, funext hf⟩

private theorem tensorTestFn_support_of_forall {fa : GL (Fin 2) (InfiniteAdeleRing F) → ℂ}
    {ff : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F) → ℂ} {G : Subgroup (GL (Fin 2) (AdeleRing (𝓞 F) F))}
    (hff : ∀ x : GL (Fin 2) (AdeleRing (𝓞 F) F), ff (glFin (𝓞 F) F x) ≠ 0 →
      ∃ a k : GL (Fin 2) (AdeleRing (𝓞 F) F), glFin (𝓞 F) F a = 1 ∧ k ∈ G ∧ x = a * k) :
    ∀ x : GL (Fin 2) (AdeleRing (𝓞 F) F), tensorTestFn fa ff x ≠ 0 →
      ∃ a k : GL (Fin 2) (AdeleRing (𝓞 F) F), glFin (𝓞 F) F a = 1 ∧ k ∈ G ∧ x = a * k :=
  fun x hx => hff x (right_ne_zero_of_mul hx)

private theorem tensorTestFn_add (fa₁ fa₂ : GL (Fin 2) (InfiniteAdeleRing F) → ℂ)
    (ff : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F) → ℂ) :
    tensorTestFn (fa₁ + fa₂) ff = tensorTestFn fa₁ ff + tensorTestFn fa₂ ff := by
  funext g
  simp only [Pi.add_apply, tensorTestFn_apply, add_mul]

private theorem tensorTestFn_smul (c : ℂ) (fa : GL (Fin 2) (InfiniteAdeleRing F) → ℂ)
    (ff : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F) → ℂ) : tensorTestFn (c • fa) ff = c • tensorTestFn fa ff := by
  funext g
  simp only [tensorTestFn_apply, Pi.smul_apply, smul_eq_mul, mul_assoc]

private theorem tensorTestFn_finset_sum_smul {ι : Type} (s : Finset ι) (c : ι → ℂ)
    (fa : ι → GL (Fin 2) (InfiniteAdeleRing F) → ℂ) (ff : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F) → ℂ) :
    tensorTestFn (∑ i ∈ s, c i • fa i) ff = ∑ i ∈ s, c i • tensorTestFn (fa i) ff := by
  funext g
  simp only [tensorTestFn_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul, mul_assoc]

private theorem isArchTestFactor_finset_sum {ι : Type} (s : Finset ι) (c : ι → ℂ)
    {fa : ι → GL (Fin 2) (InfiniteAdeleRing F) → ℂ} (hfa : ∀ i, IsArchTestFactor F (fa i)) :
    IsArchTestFactor F (∑ i ∈ s, c i • fa i) :=
  Finset.sum_induction (fun i => c i • fa i) (IsArchTestFactor F) (fun _ _ ha hb => (isArchTestFactor_add ha) hb)
    (isArchTestFactor_zero F) fun i _ => (isArchTestFactor_smul (hfa i)) (c i)

private theorem rightConv_const_mul_right (φ : AdelicGL2 (𝓞 F) F → ℂ) (c : ℂ) (f : AdelicGL2 (𝓞 F) F → ℂ) :
    rightConv F φ (fun y => c * f y) = c • rightConv F φ f := by
  funext g
  simp only [rightConv_apply, Pi.smul_apply, smul_eq_mul, mul_left_comm _ c, MeasureTheory.integral_const_mul]

private theorem rightConv_smul_right (φ : AdelicGL2 (𝓞 F) F → ℂ) (c : ℂ) (f : AdelicGL2 (𝓞 F) F → ℂ) :
    rightConv F φ (c • f) = c • rightConv F φ f :=
  rightConv_const_mul_right φ c f

private theorem rightConv_add_right {φ : AdelicGL2 (𝓞 F) F → ℂ} (hφ : Continuous φ) {f₁ f₂ : AdelicGL2 (𝓞 F) F → ℂ}
    (h₁ : Continuous f₁) (h₁c : HasCompactSupport f₁) (h₂ : Continuous f₂) (h₂c : HasCompactSupport f₂) :
    rightConv F φ (f₁ + f₂) = rightConv F φ f₁ + rightConv F φ f₂ := by
  letI : MeasurableSpace (AdelicGL2 (𝓞 F) F) := AdelicHaar.glBorel (Fin 2) (𝓞 F) F
  haveI : BorelSpace (AdelicGL2 (𝓞 F) F) := AdelicHaar.borelSpace_glBorel (Fin 2) (𝓞 F) F
  haveI : (AdelicHaar.adelicGLHaar (Fin 2) (𝓞 F) F).IsHaarMeasure :=
    AdelicHaar.isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 F) F
  have hint : ∀ {f : AdelicGL2 (𝓞 F) F → ℂ}, Continuous f → HasCompactSupport f → ∀ g : AdelicGL2 (𝓞 F) F,
      MeasureTheory.Integrable (fun x => φ (g * x) * f x) (AdelicHaar.adelicGLHaar (Fin 2) (𝓞 F) F) := by
    intro f hf hfc g
    exact ((hφ.comp (continuous_const.mul continuous_id)).mul hf).integrable_of_hasCompactSupport hfc.mul_left
  funext g
  simp only [rightConv_apply, Pi.add_apply, mul_add]
  exact MeasureTheory.integral_add (hint h₁ h₁c g) (hint h₂ h₂c g)

private theorem rightConv_zero_right' (φ : AdelicGL2 (𝓞 F) F → ℂ) : rightConv F φ 0 = 0 := by
  funext g
  simp [rightConv_apply]

private theorem rightConv_finset_sum_right {φ : AdelicGL2 (𝓞 F) F → ℂ} (hφ : Continuous φ) {ι : Type} (s : Finset ι)
    {h : ι → AdelicGL2 (𝓞 F) F → ℂ} (hh : ∀ i ∈ s, Continuous (h i) ∧ HasCompactSupport (h i)) :
    rightConv F φ (∑ i ∈ s, h i) = ∑ i ∈ s, rightConv F φ (h i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty, rightConv_zero_right']
  | insert a s has ih =>
    have hs : Continuous (∑ i ∈ s, h i) ∧ HasCompactSupport (∑ i ∈ s, h i) :=
      Finset.sum_induction h (fun f => Continuous f ∧ HasCompactSupport f)
        (fun _ _ ha hb => ⟨ha.1.add hb.1, ha.2.add hb.2⟩) ⟨continuous_zero, HasCompactSupport.zero⟩
        fun i hi => hh i (Finset.mem_insert_of_mem hi)
    have ha := hh a (Finset.mem_insert_self a s)
    rw [Finset.sum_insert has, Finset.sum_insert has, rightConv_add_right hφ ha.1 ha.2 hs.1 hs.2,
      ih fun i hi => hh i (Finset.mem_insert_of_mem hi)]

private theorem funext_comp_inv_mul_of_forall_apply_mul_inv {β : AdelicGL2 (𝓞 F) F → ℂ} {cst : ℂ} (t : AdelicGL2
    (𝓞 F) F)
    (ht : ∀ g : AdelicGL2 (𝓞 F) F, β (g * t)⁻¹ = cst * β g⁻¹) : (fun y => β (t⁻¹ * y)) = fun y => cst * β y := by
  funext y
  have := ht y⁻¹
  rwa [_root_.mul_inv_rev, _root_.inv_inv] at this

private theorem hasArchCharacterAt₀_rightConv_of_isArchBiFinite_ofChar {φ : AdelicGL2 (𝓞 F) F → ℂ}
    {χ : ∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion →* ℂˣ} {β : AdelicGL2 (𝓞 F) F → ℂ}
    (hβ : IsArchBiFinite F (ArchTypeFamily.ofChar F χ) β) (w : InfinitePlace F) :
    HasArchCharacterAt₀ F w (χ w) (rightConv F φ β) := by
  have hinv : HasArchCharacterAt₀ F w (χ w) fun x => β x⁻¹ :=
    (mem_archCutSubmodule_ofChar_iff (F := F) χ _).mp hβ.1 w
  intro k g
  rw [rightConv_apply_mul_eq_rightConv_comp_inv_mul_apply, funext_comp_inv_mul_of_forall_apply_mul_inv _ (hinv k),
    rightConv_const_mul_right, Pi.smul_apply, smul_eq_mul]

private theorem mem_archCutSubmodule_rightConv_of_isArchBiFinite_ofChar (φ : AdelicGL2 (𝓞 F) F → ℂ)
    {χ : ∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion →* ℂˣ} {β : AdelicGL2 (𝓞 F) F → ℂ}
    (hβ : IsArchBiFinite F (ArchTypeFamily.ofChar F χ) β) :
    rightConv F φ β ∈ archCutSubmodule F (ArchTypeFamily.ofChar F χ) :=
  (mem_archCutSubmodule_ofChar_iff (F := F) χ _).mpr fun w =>
    hasArchCharacterAt₀_rightConv_of_isArchBiFinite_ofChar hβ w

private theorem exists_finsupp_sum_eq_of_tendsto_of_finiteDimensional {M : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ)}
    (hM : FiniteDimensional ℂ M) (a : ℕ → AdelicGL2 (𝓞 F) F → ℂ) (ha : ∀ n, a n ∈ M) {f : AdelicGL2 (𝓞 F) F → ℂ}
    (hf : ∀ g, Filter.Tendsto (fun n => a n g) Filter.atTop (nhds (f g))) :
    ∃ c : ℕ →₀ ℂ, (c.sum fun n cn => cn • a n) = f := by
  haveI := hM
  have hle : Submodule.span ℂ (Set.range a) ≤ M := Submodule.span_le.mpr (Set.range_subset_iff.mpr ha)
  haveI : FiniteDimensional ℂ (Submodule.span ℂ (Set.range a)) := Submodule.finiteDimensional_of_le hle
  have hclosed : IsClosed ((Submodule.span ℂ (Set.range a) : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ)) :
      Set (AdelicGL2 (𝓞 F) F → ℂ)) :=
    Submodule.closed_of_finiteDimensional _
  have hmem : f ∈ Submodule.span ℂ (Set.range a) :=
    hclosed.mem_of_tendsto (tendsto_pi_nhds.mpr hf)
      (Filter.Eventually.of_forall fun n => Submodule.subset_span ⟨n, rfl⟩)
  exact Finsupp.mem_span_range_iff_exists_finsupp.mp hmem

section IsotypyOfConvolutions
open IsDedekindDomain NumberField MeasureTheory Matrix
open NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open NumberField.InfinitePlace.Completion
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open LanglandsTunnell LanglandsTunnell.Converse NumberField.TateGlobal

private theorem isIsotypicCuspFormAt_rightConv_of_isIsotypicCuspFormAt
    (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 ℚ) ℚ)) (hd : d₁ < d₂)
    (hcov : CoversModCentre ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂))
    (Φ : HeckeEigensystem ℚ ℂ)
    {ξ : (productionPinsOf ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂)
        (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ)).Z →* ℂˣ}
    {S : Finset (HeightOneSpectrum (𝓞 ℚ))} {φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ}
    (hφ : IsIsotypicCuspFormAt ℚ
      (productionPinsOf ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂)
        (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ))
      ξ Φ.level S Φ φ)
    (hne : φ ≠ 0) (f : AdelicGL2 (𝓞 ℚ) ℚ → ℂ) (hf : IsFactorizableTestFn ℚ f)
    (hfs : ∀ x : AdelicGL2 (𝓞 ℚ) ℚ, f x ≠ 0 → ∃ a k : AdelicGL2 (𝓞 ℚ) ℚ,
      glFin (𝓞 ℚ) ℚ a = 1 ∧ k ∈ levelOne (𝓞 ℚ) ℚ Φ.level ⊓ finiteAdelicGL2Subgroup ℚ ∧ x = a * k) :
    IsIsotypicCuspFormAt ℚ
      (productionPinsOf ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂)
        (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ))
      ξ Φ.level S Φ (rightConv ℚ φ f) :=
  isIsotypicCuspFormAt_rightConv_of_isFactorizableTestFn_of_support_subset_of_coversModCentre c u d₁ d₂ T hd hcov Φ
    (realizationOfIsIsotypicCuspFormAt hφ hne) hφ.continuous f hf hfs

private theorem ringHom_eq_id_ringOfIntegers_rat (e : 𝓞 ℚ →+* 𝓞 ℚ) : e = RingHom.id (𝓞 ℚ) := by
  have h : e.comp (Rat.ringOfIntegersEquiv.symm : ℤ →+* 𝓞 ℚ) = (Rat.ringOfIntegersEquiv.symm : ℤ →+* 𝓞 ℚ) :=
    Subsingleton.elim _ _
  refine RingHom.ext fun x => ?_
  have h2 : e (Rat.ringOfIntegersEquiv.symm (Rat.ringOfIntegersEquiv x))
      = Rat.ringOfIntegersEquiv.symm (Rat.ringOfIntegersEquiv x) :=
    RingHom.congr_fun h (Rat.ringOfIntegersEquiv x)
  rw [RingEquiv.symm_apply_apply] at h2
  exact h2

private theorem map_algebraMap_ringOfIntegers_rat (inst : Algebra (𝓞 ℚ) (𝓞 ℚ)) (N : Ideal (𝓞 ℚ)) :
    Ideal.map (@algebraMap (𝓞 ℚ) (𝓞 ℚ) _ _ inst) N = N := by
  rw [ringHom_eq_id_ringOfIntegers_rat (@algebraMap (𝓞 ℚ) (𝓞 ℚ) _ _ inst), Ideal.map_id]

private theorem exists_tensorTestFn_rightConv_eq_self_of_isIsotypicCuspFormAt
    (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 ℚ) ℚ)) (hd : d₁ < d₂)
    (hcov : CoversModCentre ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂))
    (Φ : HeckeEigensystem ℚ ℂ) (χ : ∀ w : InfinitePlace ℚ, rowIsometrySubgroup₀ w.Completion →* ℂˣ)
    {ξ : (productionPinsOf ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂)
        (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ)).Z →* ℂˣ}
    {S : Finset (HeightOneSpectrum (𝓞 ℚ))} {φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ}
    (hφ : IsIsotypicCuspFormAt ℚ
      (productionPinsOf ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂)
        (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ))
      ξ Φ.level S Φ φ)
    (hne : φ ≠ 0) (harch : φ ∈ archCutSubmodule ℚ (ArchTypeFamily.ofChar ℚ χ)) :
    ∃ (fa : GL (Fin 2) (InfiniteAdeleRing ℚ) → ℂ) (ff : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ) → ℂ),
      IsArchTestFactor ℚ fa ∧ IsFinTestFactor ℚ ff ∧
      (∀ x : AdelicGL2 (𝓞 ℚ) ℚ, ff (glFin (𝓞 ℚ) ℚ x) ≠ 0 → ∃ a k : AdelicGL2 (𝓞 ℚ) ℚ,
        glFin (𝓞 ℚ) ℚ a = 1 ∧ k ∈ levelOne (𝓞 ℚ) ℚ Φ.level ⊓ finiteAdelicGL2Subgroup ℚ ∧ x = a * k) ∧
      rightConv ℚ φ (tensorTestFn fa ff) = φ := by
  classical

  have hlevel : Φ.level ≠ 0 := by simpa using Φ.level_ne_bot
  obtain ⟨S', hNS⟩ :
      ∃ S' : Finset (HeightOneSpectrum (𝓞 ℚ)), ∀ p : HeightOneSpectrum (𝓞 ℚ), p.asIdeal ∣ Φ.level → p ∈ S' :=
    ⟨(Ideal.finite_factors hlevel).toFinset, fun _ hp => (Set.Finite.mem_toFinset _).mpr hp⟩

  obtain ⟨ff, fa, hff, hffs, hfa, htype, htend⟩ :=
    exists_finTestFactor_isUnitFactorizableAboveOfType_tendsto_rightConv_of_mem_archCutSubmodule ℚ ℚ Φ.level S' hNS
      (ArchTypeFamily.ofChar ℚ χ) φ hφ.continuous
      (by
        intro g k hk
        rw [map_algebraMap_ringOfIntegers_rat] at hk
        exact hφ.level_invariant g k hk)
      harch
  rw [map_algebraMap_ringOfIntegers_rat] at hffs

  have hmemM : ∀ n, rightConv ℚ φ (tensorTestFn (fa n) ff) ∈
      isotypicCuspSubmodule ℚ
        (productionPinsOf ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂)
          (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ))
        ξ Φ.level S Φ ⊓ archCutSubmodule ℚ (ArchTypeFamily.ofChar ℚ χ) := by
    intro n
    refine Submodule.mem_inf.mpr ⟨?_, ?_⟩
    · exact (isIsotypicCuspFormAt_rightConv_of_isIsotypicCuspFormAt c u d₁ d₂ T hd hcov Φ hφ hne _
        (isFactorizableTestFn_tensorTestFn (hfa n) hff)
        (tensorTestFn_support_of_forall hffs)).mem_isotypicCuspSubmodule
    · exact mem_archCutSubmodule_rightConv_of_isArchBiFinite_ofChar φ (htype n).isArchBiFinite
  have hfin := finiteDimensional_isotypicCuspSubmodule_inf_archCutSubmodule ℚ c u d₁ d₂ T hd hcov ξ Φ.level
    Φ.level_ne_bot S (ArchTypeFamily.ofChar ℚ χ) Φ
  obtain ⟨cf, hcf⟩ := exists_finsupp_sum_eq_of_tendsto_of_finiteDimensional hfin
    (fun n => rightConv ℚ φ (tensorTestFn (fa n) ff)) hmemM htend

  refine ⟨∑ n ∈ cf.support, cf n • fa n, ff, isArchTestFactor_finset_sum _ _ hfa, hff, hffs, ?_⟩
  have hterm : ∀ n ∈ cf.support, Continuous (cf n • tensorTestFn (fa n) ff) ∧
      HasCompactSupport (cf n • tensorTestFn (fa n) ff) := by
    intro n _
    rw [← tensorTestFn_smul]
    exact continuous_and_hasCompactSupport_of_isFactorizableTestFn ℚ _
      (isFactorizableTestFn_tensorTestFn ((isArchTestFactor_smul (hfa n)) (cf n)) hff)
  rw [tensorTestFn_finset_sum_smul, rightConv_finset_sum_right hφ.continuous _ hterm]
  simp only [rightConv_smul_right]
  simpa only [Finsupp.sum] using hcf

private theorem exists_isFactorizableTestFn_rightConv_eq_self_of_isIsotypicCuspFormAt
    (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 ℚ) ℚ)) (hd : d₁ < d₂)
    (hcov : CoversModCentre ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂))
    (Φ : HeckeEigensystem ℚ ℂ) (χ : ∀ w : InfinitePlace ℚ, rowIsometrySubgroup₀ w.Completion →* ℂˣ)
    {ξ : (productionPinsOf ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂)
        (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ)).Z →* ℂˣ}
    {S : Finset (HeightOneSpectrum (𝓞 ℚ))} {φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ}
    (hφ : IsIsotypicCuspFormAt ℚ
      (productionPinsOf ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂)
        (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ))
      ξ Φ.level S Φ φ)
    (hne : φ ≠ 0) (harch : φ ∈ archCutSubmodule ℚ (ArchTypeFamily.ofChar ℚ χ)) :
    ∃ γ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ, IsFactorizableTestFn ℚ γ ∧
      (∀ x : AdelicGL2 (𝓞 ℚ) ℚ, γ x ≠ 0 → ∃ a k : AdelicGL2 (𝓞 ℚ) ℚ,
        glFin (𝓞 ℚ) ℚ a = 1 ∧ k ∈ levelOne (𝓞 ℚ) ℚ Φ.level ⊓ finiteAdelicGL2Subgroup ℚ ∧ x = a * k) ∧
      rightConv ℚ φ γ = φ := by
  obtain ⟨fa, ff, hfa, hff, hffs, hrep⟩ :=
    exists_tensorTestFn_rightConv_eq_self_of_isIsotypicCuspFormAt c u d₁ d₂ T hd hcov Φ χ hφ hne harch
  exact ⟨tensorTestFn fa ff, isFactorizableTestFn_tensorTestFn hfa hff, tensorTestFn_support_of_forall hffs, hrep⟩

end IsotypyOfConvolutions
end
end IsotypicReproduction
section CoefficientIntegrands
open MeasureTheory
variable {F : Type} [Field F] [NumberField F]
private theorem whittakerCoefficientIntegrable_smul (pins : CarrierPins F) (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ)
    {φ : AdelicGL2 (𝓞 F) F → ℂ} {α : F} {g : AdelicGL2 (𝓞 F) F} (c : ℂ)
    (h : WhittakerCoefficientIntegrable F pins ψ φ α g) : WhittakerCoefficientIntegrable F pins ψ (c • φ) α g := by
  unfold WhittakerCoefficientIntegrable at h ⊢
  simp only [Pi.smul_apply, smul_eq_mul, mul_assoc]
  exact h.const_mul c

private theorem exists_archDerivAt_eq_rightConv_tensorTestFn {φ : AdelicGL2 (𝓞 F) F → ℂ} (hφ : Continuous φ)
    {fa : GL (Fin 2) (InfiniteAdeleRing F) → ℂ} {ff : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F) → ℂ}
    (hfa : IsArchTestFactor F fa) (hff : IsFinTestFactor F ff) (hrep : rightConv F φ (tensorTestFn fa ff) = φ)
    {w : InfinitePlace F} (hw : w.IsReal) (d : ArchDir) :
    ∃ fa' : GL (Fin 2) (InfiniteAdeleRing F) → ℂ, IsArchTestFactor F fa' ∧
      archDerivAt hw d φ = rightConv F φ (tensorTestFn fa' ff) := by
  obtain ⟨-, heq⟩ := (archDerivAt_rightConv_eq_rightConv_deriv_of_isFactorizableTestFn F hw d).1 φ _ hφ
    (isFactorizableTestFn_tensorTestFn hfa hff)
  obtain ⟨fa', hfa', hfa'eq⟩ := (archDerivAt_rightConv_eq_rightConv_deriv_of_isFactorizableTestFn F hw d).2.1 fa ff hfa
  refine ⟨fa', hfa', ?_⟩
  rw [hrep] at heq
  rw [heq]
  exact congrArg (rightConv F φ) hfa'eq

end CoefficientIntegrands
section CoefficientIntegrability

private theorem whittakerCoefficientIntegrable_self_and_archDerivAt
    (D : Set (AdelicGL2 (𝓞 ℚ) ℚ)) (U : Ideal (𝓞 ℚ) → Subgroup (AdelicGL2 (𝓞 ℚ) ℚ))
    (gen : HeightOneSpectrum (𝓞 ℚ) → AdelicGL2 (𝓞 ℚ) ℚ)
    (ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ) (hψ : IsGlobalAddChar ℚ ψ) {w : InfinitePlace ℚ} (hw : w.IsReal)
    {φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ} (hcont : Continuous φ)
    (hleft : ∀ (β : ℚ) (g : AdelicGL2 (𝓞 ℚ) ℚ), φ (unipotentGL2 (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) β) * g) = φ g)
    (hconv : ∃ α : AdelicGL2 (𝓞 ℚ) ℚ → ℂ, IsFactorizableTestFn ℚ α ∧ rightConv ℚ φ α = φ)
    (hsm : IsArchSmoothAt hw φ) :
    (∀ (α : ℚ) (g : AdelicGL2 (𝓞 ℚ) ℚ),
        WhittakerCoefficientIntegrable ℚ (productionPinsOf ℚ D U gen (adelicBox ℚ)) ψ φ α g) ∧
      ∀ (d : ArchDir) (α : ℚ) (g : AdelicGL2 (𝓞 ℚ) ℚ),
        WhittakerCoefficientIntegrable ℚ (productionPinsOf ℚ D U gen (adelicBox ℚ)) ψ (archDerivAt hw d φ) α g := by
  obtain ⟨α₀, hα₀, hrep₀⟩ := hconv
  obtain ⟨fa, ff, hfa, hff, rfl⟩ := isFactorizableTestFn_exists_eq_tensorTestFn hα₀
  refine ⟨fun α g => ?_, fun d α g => ?_⟩
  · exact (whittakerCoefficientIntegrable_and_summable_of_isKfSmooth_of_contDiff D U gen ψ hψ φ hleft
      (isKfSmooth_of_exists_rightConv_eq ℚ φ ⟨_, isFactorizableTestFn_tensorTestFn hfa hff, hrep₀⟩)
      (fun g => contDiff_two_unipotentGL2_ratArchLine_mul_of_isArchSmoothAt hw hsm g)).1 α g
  · obtain ⟨fa', hfa', hd⟩ := exists_archDerivAt_eq_rightConv_tensorTestFn hcont hfa hff hrep₀ hw d
    have hleft' : ∀ (β : ℚ) (g : AdelicGL2 (𝓞 ℚ) ℚ),
        archDerivAt hw d φ (unipotentGL2 (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) β) * g) = archDerivAt hw d φ g := by
      intro β g
      have hfun : (fun x => φ (unipotentGL2 (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) β) * x)) = φ := funext fun x => hleft β x
      have := congrFun (archDerivAt_comp_mul_left hw d φ (unipotentGL2 (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) β))) g
      rw [hfun] at this
      exact this.symm
    have hKf : IsKfSmooth ℚ (archDerivAt hw d φ) := by
      rw [hd]
      exact isKfSmooth_rightConv ℚ φ _ (isFactorizableTestFn_tensorTestFn hfa' hff)
    exact (whittakerCoefficientIntegrable_and_summable_of_isKfSmooth_of_contDiff D U gen ψ hψ _ hleft' hKf
      (fun g => contDiff_two_unipotentGL2_ratArchLine_mul_of_isArchSmoothAt hw (hsm.archDerivAt d) g)).1 α g

end CoefficientIntegrability
section WeightValue
variable (F : Type) [Field F] [NumberField F]
variable {F}

private theorem archWeightCharAt_rotationAt_eq_exp {w : InfinitePlace F} (hw : w.IsReal) (k : ℤ) (θ : ℝ) :
    ((archWeightCharAt hw k (rotationAt hw θ) : ℂˣ) : ℂ) = Complex.exp ((k : ℂ) * ((θ : ℂ) * Complex.I)) := by
  have h1 : ((archWeightCharAt hw k (rotationAt hw θ) : ℂˣ) : ℂ)
      = ((archWeightCharAt hw 1 (rotationAt hw θ) : ℂˣ) : ℂ) ^ k := by
    show ((archWeightOneAt hw (rotationAt hw θ) ^ k : ℂˣ) : ℂ)
      = ((archWeightOneAt hw (rotationAt hw θ) ^ (1 : ℤ) : ℂˣ) : ℂ) ^ k
    rw [zpow_one, Units.val_zpow_eq_zpow_val]
  have h2 : (⟨Real.cos θ, Real.sin θ⟩ : ℂ) = Complex.exp ((θ : ℂ) * Complex.I) :=
    Complex.ext (Complex.exp_ofReal_mul_I_re θ).symm (Complex.exp_ofReal_mul_I_im θ).symm
  rw [h1, archWeightCharAt_one_rotationAt, h2, ← Complex.exp_int_mul]

private theorem archDerivAt_E_sub_Fm_apply_of_hasArchCharacterAt₀ {w : InfinitePlace F} {hw : w.IsReal}
    {φ : AdelicGL2 (𝓞 F) F → ℂ} (hφ : IsArchSmoothAt hw φ) (k : ℤ)
    (hwt : HasArchCharacterAt₀ F w (archWeightCharAt hw k) φ) (g : AdelicGL2 (𝓞 F) F) :
    archDerivAt hw .E φ g - archDerivAt hw .Fm φ g = (k : ℂ) * Complex.I * φ g := by
  have hopen := isOpen_setOf_det_ne_zero
  have hcurve : (fun θ : ℝ => φ (g * archRealLiftAt hw (rotationArray θ))) =
      fun θ : ℝ => Complex.exp ((k : ℂ) * ((θ : ℂ) * Complex.I)) * φ g := by
    funext θ
    rw [archRealLiftAt_rotationArray, archRealGLAt_rotation, hwt (rotationAt hw θ) g,
      archWeightCharAt_rotationAt_eq_exp]
  have hder : HasDerivAt (fun θ : ℝ => Complex.exp ((k : ℂ) * ((θ : ℂ) * Complex.I)) * φ g)
      ((k : ℂ) * Complex.I * φ g) 0 := by
    have h2 := ((((hasDerivAt_id' (0 : ℝ)).ofReal_comp).mul_const Complex.I).const_mul (k : ℂ)).cexp.mul_const (φ g)
    simpa using h2
  have hΦ : HasFDerivAt (fun e' => φ (g * archRealLiftAt hw e'))
      (fderiv ℝ (fun e' => φ (g * archRealLiftAt hw e')) (Matrix.of.symm (1 : Matrix (Fin 2) (Fin 2) ℝ)))
      (rotationArray 0) := by
    rw [rotationArray_zero]
    exact (((hφ g).contDiffAt (hopen.mem_nhds det_of_of_symm_one)).differentiableAt (by simp)).hasFDerivAt
  have hchain := hΦ.comp_hasDerivAt (0 : ℝ) hasDerivAt_rotationArray
  have hdir : mulRightArrayCLM (archDirMatrix .E) (Matrix.of.symm (1 : Matrix (Fin 2) (Fin 2) ℝ)) -
      mulRightArrayCLM (archDirMatrix .Fm) (Matrix.of.symm (1 : Matrix (Fin 2) (Fin 2) ℝ)) =
        (![![0, 1], ![-1, 0]] : Fin 2 → Fin 2 → ℝ) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [mulRightArrayCLM_apply, archDirMatrix, Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply,
        Matrix.of_symm_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
        Matrix.cons_val_fin_one]
  rw [isArchSmoothAt_archDerivAt_apply_eq_fderiv hφ .E g, isArchSmoothAt_archDerivAt_apply_eq_fderiv hφ .Fm g,
    ← _root_.map_sub, hdir]
  have hcomp : (fun e' => φ (g * archRealLiftAt hw e')) ∘ rotationArray =
      fun θ : ℝ => Complex.exp ((k : ℂ) * ((θ : ℂ) * Complex.I)) * φ g := hcurve
  rw [hcomp] at hchain
  exact hchain.unique hder

end WeightValue
section LoweringTransfer

private theorem archDerivAt_whittakerCoefficient_one_eq (D : Set (AdelicGL2 (𝓞 ℚ) ℚ))
    (U : Ideal (𝓞 ℚ) → Subgroup (AdelicGL2 (𝓞 ℚ) ℚ)) (gen : HeightOneSpectrum (𝓞 ℚ) → AdelicGL2 (𝓞 ℚ) ℚ)
    (ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ) (hψ : IsGlobalAddChar ℚ ψ) {w : InfinitePlace ℚ} (hw : w.IsReal)
    {φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ} (hsm : IsArchSmoothAt hw φ)
    (hconv : ∃ α : AdelicGL2 (𝓞 ℚ) ℚ → ℂ, IsFactorizableTestFn ℚ α ∧ rightConv ℚ φ α = φ) (d : ArchDir) :
    archDerivAt hw d (whittakerCoefficient ℚ (productionPinsOf ℚ D U gen (adelicBox ℚ)) ψ φ 1)
      = whittakerCoefficient ℚ (productionPinsOf ℚ D U gen (adelicBox ℚ)) ψ (archDerivAt hw d φ) 1 :=
  (isArchSmoothAt_whittakerCoefficient_and_archDerivAt_comm D U gen ψ hψ.continuous w hw φ hsm
    (isKfSmooth_of_exists_rightConv_eq ℚ φ hconv) 1).2.1 d

end LoweringTransfer
section RaisingOperator
variable (F : Type) [Field F] [NumberField F]
variable {F}
private theorem archRaiseAt_smul {w : InfinitePlace F} (hw : w.IsReal) (c : ℂ) (φ : AdelicGL2 (𝓞 F) F → ℂ) :
    archRaiseAt hw (c • φ) = c • archRaiseAt hw φ := by
  simp only [archRaiseAt, archDerivAt_smul]
  module

private theorem archRotDerivAt_archRaiseAt_of_isArchSmoothAt {w : InfinitePlace F} {hw : w.IsReal}
    {φ : AdelicGL2 (𝓞 F) F → ℂ} (hφ : IsArchSmoothAt hw φ) :
    archRotDerivAt hw (archRaiseAt hw φ) =
      archRaiseAt hw (archRotDerivAt hw φ) + (2 * Complex.I) • archRaiseAt hw φ := by
  have hH := hφ.archDerivAt .H
  have hE := hφ.archDerivAt .E
  have hF := hφ.archDerivAt .Fm
  simp only [archRotDerivAt, archRaiseAt, archDerivAt_smul,
    archDerivAt_add hH ((hE.add hF).smul Complex.I) .E, archDerivAt_add hH ((hE.add hF).smul Complex.I) .Fm,
    archDerivAt_add hE hF .E, archDerivAt_add hE hF .Fm, archDerivAt_sub hE hF .H, archDerivAt_sub hE hF .E,
    archDerivAt_sub hE hF .Fm, isArchSmoothAt_archDerivAt_E_H hφ, isArchSmoothAt_archDerivAt_Fm_H hφ,
    isArchSmoothAt_archDerivAt_Fm_E hφ]
  funext g
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  first
    | linear_combination (2 * (archDerivAt hw .E φ g + archDerivAt hw .Fm φ g)) * Complex.I_sq
    | linear_combination (-2 * (archDerivAt hw .E φ g + archDerivAt hw .Fm φ g)) * Complex.I_sq

private theorem archRotDerivAt_eq_of_hasArchCharacterAt₀
    {w : InfinitePlace F} {hw : w.IsReal} {φ : AdelicGL2 (𝓞 F) F → ℂ}
    (hφ : IsArchSmoothAt hw φ) (k : ℤ) (hk : HasArchCharacterAt₀ F w (archWeightCharAt hw k) φ) :
    archRotDerivAt hw φ = ((k : ℂ) * Complex.I) • φ := by
  funext g
  simp only [archRotDerivAt, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  exact archDerivAt_E_sub_Fm_apply_of_hasArchCharacterAt₀ hφ k hk g

private theorem archRotDerivAt_archRaiseAt_eq_of_eq {w : InfinitePlace F} {hw : w.IsReal} {φ : AdelicGL2 (𝓞 F) F → ℂ}
    (hφ : IsArchSmoothAt hw φ) {k : ℂ} (hW : archRotDerivAt hw φ = (k * Complex.I) • φ) :
    archRotDerivAt hw (archRaiseAt hw φ) = ((k + 2) * Complex.I) • archRaiseAt hw φ := by
  rw [archRotDerivAt_archRaiseAt_of_isArchSmoothAt hφ, hW, archRaiseAt_smul, ← add_smul]
  congr 1
  ring

private theorem apply_mul_archRealLiftAt_rotationArray_of_archRotDerivAt_eq {w : InfinitePlace F} {hw : w.IsReal}
    {φ : AdelicGL2 (𝓞 F) F → ℂ} (hφ : IsArchSmoothAt hw φ) {k : ℂ} (hW : archRotDerivAt hw φ = (k * Complex.I) • φ)
    (θ : ℝ) (g : AdelicGL2 (𝓞 F) F) :
    φ (g * archRealLiftAt hw (rotationArray θ)) = Complex.exp (k * ((θ : ℂ) * Complex.I)) * φ g := by
  have hopen := isOpen_setOf_det_ne_zero
  set f : ℝ → ℂ := fun θ => φ (g * archRealLiftAt hw (rotationArray θ)) with hf

  have hf' : ∀ θ : ℝ, HasDerivAt f (k * Complex.I * f θ) θ := by
    intro θ
    have hΦ : HasFDerivAt (fun e' => φ (g * archRealLiftAt hw e'))
        (fderiv ℝ (fun e' => φ (g * archRealLiftAt hw e')) (rotationArray θ)) (rotationArray θ) :=
      (((hφ g).contDiffAt (hopen.mem_nhds (det_of_rotationArray θ))).differentiableAt (by simp)).hasFDerivAt
    have hchain := hΦ.comp_hasDerivAt θ (hasDerivAt_rotationArray' θ)
    have hkey : fderiv ℝ (fun e' => φ (g * archRealLiftAt hw e')) (rotationArray θ)
        (![![-Real.sin θ, Real.cos θ], ![-Real.cos θ, -Real.sin θ]] : Fin 2 → Fin 2 → ℝ) = k * Complex.I * f θ := by
      rw [← mulRightArrayCLM_E_sub_Fm_rotationArray, _root_.map_sub,
        ← isArchSmoothAt_archDerivAt_apply_mul_archRealLiftAt hφ .E g (det_of_rotationArray θ),
        ← isArchSmoothAt_archDerivAt_apply_mul_archRealLiftAt hφ .Fm g (det_of_rotationArray θ)]
      have h := congrFun hW (g * archRealLiftAt hw (rotationArray θ))
      simp only [archRotDerivAt, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at h
      exact h
    rw [hkey] at hchain
    exact hchain

  have hu : ∀ θ : ℝ, HasDerivAt (fun θ : ℝ => Complex.exp (-(k * ((θ : ℂ) * Complex.I))) * f θ) 0 θ := by
    intro θ
    have h := ((((hasDerivAt_id' θ).ofReal_comp.mul_const Complex.I).const_mul k).fun_neg.cexp).fun_mul (hf' θ)
    refine h.congr_deriv (Eq.symm ?_)
    push_cast
    ring
  have hconst : ∀ θ : ℝ, Complex.exp (-(k * ((θ : ℂ) * Complex.I))) * f θ = f 0 := by
    intro θ
    have h := is_const_of_deriv_eq_zero (fun θ => (hu θ).differentiableAt) (fun θ => (hu θ).deriv) θ 0
    simpa using h
  have hf0 : f 0 = φ g := by
    simp only [hf, rotationArray_zero, archRealLiftAt_of_symm_one, mul_one]
  calc f θ = Complex.exp (k * ((θ : ℂ) * Complex.I)) * (Complex.exp (-(k * ((θ : ℂ) * Complex.I))) * f θ) := by
        rw [← mul_assoc, ← Complex.exp_add, add_neg_cancel, Complex.exp_zero, one_mul]
    _ = Complex.exp (k * ((θ : ℂ) * Complex.I)) * φ g := by rw [hconst θ, hf0]

private theorem hasArchCharacterAt₀_of_archRotDerivAt_eq
    {w : InfinitePlace F} {hw : w.IsReal} {φ : AdelicGL2 (𝓞 F) F → ℂ}
    (hφ : IsArchSmoothAt hw φ) (k : ℤ) (hW : archRotDerivAt hw φ = ((k : ℂ) * Complex.I) • φ) :
    HasArchCharacterAt₀ F w (archWeightCharAt hw k) φ := by
  intro r g
  obtain ⟨θ, rfl⟩ := exists_rotationAt_eq hw r
  rw [archWeightCharAt_rotationAt_eq_exp hw k θ, ← archRealGLAt_rotation, ← archRealLiftAt_rotationArray]
  exact apply_mul_archRealLiftAt_rotationArray_of_archRotDerivAt_eq hφ hW θ g

private theorem hasArchCharacterAt₀_archRaiseAt {w : InfinitePlace F} {hw : w.IsReal} {φ : AdelicGL2 (𝓞 F) F → ℂ}
    (hφ : IsArchSmoothAt hw φ) (k : ℤ) (hk : HasArchCharacterAt₀ F w (archWeightCharAt hw k) φ) :
    HasArchCharacterAt₀ F w (archWeightCharAt hw (k + 2)) (archRaiseAt hw φ) := by
  refine hasArchCharacterAt₀_of_archRotDerivAt_eq (isArchSmoothAt_archRaiseAt hφ) (k + 2) ?_
  exact_mod_cast archRotDerivAt_archRaiseAt_eq_of_eq hφ (archRotDerivAt_eq_of_hasArchCharacterAt₀ hφ k hk)

end RaisingOperator
section RaisedCoefficient
variable (F : Type) [Field F] [NumberField F]
variable {F}
private theorem whittakerCoefficientIntegrable_add (pins : CarrierPins F) (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ)
    {φ₁ φ₂ : AdelicGL2 (𝓞 F) F → ℂ} {α : F} {g : AdelicGL2 (𝓞 F) F}
    (h₁ : WhittakerCoefficientIntegrable F pins ψ φ₁ α g) (h₂ : WhittakerCoefficientIntegrable F pins ψ φ₂ α g) :
    WhittakerCoefficientIntegrable F pins ψ (φ₁ + φ₂) α g := by
  unfold WhittakerCoefficientIntegrable at h₁ h₂ ⊢
  simp only [Pi.add_apply, add_mul]
  exact h₁.add h₂

private theorem whittakerCoefficient_smul_apply (pins : CarrierPins F) (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (cs : ℂ)
    (φ : AdelicGL2 (𝓞 F) F → ℂ) (α : F) (x : AdelicGL2 (𝓞 F) F) :
    whittakerCoefficient F pins ψ (cs • φ) α x = cs * whittakerCoefficient F pins ψ φ α x :=
  congrFun (whittakerCoefficient_smul_fn F pins ψ cs φ α) x

end RaisedCoefficient
section RaisedCoefficientOverRationals

private theorem whittakerCoefficient_one_archRaiseAt_apply (D : Set (AdelicGL2 (𝓞 ℚ) ℚ))
    (U : Ideal (𝓞 ℚ) → Subgroup (AdelicGL2 (𝓞 ℚ) ℚ)) (gen : HeightOneSpectrum (𝓞 ℚ) → AdelicGL2 (𝓞 ℚ) ℚ)
    (ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ) (hψ : IsGlobalAddChar ℚ ψ) {w : InfinitePlace ℚ} (hw : w.IsReal)
    {φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ} (hcont : Continuous φ)
    (hleft : ∀ (β : ℚ) (g : AdelicGL2 (𝓞 ℚ) ℚ), φ (unipotentGL2 (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) β) * g) = φ g)
    (hconv : ∃ α : AdelicGL2 (𝓞 ℚ) ℚ → ℂ, IsFactorizableTestFn ℚ α ∧ rightConv ℚ φ α = φ) (hsm : IsArchSmoothAt hw φ)
    (p : AdelicGL2 (𝓞 ℚ) ℚ) :
    whittakerCoefficient ℚ (productionPinsOf ℚ D U gen (adelicBox ℚ)) ψ (archRaiseAt hw φ) 1 p
      = archDerivAt hw .H (whittakerCoefficient ℚ (productionPinsOf ℚ D U gen (adelicBox ℚ)) ψ φ 1) p
        + Complex.I * (archDerivAt hw .E (whittakerCoefficient ℚ (productionPinsOf ℚ D U gen (adelicBox ℚ)) ψ φ 1) p
          + archDerivAt hw .Fm (whittakerCoefficient ℚ (productionPinsOf ℚ D U gen (adelicBox ℚ)) ψ φ 1) p) := by
  obtain ⟨-, hint⟩ := whittakerCoefficientIntegrable_self_and_archDerivAt D U gen ψ hψ hw hcont hleft hconv hsm
  rw [archDerivAt_whittakerCoefficient_one_eq D U gen ψ hψ hw hsm hconv .H,
    archDerivAt_whittakerCoefficient_one_eq D U gen ψ hψ hw hsm hconv .E,
    archDerivAt_whittakerCoefficient_one_eq D U gen ψ hψ hw hsm hconv .Fm]
  show whittakerCoefficient ℚ (productionPinsOf ℚ D U gen (adelicBox ℚ)) ψ
    (archDerivAt hw .H φ + Complex.I • (archDerivAt hw .E φ + archDerivAt hw .Fm φ)) 1 p = _
  rw [whittakerCoefficient_add _ ψ (hint .H 1 p) (whittakerCoefficientIntegrable_smul _ ψ Complex.I
      (whittakerCoefficientIntegrable_add _ ψ (hint .E 1 p) (hint .Fm 1 p))),
    whittakerCoefficient_smul_apply, whittakerCoefficient_add _ ψ (hint .E 1 p) (hint .Fm 1 p)]

private theorem isIsotypicCuspFormAt_smul_comb_of_rightConv_tensorTestFn
    (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 ℚ) ℚ)) (hd : d₁ < d₂)
    (hcov : CoversModCentre ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂))
    (Φ : HeckeEigensystem ℚ ℂ)
    {ξ : (productionPinsOf ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂)
        (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ)).Z →* ℂˣ}
    {S : Finset (HeightOneSpectrum (𝓞 ℚ))} {φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ}
    (hφ : IsIsotypicCuspFormAt ℚ
      (productionPinsOf ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂)
        (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ))
      ξ Φ.level S Φ φ)
    (hne : φ ≠ 0) {fa : GL (Fin 2) (InfiniteAdeleRing ℚ) → ℂ} {ff : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ) → ℂ}
    (hfa : IsArchTestFactor ℚ fa) (hff : IsFinTestFactor ℚ ff)
    (hffs : ∀ x : AdelicGL2 (𝓞 ℚ) ℚ, ff (glFin (𝓞 ℚ) ℚ x) ≠ 0 → ∃ a k : AdelicGL2 (𝓞 ℚ) ℚ,
      glFin (𝓞 ℚ) ℚ a = 1 ∧ k ∈ levelOne (𝓞 ℚ) ℚ Φ.level ⊓ finiteAdelicGL2Subgroup ℚ ∧ x = a * k)
    (hrep : rightConv ℚ φ (tensorTestFn fa ff) = φ) {w : InfinitePlace ℚ} (hw : w.IsReal) (cH cE cF c₀ : ℂ) :
    IsIsotypicCuspFormAt ℚ
      (productionPinsOf ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂)
        (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ))
      ξ Φ.level S Φ
      (c₀ • (cH • archDerivAt hw .H φ + cE • archDerivAt hw .E φ + cF • archDerivAt hw .Fm φ)) := by

  have hder : ∀ d : ArchDir, ∃ fa' : GL (Fin 2) (InfiniteAdeleRing ℚ) → ℂ, IsArchTestFactor ℚ fa' ∧
      archDerivAt hw d φ = rightConv ℚ φ (tensorTestFn fa' ff) := by
    intro d
    obtain ⟨-, heq⟩ := (archDerivAt_rightConv_eq_rightConv_deriv_of_isFactorizableTestFn ℚ hw d).1 φ _
      hφ.continuous (isFactorizableTestFn_tensorTestFn hfa hff)
    obtain ⟨fa', hfa', hfa'eq⟩ :=
      (archDerivAt_rightConv_eq_rightConv_deriv_of_isFactorizableTestFn ℚ hw d).2.1 fa ff hfa
    refine ⟨fa', hfa', ?_⟩
    rw [hrep] at heq
    rw [heq]
    exact congrArg (rightConv ℚ φ) hfa'eq
  obtain ⟨fH, hfH, hH⟩ := hder .H
  obtain ⟨fE, hfE, hE⟩ := hder .E
  obtain ⟨fF, hfF, hF⟩ := hder .Fm
  have hcs : ∀ fa₀ : GL (Fin 2) (InfiniteAdeleRing ℚ) → ℂ, IsArchTestFactor ℚ fa₀ →
      Continuous (tensorTestFn fa₀ ff) ∧ HasCompactSupport (tensorTestFn fa₀ ff) := fun _ h =>
    continuous_and_hasCompactSupport_of_isFactorizableTestFn ℚ _ (isFactorizableTestFn_tensorTestFn h hff)
  have hfX : IsArchTestFactor ℚ (cH • fH + cE • fE + cF • fF) := (isArchTestFactor_add ((isArchTestFactor_add
      ((isArchTestFactor_smul hfH) cH)) ((isArchTestFactor_smul hfE) cE))) ((isArchTestFactor_smul hfF) cF)

  have h1 : rightConv ℚ φ (tensorTestFn (cH • fH) ff) = cH • archDerivAt hw .H φ := by
    rw [tensorTestFn_smul, rightConv_smul_right, hH]
  have h2 : rightConv ℚ φ (tensorTestFn (cE • fE) ff) = cE • archDerivAt hw .E φ := by
    rw [tensorTestFn_smul, rightConv_smul_right, hE]
  have h3 : rightConv ℚ φ (tensorTestFn (cF • fF) ff) = cF • archDerivAt hw .Fm φ := by
    rw [tensorTestFn_smul, rightConv_smul_right, hF]
  have h12 : rightConv ℚ φ (tensorTestFn (cH • fH + cE • fE) ff) =
      cH • archDerivAt hw .H φ + cE • archDerivAt hw .E φ := by
    rw [tensorTestFn_add,
        rightConv_add_right hφ.continuous (hcs _ ((isArchTestFactor_smul hfH) cH)).1 (hcs _
            ((isArchTestFactor_smul hfH) cH)).2
      (hcs _ ((isArchTestFactor_smul hfE) cE)).1 (hcs _ ((isArchTestFactor_smul hfE) cE)).2, h1, h2]
  have hcomb : rightConv ℚ φ (tensorTestFn (cH • fH + cE • fE + cF • fF) ff) =
      cH • archDerivAt hw .H φ + cE • archDerivAt hw .E φ + cF • archDerivAt hw .Fm φ := by
    rw [tensorTestFn_add,
        rightConv_add_right hφ.continuous (hcs _ ((isArchTestFactor_add ((isArchTestFactor_smul hfH) cH))
            ((isArchTestFactor_smul hfE) cE))).1
      (hcs _ ((isArchTestFactor_add ((isArchTestFactor_smul hfH) cH)) ((isArchTestFactor_smul hfE) cE))).2 (hcs
          _ ((isArchTestFactor_smul hfF) cF)).1 (hcs _ ((isArchTestFactor_smul hfF) cF)).2, h12, h3]
  have hfinal : rightConv ℚ φ (tensorTestFn (c₀ • (cH • fH + cE • fE + cF • fF)) ff)
      = c₀ • (cH • archDerivAt hw .H φ + cE • archDerivAt hw .E φ + cF • archDerivAt hw .Fm φ) := by
    rw [tensorTestFn_smul, rightConv_smul_right, hcomb]
  rw [← hfinal]
  exact isIsotypicCuspFormAt_rightConv_of_isIsotypicCuspFormAt c u d₁ d₂ T hd hcov Φ hφ hne _
    (isFactorizableTestFn_tensorTestFn ((isArchTestFactor_smul hfX) c₀) hff) (tensorTestFn_support_of_forall hffs)

end RaisedCoefficientOverRationals
end MinimalWeightWhittaker
p2m_reactivate "P2MW.S_LanglandsTunnell_isIsotypicCuspFormAt_smul_archRaise_and_whittakerCoefficient_archRaise_archLower.MinimalWeightWhittaker"

open MinimalWeightWhittaker in
theorem solution
    (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 ℚ) ℚ)) (hd : d₁ < d₂)
    (hcov : CoversModCentre ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂))
    (Φ : HeckeEigensystem ℚ ℂ) (ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ) (hψ : IsGlobalAddChar ℚ ψ)
    (w : InfinitePlace ℚ) (hw : w.IsReal)
    (ξ : (productionPinsOf ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂)
      (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ)).Z →* ℂˣ)
    (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ)
    (hiso : IsIsotypicCuspFormAt ℚ (productionPinsOf ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂)
      (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ))
      ξ Φ.level S Φ φ)
    (hne : φ ≠ 0) (hconv : ∃ α : AdelicGL2 (𝓞 ℚ) ℚ → ℂ, IsFactorizableTestFn ℚ α ∧ rightConv ℚ φ α = φ)
    (hsm : IsArchSmoothAt hw φ) (k : InfinitePlace ℚ → ℤ)
    (hwt : ∀ (w' : InfinitePlace ℚ) (hw' : w'.IsReal), HasArchCharacterAt₀ ℚ w' (archWeightCharAt hw' (k w')) φ)
    (W : AdelicGL2 (𝓞 ℚ) ℚ → ℂ)
    (hW : W = whittakerCoefficient ℚ
      (productionPinsOf ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂)
        (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ))
      ψ φ 1) :

    (∀ p : AdelicGL2 (𝓞 ℚ) ℚ,
      whittakerCoefficient ℚ
          (productionPinsOf ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂)
            (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ))
          ψ (archDerivAt hw ArchDir.H φ - Complex.I • (archDerivAt hw ArchDir.E φ + archDerivAt hw ArchDir.Fm φ)) 1 p
        = archDerivAt hw ArchDir.H W p - Complex.I * (archDerivAt hw ArchDir.E W p + archDerivAt hw ArchDir.Fm W p)) ∧
    (∀ p : AdelicGL2 (𝓞 ℚ) ℚ,
      whittakerCoefficient ℚ
          (productionPinsOf ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂)
            (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ))
          ψ (archDerivAt hw ArchDir.H φ + Complex.I • (archDerivAt hw ArchDir.E φ + archDerivAt hw ArchDir.Fm φ)) 1 p
        = archDerivAt hw ArchDir.H W p + Complex.I * (archDerivAt hw ArchDir.E W p + archDerivAt hw ArchDir.Fm W p)) ∧

    (∀ cs : ℂ,
      IsIsotypicCuspFormAt ℚ (productionPinsOf ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂)
          (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ))
          ξ Φ.level S Φ
          (cs • (archDerivAt hw ArchDir.H φ
            + Complex.I • (archDerivAt hw ArchDir.E φ + archDerivAt hw ArchDir.Fm φ))) ∧
      HasArchCharacterAt₀ ℚ w (archWeightCharAt hw (k w + 2))
          (cs • (archDerivAt hw ArchDir.H φ
            + Complex.I • (archDerivAt hw ArchDir.E φ + archDerivAt hw ArchDir.Fm φ))) ∧
      (cs • (archDerivAt hw ArchDir.H φ + Complex.I • (archDerivAt hw ArchDir.E φ + archDerivAt hw ArchDir.Fm φ)) ≠ 0 →
        ∃ α : AdelicGL2 (𝓞 ℚ) ℚ → ℂ, IsFactorizableTestFn ℚ α ∧
          rightConv ℚ (cs • (archDerivAt hw ArchDir.H φ
            + Complex.I • (archDerivAt hw ArchDir.E φ + archDerivAt hw ArchDir.Fm φ))) α
            = cs • (archDerivAt hw ArchDir.H φ
              + Complex.I • (archDerivAt hw ArchDir.E φ + archDerivAt hw ArchDir.Fm φ)))) := by
  have hleft : ∀ (β : ℚ) (g : AdelicGL2 (𝓞 ℚ) ℚ), φ (unipotentGL2 (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) β) * g) = φ g :=
    fun β g => apply_unipotentGL2_algebraMap_mul_of_isIsotypicCuspFormAt hiso β g
  refine ⟨?_, ?_, ?_⟩
  ·
    intro p
    obtain ⟨-, hint⟩ := whittakerCoefficientIntegrable_self_and_archDerivAt _ _ _ ψ hψ hw hiso.continuous hleft hconv
      hsm
    rw [hW, archDerivAt_whittakerCoefficient_one_eq _ _ _ ψ hψ hw hsm hconv .H,
      archDerivAt_whittakerCoefficient_one_eq _ _ _ ψ hψ hw hsm hconv .E,
      archDerivAt_whittakerCoefficient_one_eq _ _ _ ψ hψ hw hsm hconv .Fm,
      whittakerCoefficient_sub _ ψ (hint .H 1 p) (whittakerCoefficientIntegrable_smul _ ψ Complex.I
        (whittakerCoefficientIntegrable_add _ ψ (hint .E 1 p) (hint .Fm 1 p))),
      whittakerCoefficient_smul_apply, whittakerCoefficient_add _ ψ (hint .E 1 p) (hint .Fm 1 p)]
  ·
    intro p
    rw [hW]
    exact whittakerCoefficient_one_archRaiseAt_apply _ _ _ ψ hψ hw hiso.continuous hleft hconv hsm p
  · intro cs
    have harch₁ : φ ∈ archCutSubmodule ℚ
        (ArchTypeFamily.ofChar ℚ fun w' => archWeightCharAt (isReal_infinitePlace_rat w') (k w')) :=
      mem_archCutSubmodule_weightTypeFamilyRat hwt
    obtain ⟨fa, ff, hfa, hff, hffs, hrep⟩ := exists_tensorTestFn_rightConv_eq_self_of_isIsotypicCuspFormAt c u d₁ d₂ T
      hd hcov Φ (fun w' => archWeightCharAt (isReal_infinitePlace_rat w') (k w')) hiso hne harch₁
    have hX : archRaiseAt hw φ = (1 : ℂ) • archDerivAt hw .H φ + Complex.I • archDerivAt hw .E φ
        + Complex.I • archDerivAt hw .Fm φ := by
      simp only [archRaiseAt, one_smul, smul_add, add_assoc]
    have hiso₂ : IsIsotypicCuspFormAt ℚ
        (productionPinsOf ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂)
          (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ)
          (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ))
        ξ Φ.level S Φ (cs • archRaiseAt hw φ) := by
      have h := isIsotypicCuspFormAt_smul_comb_of_rightConv_tensorTestFn c u d₁ d₂ T hd hcov Φ hiso hne hfa hff hffs
        hrep hw 1 Complex.I Complex.I cs
      rw [hX]
      exact h
    have hwt₂ : ∀ (w' : InfinitePlace ℚ) (hw' : w'.IsReal),
        HasArchCharacterAt₀ ℚ w' (archWeightCharAt hw' ((fun _ => k w + 2) w')) (cs • archRaiseAt hw φ) := by
      intro w' hw'
      obtain rfl : w' = w := Subsingleton.elim w' w
      exact hasArchCharacterAt₀_smul _ (hasArchCharacterAt₀_archRaiseAt hsm (k w') (hwt w' hw'))
    have harch₂ : cs • archRaiseAt hw φ ∈ archCutSubmodule ℚ
        (ArchTypeFamily.ofChar ℚ fun w' => archWeightCharAt (isReal_infinitePlace_rat w') ((fun _ => k w + 2) w')) :=
      mem_archCutSubmodule_weightTypeFamilyRat (k := fun _ => k w + 2) hwt₂
    refine ⟨hiso₂, hwt₂ w hw, fun hne₂ => ?_⟩
    obtain ⟨γ, hγ, -, hγrep⟩ := exists_isFactorizableTestFn_rightConv_eq_self_of_isIsotypicCuspFormAt c u d₁ d₂ T hd
      hcov Φ (fun w' => archWeightCharAt (isReal_infinitePlace_rat w') ((fun _ => k w + 2) w')) hiso₂ hne₂ harch₂
    exact ⟨γ, hγ, hγrep⟩

end S_LanglandsTunnell_isIsotypicCuspFormAt_smul_archRaise_and_whittakerCoefficient_archRaise_archLower
end P2MW
export P2MW.S_LanglandsTunnell_isIsotypicCuspFormAt_smul_archRaise_and_whittakerCoefficient_archRaise_archLower (solution)
