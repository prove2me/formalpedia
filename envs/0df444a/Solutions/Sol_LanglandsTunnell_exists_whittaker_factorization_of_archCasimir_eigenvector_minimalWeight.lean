-- Prove2me | solution 1 for LanglandsTunnell.exists_whittaker_factorization_of_archCasimir_eigenvector_minimalWeight
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/31f747a3-b9a9-5b88-8042-44e4b2634ad8

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
import Theorems.Thm_AutomorphicForm_whittakerCoefficient_unipotentGL2_mul
import Theorems.Thm_LanglandsTunnell_isArchSmoothAt_whittakerCoefficient_and_archDerivAt_comm
import Theorems.Thm_AutomorphicForm_isKfSmooth_rightConv
import Theorems.Thm_LanglandsTunnell_whittaker_ode_splitTorus_of_isArchSmoothAt_of_archCasimirAt_eq
import Theorems.Thm_LanglandsTunnell_linearDependent_of_whittaker_ode_of_moderateGrowth_complexParam
import Theorems.Thm_NumberField_TateGlobal_ideleNorm_eq_prod_norm_infinitePlace_pow_mult_of_snd_eq_one
import Theorems.Thm_AutomorphicForm_whittakerCoefficientIntegrable_and_summable_of_isKfSmooth_of_contDiff
import Theorems.Thm_AutomorphicForm_exists_whittakerCoefficient_one_ne_zero
import Theorems.Thm_AutomorphicForm_continuous_unipotentGL2
import Theorems.Thm_LanglandsTunnell_mellin_whittakerProfile_eq_GammaC_of_lowering_eq_zero
import Theorems.Thm_AutomorphicForm_rightConv_apply_mul_eq_rightConv_comp_inv_mul_apply
import Theorems.Thm_AutomorphicForm_isFactorizableTestFn_comp_inv_mul_of_isFactorizableTestFn
import Theorems.Thm_NumberField_AdelicHaar_measurePreserving_mul_algebraMap_adelicAddHaar
import Theorems.Thm_NumberField_AdelicBox_isAddFundamentalDomain_preimage_mul_algebraMap_adelicBox
import Theorems.Thm_AutomorphicForm_exists_norm_whittakerCoefficient_rightConv_diagOne_mul_le_ideleNorm_rpow_mul_norm_infinitePlace_rpow_neg
import Theorems.Thm_AutomorphicForm_exists_ne_zero_forall_eq_stdAddChar_mul_of_isGlobalAddChar
import Theorems.Thm_NumberField_StandardAddChar_isGlobalAddChar_stdAddChar
import Theorems.Thm_AutomorphicForm_isIdeleClassChar_and_continuous_of_isLsXiFunction_of_continuous
import Theorems.Thm_RatIdele_exists_norm_apply_eq_ideleNorm_rpow
import Theorems.Thm_AutomorphicForm_isIsotypicCuspFormAt_rightConv_of_isFactorizableTestFn_of_support_subset_of_coversModCentre
import Theorems.Thm_AutomorphicForm_exists_finTestFactor_isUnitFactorizableAboveOfType_tendsto_rightConv_of_mem_archCutSubmodule
import Theorems.Thm_AutomorphicForm_finiteDimensional_isotypicCuspSubmodule_inf_archCutSubmodule
import Theorems.Thm_AutomorphicForm_continuous_and_hasCompactSupport_of_isFactorizableTestFn
import Theorems.Thm_AutomorphicForm_archDerivAt_rightConv_eq_rightConv_deriv_of_isFactorizableTestFn
import Theorems.Thm_LanglandsTunnell_mellin_whittakerProfile_eq_archFactor_of_whittaker_ode_weightZero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_exists_whittaker_factorization_of_archCasimir_eigenvector_minimalWeight
p2m_attr_erase "instance" "instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions AutomorphicForm.compactSpace_maximalCompactAway AutomorphicForm.compactSpace_adelicMaximalCompact AutomorphicForm.isProbabilityMeasure_maximalCompactHaar AutomorphicForm.isHaarMeasure_maximalCompactHaar AutomorphicForm.compactSpace_maximalCompactAt AutomorphicForm.isProbabilityMeasure_maximalCompactAwayHaar AutomorphicForm.isHaarMeasure_maximalCompactAwayHaar AutomorphicForm.isProbabilityMeasure_maximalCompactAtHaar AutomorphicForm.isHaarMeasure_maximalCompactAtHaar instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions"
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

private theorem apply_archRealGLAt_unipotentGL2_mul_of_forall_unipotentGL2_mul
    (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) {w : InfinitePlace F} (hw : w.IsReal)
    (hψr : ∀ x : InfiniteAdeleRing F, (∀ w' : InfinitePlace F, w' ≠ w → x w' = 0) →
      ψ (⟨x, 0⟩ : AdeleRing (𝓞 F) F) = Complex.exp (2 * Real.pi * Complex.I * extensionEmbedding w (x w)))
    (W : AdelicGL2 (𝓞 F) F → ℂ)
    (hW : ∀ (X : AdeleRing (𝓞 F) F) (g : AdelicGL2 (𝓞 F) F), W (unipotentGL2 X * g) = ψ X * W g)
    (x : ℝ) (g : AdelicGL2 (𝓞 F) F) :
    W (archRealGLAt hw (unipotentGL2 x) * g) = Complex.exp (2 * Real.pi * Complex.I * x) * W g := by
  obtain ⟨X, hXw, hX0, hX⟩ := archRealGLAt_unipotentGL2_eq F hw x
  rw [hX]
  refine (hW ⟨X, 0⟩ g).trans ?_
  rw [hψr X hX0, hXw]
  congr 3
  rw [← extensionEmbeddingOfIsReal_apply hw, ← ringEquivRealOfIsReal_apply hw, RingEquiv.apply_symm_apply]

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

private theorem apply_unipotentGL2_algebraMap_add_mul_of_isIsotypicCuspFormAt {pins : CarrierPins F} {ξ : pins.Z →* ℂˣ}
    {N : Ideal (𝓞 F)} {S : Finset (HeightOneSpectrum (𝓞 F))} {Φ : HeckeEigensystem F ℂ}
    {φ : AdelicGL2 (𝓞 F) F → ℂ} (h : IsIsotypicCuspFormAt F pins ξ N S Φ φ)
    (β : F) (u : AdeleRing (𝓞 F) F) (g : AdelicGL2 (𝓞 F) F) :
    φ (unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) β + u) * g) = φ (unipotentGL2 u * g) := by
  have hinv := (isLsXiFunction_of_isIsotypicCuspFormAt h).left_invariant
  rw [unipotentGL2_add, mul_assoc, ← globalPoints_unipotentGL2, hinv]

variable (F)

private theorem whittakerCoefficient_one_unipotentGL2_mul_of_isIsotypicCuspFormAt
    (D : Set (AdelicGL2 (𝓞 F) F)) (U : Ideal (𝓞 F) → Subgroup (AdelicGL2 (𝓞 F) F))
    (gen : HeightOneSpectrum (𝓞 F) → AdelicGL2 (𝓞 F) F)
    (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (hψ : IsGlobalAddChar F ψ)
    {pins : CarrierPins F} {ξ : pins.Z →* ℂˣ} {N : Ideal (𝓞 F)} {S : Finset (HeightOneSpectrum (𝓞 F))}
    {Φ : HeckeEigensystem F ℂ} {φ : AdelicGL2 (𝓞 F) F → ℂ} (hφ : IsIsotypicCuspFormAt F pins ξ N S Φ φ)
    (x : AdeleRing (𝓞 F) F) (g : AdelicGL2 (𝓞 F) F) :
    whittakerCoefficient F (productionPinsOf F D U gen (adelicBox F)) ψ φ 1 (unipotentGL2 x * g) =
      ψ x * whittakerCoefficient F (productionPinsOf F D U gen (adelicBox F)) ψ φ 1 g := by
  have h := whittakerCoefficient_unipotentGL2_mul F D U gen ψ hψ.principalInvariant φ g
    (fun β u => (apply_unipotentGL2_algebraMap_add_mul_of_isIsotypicCuspFormAt hφ) β u g) 1 x
  rwa [map_one, one_mul] at h

end Periodicity

section Peeling

section CentralLaw

private theorem whittakerCoefficient_centralScalar_mul (pins : CarrierPins F) (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ)
    {ξ : pins.Z →* ℂˣ} {φ : AdelicGL2 (𝓞 F) F → ℂ} (hφ : IsLsXiFunction (𝓞 F) F pins.Z ξ φ) (z : pins.Z) (α : F)
    (g : AdelicGL2 (𝓞 F) F) :
    whittakerCoefficient F pins ψ φ α (centralScalar (𝓞 F) F (z : (AdeleRing (𝓞 F) F)ˣ) * g)
      = ((ξ z : ℂˣ) : ℂ) * whittakerCoefficient F pins ψ φ α g := by
  unfold whittakerCoefficient
  have h : ∀ x : AdeleRing (𝓞 F) F,
      φ (unipotentGL2 x * (centralScalar (𝓞 F) F (z : (AdeleRing (𝓞 F) F)ˣ) * g))
        = ((ξ z : ℂˣ) : ℂ) * φ (unipotentGL2 x * g) := by
    intro x
    rw [← mul_assoc, mul_centralScalar_comm (F := F), mul_assoc, hφ.central_transform z]
  simp only [h, mul_assoc, integral_const_mul]

end CentralLaw

section RealUnits

variable {F}

private noncomputable def archRealUnit {w : InfinitePlace F} (hw : w.IsReal) (r : ℝ) (hr : r ≠ 0) : (w.Completion)ˣ :=
  Units.mk0 ((ringEquivRealOfIsReal hw).symm r) ((map_ne_zero_iff _ (ringEquivRealOfIsReal hw).symm.injective).mpr hr)

private theorem archRealUnit_coe {w : InfinitePlace F} (hw : w.IsReal) (r : ℝ) (hr : r ≠ 0) :
    ((archRealUnit hw r hr : (w.Completion)ˣ) : w.Completion) = (ringEquivRealOfIsReal hw).symm r := rfl

private theorem extensionEmbedding_archRealUnit {w : InfinitePlace F} (hw : w.IsReal) (r : ℝ) (hr : r ≠ 0) :
    extensionEmbedding w ((archRealUnit hw r hr : (w.Completion)ˣ) : w.Completion) = (r : ℂ) := by
  rw [archRealUnit_coe, ← extensionEmbeddingOfIsReal_apply hw, ← ringEquivRealOfIsReal_apply hw,
    RingEquiv.apply_symm_apply]

private theorem norm_archRealUnit {w : InfinitePlace F} (hw : w.IsReal) (r : ℝ) (hr : r ≠ 0) :
    ‖((archRealUnit hw r hr : (w.Completion)ˣ) : w.Completion)‖ = |r| := by
  rw [← (isometry_extensionEmbeddingOfIsReal hw).norm_map_of_map_zero (map_zero _), archRealUnit_coe,
    ← ringEquivRealOfIsReal_apply hw, RingEquiv.apply_symm_apply, Real.norm_eq_abs]

private theorem archUnitHom_archRealUnit_of_isArchCompAt {μ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ} {w : InfinitePlace F}
    (hw : w.IsReal) {u : ℂ} {a : ℤ} (h : IsArchCompAt F μ w u a) (r : ℝ) (hr : 0 < r) :
    ((μ (archUnitHom w (archRealUnit hw r hr.ne')) : ℂˣ) : ℂ) = (r : ℂ) ^ u := by
  have hx := h (archRealUnit hw r hr.ne')
  rw [archLocalChar_apply] at hx
  have hm : w.mult = 1 := InfinitePlace.mult_isReal ⟨w, hw⟩
  rw [archUnitHom_apply, hx, norm_archRealUnit, extensionEmbedding_archRealUnit, abs_of_pos hr, hm, Nat.cast_one,
    one_mul, div_self (Complex.ofReal_ne_zero.mpr hr.ne'), _root_.one_zpow, mul_one]

end RealUnits

section Naturality

private theorem archRealGLAt_diagOne {w : InfinitePlace F} (hw : w.IsReal) (r : ℝ) (hr : r ≠ 0) :
    archRealGLAt hw (diagOne (Units.mk0 r hr)) = diagOne (archUnitHom w (archRealUnit hw r hr)) := by
  set m : GL (Fin 2) w.Completion := glEquivOfRingEquiv (ringEquivRealOfIsReal hw).symm (diagOne (Units.mk0 r hr))
    with hm
  refine eq_of_glArch_eq_of_glFin_eq ?_ ?_
  · have h1 : AdelicLevel.glArch (𝓞 F) F (archRealGLAt hw (diagOne (Units.mk0 r hr))) = archGLIncl F w m :=
      glArch_adelicArchGLIncl F _
    rw [h1]
    apply Units.ext
    ext i j
    rw [AdelicLevel.glArch_apply, diagOne_coe_apply]
    change archMatrixUpdate F w (m : Matrix (Fin 2) (Fin 2) w.Completion) i j = _
    funext v
    by_cases hv : v = w
    · subst hv
      rw [archMatrixUpdate_apply_self, hm, glEquivOfRingEquiv_apply_entry, diagOne_coe_apply]
      fin_cases i <;> fin_cases j <;> simp [archUnitHom_apply, archCentralUnit, archRealUnit_coe] <;> rfl
    · rw [archMatrixUpdate_apply_of_ne F w _ i j hv]
      fin_cases i <;> fin_cases j <;> simp [archUnitHom_apply, archCentralUnit, Matrix.one_apply, hv] <;> rfl
  · have h2 : AdelicLevel.glFin (𝓞 F) F (archRealGLAt hw (diagOne (Units.mk0 r hr))) = 1 := glFin_adelicArchGLIncl F _
    rw [h2]
    apply Units.ext
    ext i j
    rw [AdelicLevel.glFin_apply, diagOne_coe_apply]
    fin_cases i <;> fin_cases j <;> simp [archUnitHom_apply, archCentralUnit, Matrix.one_apply] <;> rfl

private theorem archRealGLAt_scalar {w : InfinitePlace F} (hw : w.IsReal) (r : ℝ) (hr : r ≠ 0) :
    archRealGLAt hw (Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.mk0 r hr))
      = centralScalar (𝓞 F) F (archUnitHom w (archRealUnit hw r hr)) := by
  set m : GL (Fin 2) w.Completion :=
    glEquivOfRingEquiv (ringEquivRealOfIsReal hw).symm (Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.mk0 r hr))
    with hm
  refine eq_of_glArch_eq_of_glFin_eq ?_ ?_
  · have h1 : AdelicLevel.glArch (𝓞 F) F
        (archRealGLAt hw (Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.mk0 r hr))) = archGLIncl F w m :=
      glArch_adelicArchGLIncl F _
    rw [h1]
    apply Units.ext
    ext i j
    rw [AdelicLevel.glArch_apply, centralScalar_val]
    change archMatrixUpdate F w (m : Matrix (Fin 2) (Fin 2) w.Completion) i j = _
    funext v
    by_cases hv : v = w
    · subst hv
      rw [archMatrixUpdate_apply_self, hm, glEquivOfRingEquiv_apply_entry]
      fin_cases i <;> fin_cases j <;>
        simp [Matrix.GeneralLinearGroup.scalar, archUnitHom_apply, archCentralUnit, archRealUnit_coe] <;> rfl
    · rw [archMatrixUpdate_apply_of_ne F w _ i j hv]
      fin_cases i <;> fin_cases j <;> simp [archUnitHom_apply, archCentralUnit, Matrix.one_apply, hv] <;> rfl
  · have h2 : AdelicLevel.glFin (𝓞 F) F
        (archRealGLAt hw (Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.mk0 r hr))) = 1 :=
      glFin_adelicArchGLIncl F _
    rw [h2]
    apply Units.ext
    ext i j
    rw [AdelicLevel.glFin_apply, centralScalar_val]
    fin_cases i <;> fin_cases j <;> simp [archUnitHom_apply, archCentralUnit, Matrix.one_apply] <;> rfl

end Naturality

section Torus

private theorem sqrt_ne_zero_of_pos
    {y : ℝ} (hy : 0 < y) : (Real.sqrt y)⁻¹ ≠ 0 := inv_ne_zero (Real.sqrt_pos.mpr hy).ne'

private theorem splitTorusGL2_half_log_eq (y : ℝ) (hy : 0 < y) :
    splitTorusGL2 (Real.log y / 2)
      = Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.mk0 (Real.sqrt y)⁻¹ (sqrt_ne_zero_of_pos hy))
          * diagOne (Units.mk0 y hy.ne') := by
  have hsq : Real.exp (Real.log y / 2) = Real.sqrt y := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hy, div_eq_mul_one_div]
  apply Units.ext
  show (!![Real.exp (Real.log y / 2), 0; 0, Real.exp (-(Real.log y / 2))] : Matrix (Fin 2) (Fin 2) ℝ)
    = Matrix.scalar (Fin 2) (Real.sqrt y)⁻¹ * Matrix.diagonal ![y, 1]
  rw [Real.exp_neg, hsq]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, inv_mul_eq_div, Real.div_sqrt]

private theorem whittakerCoefficient_archRealGLAt_splitTorusGL2_half_log (D : Set (AdelicGL2 (𝓞 F) F))
    (U : Ideal (𝓞 F) → Subgroup (AdelicGL2 (𝓞 F) F)) (gen : HeightOneSpectrum (𝓞 F) → AdelicGL2 (𝓞 F) F)
    (B : Set (AdeleRing (𝓞 F) F)) (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ)
    {ξ : (productionPinsOf F D U gen B).Z →* ℂˣ} {φ : AdelicGL2 (𝓞 F) F → ℂ}
    (hφ : IsLsXiFunction (𝓞 F) F (productionPinsOf F D U gen B).Z ξ φ)
    {w : InfinitePlace F} (hw : w.IsReal) (α : F) (y : ℝ) (hy : 0 < y) (g : AdelicGL2 (𝓞 F) F) :
    whittakerCoefficient F (productionPinsOf F D U gen B) ψ φ α
        (archRealGLAt hw (splitTorusGL2 (Real.log y / 2)) * g)
      = ((ξ ⟨archUnitHom w (archRealUnit hw (Real.sqrt y)⁻¹ (sqrt_ne_zero_of_pos hy)), Subgroup.mem_top _⟩ : ℂˣ) : ℂ)
          * whittakerCoefficient F (productionPinsOf F D U gen B) ψ φ α
              (diagOne (archUnitHom w (archRealUnit hw y hy.ne')) * g) := by
  rw [splitTorusGL2_half_log_eq y hy, map_mul, archRealGLAt_scalar, archRealGLAt_diagOne, mul_assoc]
  exact whittakerCoefficient_centralScalar_mul F (productionPinsOf F D U gen B) ψ hφ
    ⟨archUnitHom w (archRealUnit hw (Real.sqrt y)⁻¹ (sqrt_ne_zero_of_pos hy)), Subgroup.mem_top _⟩ α _

private theorem whittakerCoefficient_archRealGLAt_splitTorusGL2_half_log_of_isArchCompAt (D : Set (AdelicGL2 (𝓞 F) F))
    (U : Ideal (𝓞 F) → Subgroup (AdelicGL2 (𝓞 F) F)) (gen : HeightOneSpectrum (𝓞 F) → AdelicGL2 (𝓞 F) F)
    (B : Set (AdeleRing (𝓞 F) F)) (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ)
    {ξ : (productionPinsOf F D U gen B).Z →* ℂˣ} {φ : AdelicGL2 (𝓞 F) F → ℂ}
    (hφ : IsLsXiFunction (𝓞 F) F (productionPinsOf F D U gen B).Z ξ φ)
    {w : InfinitePlace F} (hw : w.IsReal) {u : ℂ} {a : ℤ}
    (hcen : IsArchCompAt F (ξ.comp Subgroup.topEquiv.symm.toMonoidHom) w u a)
    (α : F) (y : ℝ) (hy : 0 < y) (g : AdelicGL2 (𝓞 F) F) :
    whittakerCoefficient F (productionPinsOf F D U gen B) ψ φ α
        (archRealGLAt hw (splitTorusGL2 (Real.log y / 2)) * g)
      = (((Real.sqrt y)⁻¹ : ℝ) : ℂ) ^ u
          * whittakerCoefficient F (productionPinsOf F D U gen B) ψ φ α
              (diagOne (archUnitHom w (archRealUnit hw y hy.ne')) * g) := by
  rw [whittakerCoefficient_archRealGLAt_splitTorusGL2_half_log F D U gen B ψ hφ hw α y hy g]
  congr 1
  exact archUnitHom_archRealUnit_of_isArchCompAt hw hcen _ (inv_pos.mpr (Real.sqrt_pos.mpr hy))

end Torus

end Peeling

section NegativeSheet

private theorem J_mul_splitTorusGL2_half_log_eq (y : ℝ) (hy : 0 < y) :
    UpperHalfPlane.J * splitTorusGL2 (Real.log y / 2)
      = Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.mk0 (Real.sqrt y)⁻¹ (sqrt_ne_zero_of_pos hy))
          * diagOne (Units.mk0 (-y) (neg_ne_zero.mpr hy.ne')) := by
  have hsq : Real.exp (Real.log y / 2) = Real.sqrt y := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hy, div_eq_mul_one_div]
  apply Units.ext
  show (!![(-1 : ℝ), 0; 0, 1] : Matrix (Fin 2) (Fin 2) ℝ)
        * !![Real.exp (Real.log y / 2), 0; 0, Real.exp (-(Real.log y / 2))]
      = Matrix.scalar (Fin 2) (Real.sqrt y)⁻¹ * Matrix.diagonal ![-y, 1]
  rw [Real.exp_neg, hsq]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, inv_mul_eq_div, Real.div_sqrt]

private theorem whittakerCoefficient_archRealGLAt_J_mul_splitTorusGL2_half_log_of_isArchCompAt
    (D : Set (AdelicGL2 (𝓞 F) F))
    (U : Ideal (𝓞 F) → Subgroup (AdelicGL2 (𝓞 F) F)) (gen : HeightOneSpectrum (𝓞 F) → AdelicGL2 (𝓞 F) F)
    (B : Set (AdeleRing (𝓞 F) F)) (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ)
    {ξ : (productionPinsOf F D U gen B).Z →* ℂˣ} {φ : AdelicGL2 (𝓞 F) F → ℂ}
    (hφ : IsLsXiFunction (𝓞 F) F (productionPinsOf F D U gen B).Z ξ φ)
    {w : InfinitePlace F} (hw : w.IsReal) {u : ℂ} {a : ℤ}
    (hcen : IsArchCompAt F (ξ.comp Subgroup.topEquiv.symm.toMonoidHom) w u a)
    (α : F) (y : ℝ) (hy : 0 < y) (g : AdelicGL2 (𝓞 F) F) :
    whittakerCoefficient F (productionPinsOf F D U gen B) ψ φ α
        (archRealGLAt hw (UpperHalfPlane.J * splitTorusGL2 (Real.log y / 2)) * g)
      = (((Real.sqrt y)⁻¹ : ℝ) : ℂ) ^ u
          * whittakerCoefficient F (productionPinsOf F D U gen B) ψ φ α
              (diagOne (archUnitHom w (archRealUnit hw (-y) (neg_ne_zero.mpr hy.ne'))) * g) := by
  rw [J_mul_splitTorusGL2_half_log_eq y hy, map_mul, archRealGLAt_scalar, archRealGLAt_diagOne, mul_assoc,
    whittakerCoefficient_centralScalar_mul F (productionPinsOf F D U gen B) ψ hφ
      ⟨archUnitHom w (archRealUnit hw (Real.sqrt y)⁻¹ (sqrt_ne_zero_of_pos hy)), Subgroup.mem_top _⟩ α]
  congr 1
  exact archUnitHom_archRealUnit_of_isArchCompAt hw hcen _ (inv_pos.mpr (Real.sqrt_pos.mpr hy))

end NegativeSheet

section ArchUnitNorm

private theorem ideleNorm_archUnitHom_archRealUnit_rat {w : InfinitePlace ℚ} (hw : w.IsReal) (r : ℝ) (hr : r ≠ 0) :
    ideleNorm ℚ (archUnitHom w (archRealUnit hw r hr)) = |r| := by
  rw [NumberField.TateGlobal.ideleNorm_eq_prod_norm_infinitePlace_pow_mult_of_snd_eq_one ℚ _ rfl,
    Fintype.prod_subsingleton _ w]
  have hm : w.mult = 1 := InfinitePlace.mult_isReal ⟨w, hw⟩
  rw [hm, pow_one, archUnitHom_apply]
  rw [archCentralUnit_fst_self, norm_archRealUnit]

private theorem archUnitHom_archRealUnit_coe_snd {w : InfinitePlace ℚ} (hw : w.IsReal) (r : ℝ) (hr : r ≠ 0) :
    ((archUnitHom w (archRealUnit hw r hr) : (AdeleRing (𝓞 ℚ) ℚ)ˣ) : AdeleRing (𝓞 ℚ) ℚ).2 = 1 := rfl

end ArchUnitNorm

section GrowthTransfer

private theorem norm_inv_sqrt_cpow (u : ℂ) (y : ℝ) (hy : 0 < y) :
    ‖(((Real.sqrt y)⁻¹ : ℝ) : ℂ) ^ u‖ = y ^ (-(u.re / 2)) := by
  rw [Complex.norm_cpow_eq_rpow_re_of_pos (inv_pos.mpr (Real.sqrt_pos.mpr hy)), Real.sqrt_eq_rpow,
    ← Real.rpow_neg hy.le, ← Real.rpow_mul hy.le]
  congr 1
  ring

private theorem exists_forall_norm_cpow_mul_le_of_forall_norm_le (u : ℂ) (G : ℝ → ℂ) (C M : ℝ)
    (hG : ∀ y : ℝ, 0 < y → ‖G y‖ ≤ C * y ^ M) :
    ∃ C' N : ℝ, ∀ y : ℝ, 1 ≤ y → ‖(((Real.sqrt y)⁻¹ : ℝ) : ℂ) ^ u * G y‖ ≤ C' * y ^ N := by
  refine ⟨|C|, M + -(u.re / 2), fun y hy => ?_⟩
  have hy0 : 0 < y := lt_of_lt_of_le one_pos hy
  rw [norm_mul, norm_inv_sqrt_cpow u y hy0, Real.rpow_add hy0, mul_comm (y ^ M), ← mul_assoc, mul_comm |C|,
    mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg hy0.le _)
  exact (hG y hy0).trans (mul_le_mul_of_nonneg_right (le_abs_self C) (Real.rpow_nonneg hy0.le _))

end GrowthTransfer

section TorusGeneral

variable {F}

private theorem splitTorusGL2_eq_scalar_mul_diagOne (t : ℝ) :
    splitTorusGL2 t
      = Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.mk0 (Real.exp (-t)) (Real.exp_pos _).ne')
          * diagOne (Units.mk0 (Real.exp (2 * t)) (Real.exp_pos _).ne') := by
  have h : Real.exp (-t) * Real.exp (2 * t) = Real.exp t := by
    rw [← Real.exp_add]
    congr 1
    ring
  apply Units.ext
  show (!![Real.exp t, 0; 0, Real.exp (-t)] : Matrix (Fin 2) (Fin 2) ℝ)
    = Matrix.scalar (Fin 2) (Real.exp (-t)) * Matrix.diagonal ![Real.exp (2 * t), 1]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, h]

private theorem archRealUnit_mul {w : InfinitePlace F} (hw : w.IsReal) (r s : ℝ) (hr : r ≠ 0) (hs : s ≠ 0) :
    archRealUnit hw (r * s) (mul_ne_zero hr hs) = archRealUnit hw r hr * archRealUnit hw s hs := by
  apply Units.ext
  simp only [Units.val_mul, archRealUnit_coe, map_mul]

end TorusGeneral

section ReferenceDatum

variable {F}

private theorem apply_unipotentGL2_algebraMap_mul_of_isIsotypicCuspFormAt {pins : CarrierPins F} {ξ : pins.Z →* ℂˣ}
    {N : Ideal (𝓞 F)} {S : Finset (HeightOneSpectrum (𝓞 F))} {Φ : HeckeEigensystem F ℂ} {φ : AdelicGL2 (𝓞 F) F → ℂ}
    (h : IsIsotypicCuspFormAt F pins ξ N S Φ φ) (β : F) (g : AdelicGL2 (𝓞 F) F) :
    φ (unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) β) * g) = φ g := by
  rw [← globalPoints_unipotentGL2, (isLsXiFunction_of_isIsotypicCuspFormAt h).left_invariant]

private theorem whittakerCoefficient_zero_of_isIsotypicCuspFormAt
    {pins : CarrierPins F} {ξ : pins.Z →* ℂˣ} {N : Ideal (𝓞 F)}
    {S : Finset (HeightOneSpectrum (𝓞 F))} {Φ : HeckeEigensystem F ℂ} {φ : AdelicGL2 (𝓞 F) F → ℂ}
    (h : IsIsotypicCuspFormAt F pins ξ N S Φ φ) (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (g : AdelicGL2 (𝓞 F) F) :
    whittakerCoefficient F pins ψ φ 0 g = 0 := by
  rw [whittakerCoefficient_zero_eq_constantTerm]
  exact h.smoothCusp.1.2 g

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

private theorem exists_whittakerCoefficient_one_ne_zero_of_isIsotypicCuspFormAt (D : Set (AdelicGL2 (𝓞 ℚ) ℚ))
    (U : Ideal (𝓞 ℚ) → Subgroup (AdelicGL2 (𝓞 ℚ) ℚ)) (gen : HeightOneSpectrum (𝓞 ℚ) → AdelicGL2 (𝓞 ℚ) ℚ)
    (ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ) (hψ : IsGlobalAddChar ℚ ψ) {w : InfinitePlace ℚ} (hw : w.IsReal)
    {ξ : (productionPinsOf ℚ D U gen (adelicBox ℚ)).Z →* ℂˣ} {N : Ideal (𝓞 ℚ)} {S : Finset (HeightOneSpectrum (𝓞 ℚ))}
    {Φ : HeckeEigensystem ℚ ℂ} {φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ}
    (hiso : IsIsotypicCuspFormAt ℚ (productionPinsOf ℚ D U gen (adelicBox ℚ)) ξ N S Φ φ)
    (hsm : IsArchSmoothAt hw φ) (hne : φ ≠ 0) :
    ∃ g : AdelicGL2 (𝓞 ℚ) ℚ, whittakerCoefficient ℚ (productionPinsOf ℚ D U gen (adelicBox ℚ)) ψ φ 1 g ≠ 0 := by
  obtain ⟨g₀, hg₀⟩ := Function.ne_iff.mp hne
  have hsum := (whittakerCoefficientIntegrable_and_summable_of_isKfSmooth_of_contDiff D U gen ψ hψ φ
    (fun β g => (apply_unipotentGL2_algebraMap_mul_of_isIsotypicCuspFormAt hiso) β g) hiso.smoothCusp.2
    (fun g => contDiff_two_unipotentGL2_ratArchLine_mul_of_isArchSmoothAt hw hsm g)).2 g₀
  exact exists_whittakerCoefficient_one_ne_zero ℚ D U gen ψ hψ φ
    (isLsXiFunction_of_isIsotypicCuspFormAt hiso).left_invariant g₀
    ((whittakerCoefficient_zero_of_isIsotypicCuspFormAt hiso) ψ g₀)
    (hiso.continuous.comp ((continuous_unipotentGL2 (R := AdeleRing (𝓞 ℚ) ℚ)).mul continuous_const)) hsum hg₀

end ReferenceDatumRat

section RealIwasawa

private theorem det_rotMatrix (c' d' : ℝ) (h : c' ^ 2 + d' ^ 2 = 1) :
    (!![d', -c'; c', d'] : Matrix (Fin 2) (Fin 2) ℝ).det = 1 := by
  rw [Matrix.det_fin_two_of]
  linear_combination h

private noncomputable def rotOf (c' d' : ℝ) (h : c' ^ 2 + d' ^ 2 = 1) : GL (Fin 2) ℝ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![d', -c'; c', d'] (by rw [det_rotMatrix c' d' h]; exact one_ne_zero)

private theorem rotOf_coe (c' d' : ℝ) (h : c' ^ 2 + d' ^ 2 = 1) :
    ((rotOf c' d' h : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = !![d', -c'; c', d'] := rfl

private theorem rotOf_mem_rowIsometrySubgroup₀ (c' d' : ℝ) (h : c' ^ 2 + d' ^ 2 = 1) :
    rotOf c' d' h ∈ rowIsometrySubgroup₀ ℝ := by
  rw [mem_rowIsometrySubgroup₀_iff]
  refine ⟨by rw [rotOf_coe]; exact det_rotMatrix c' d' h, ?_, ?_⟩
  · rw [rotOf_coe, det_rotMatrix c' d' h, norm_one]
  · intro x y
    rw [rotOf_coe]
    simp
    linear_combination (x ^ 2 + y ^ 2) * h

private theorem exists_unipotentGL2_mul_scalar_mul_diagOne_mul_eq (p : GL (Fin 2) ℝ) :
    ∃ (x : ℝ) (δ v : ℝˣ) (k : rowIsometrySubgroup₀ ℝ),
      unipotentGL2 x * Matrix.GeneralLinearGroup.scalar (Fin 2) δ * diagOne v * (k : GL (Fin 2) ℝ) = p := by
  have hdet : (p : Matrix (Fin 2) (Fin 2) ℝ).det ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det (p : Matrix (Fin 2) (Fin 2) ℝ)).mp p.isUnit).ne_zero
  obtain ⟨c, hc⟩ : ∃ c : ℝ, (p : Matrix (Fin 2) (Fin 2) ℝ) 1 0 = c := ⟨_, rfl⟩
  obtain ⟨d, hd⟩ : ∃ d : ℝ, (p : Matrix (Fin 2) (Fin 2) ℝ) 1 1 = d := ⟨_, rfl⟩
  have hcd : 0 < c ^ 2 + d ^ 2 := by
    by_contra hle
    have hc0 : c = 0 := by nlinarith [sq_nonneg c, sq_nonneg d]
    have hd0 : d = 0 := by nlinarith [sq_nonneg c, sq_nonneg d]
    apply hdet
    rw [Matrix.det_fin_two, hc, hd, hc0, hd0]
    ring
  obtain ⟨ρ, hρdef⟩ : ∃ ρ : ℝ, ρ = Real.sqrt (c ^ 2 + d ^ 2) := ⟨_, rfl⟩
  have hρ : 0 < ρ := hρdef ▸ Real.sqrt_pos.mpr hcd
  have hρ0 : ρ ≠ 0 := hρ.ne'
  have hρ2 : ρ ^ 2 = c ^ 2 + d ^ 2 := by rw [hρdef]; exact Real.sq_sqrt hcd.le
  have h1 : (c / ρ) ^ 2 + (d / ρ) ^ 2 = 1 := by
    rw [div_pow, div_pow, ← add_div, ← hρ2, div_self (pow_ne_zero 2 hρ0)]

  obtain ⟨M, hM⟩ : ∃ M : Matrix (Fin 2) (Fin 2) ℝ,
      M = (p : Matrix (Fin 2) (Fin 2) ℝ) * !![d / ρ, c / ρ; -(c / ρ), d / ρ] := ⟨_, rfl⟩
  have hM10 : M 1 0 = 0 := by
    rw [hM]
    simp [Matrix.mul_apply, Fin.sum_univ_two, hc, hd]
    ring
  have hM11 : M 1 1 = ρ := by
    rw [hM]
    simp [Matrix.mul_apply, Fin.sum_univ_two, hc, hd]
    field_simp
    linarith [hρ2]
  have hMdet : M.det = (p : Matrix (Fin 2) (Fin 2) ℝ).det := by
    rw [hM, Matrix.det_mul, Matrix.det_fin_two_of]
    linear_combination (p : Matrix (Fin 2) (Fin 2) ℝ).det * h1
  have hα : M 0 0 ≠ 0 := by
    intro h0
    apply hdet
    rw [← hMdet, Matrix.det_fin_two, h0, hM10]
    ring
  refine ⟨M 0 1 / ρ, Units.mk0 ρ hρ0, Units.mk0 (M 0 0 / ρ) (div_ne_zero hα hρ0),
    ⟨rotOf (c / ρ) (d / ρ) h1, rotOf_mem_rowIsometrySubgroup₀ _ _ h1⟩, ?_⟩
  apply Units.ext
  have hkk : (!![d / ρ, c / ρ; -(c / ρ), d / ρ] : Matrix (Fin 2) (Fin 2) ℝ)
      * !![d / ρ, -(c / ρ); c / ρ, d / ρ] = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> first | ring1 | linear_combination h1
  have hp : (p : Matrix (Fin 2) (Fin 2) ℝ) = M * !![d / ρ, -(c / ρ); c / ρ, d / ρ] := by
    rw [hM, Matrix.mul_assoc, hkk, Matrix.mul_one]
  show (!![(1 : ℝ), M 0 1 / ρ; 0, 1] : Matrix (Fin 2) (Fin 2) ℝ) * Matrix.scalar (Fin 2) ρ
      * Matrix.diagonal ![M 0 0 / ρ, 1] * !![d / ρ, -(c / ρ); c / ρ, d / ρ] = (p : Matrix (Fin 2) (Fin 2) ℝ)
  rw [hp]
  congr 1
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, hM10, hM11] <;> field_simp

end RealIwasawa

section ReferenceDatumIwasawa

variable {F}

private theorem norm_ringEquivRealOfIsReal_symm_real {w : InfinitePlace F} (hw : w.IsReal) (r : ℝ) :
    ‖(ringEquivRealOfIsReal hw).symm r‖ = ‖r‖ := by
  rw [← (isometry_extensionEmbeddingOfIsReal hw).norm_map_of_map_zero (map_zero _), ← ringEquivRealOfIsReal_apply hw,
    RingEquiv.apply_symm_apply]

private noncomputable def rotAt {w : InfinitePlace F} (hw : w.IsReal) :
    rowIsometrySubgroup₀ ℝ →* rowIsometrySubgroup₀ w.Completion :=
  rowIsometrySubgroup₀Map (ringEquivRealOfIsReal hw).symm (norm_ringEquivRealOfIsReal_symm_real hw)

private theorem archRealGLAt_coe_eq_adelicArchGLInclAt_rotAt {w : InfinitePlace F} (hw : w.IsReal)
    (k : rowIsometrySubgroup₀ ℝ) :
    archRealGLAt hw (k : GL (Fin 2) ℝ)
      = adelicArchGLInclAt F w ((rotAt hw k : rowIsometrySubgroup₀ w.Completion) : GL (Fin 2) w.Completion) :=
  rfl

end ReferenceDatumIwasawa

section NegativeSheetVanishing

open Complex in

private theorem inv_sqrt_cpow_mul_sqrt_cpow (u : ℂ) {y : ℝ} (hy : 0 < y) :
    (((Real.sqrt y)⁻¹ : ℝ) : ℂ) ^ u * ((Real.sqrt y : ℝ) : ℂ) ^ u = 1 := by
  rw [← mul_cpow_ofReal_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg y)) (Real.sqrt_nonneg y) u, ← ofReal_mul,
    inv_mul_cancel₀ (Real.sqrt_pos.mpr hy).ne', ofReal_one, one_cpow]

private noncomputable def loweringSolution (k₀ : ℤ) (y : ℝ) : ℂ :=
  (y : ℂ) ^ ((k₀ : ℂ) / 2) * Complex.exp (-(2 * (π : ℂ)) * (y : ℂ))

private theorem hasDerivAt_loweringSolution (k₀ : ℤ) {y : ℝ} (hy : 0 < y) :
    HasDerivAt (loweringSolution k₀)
      ((k₀ : ℂ) / 2 * (y : ℂ) ^ ((k₀ : ℂ) / 2 - 1) * 1 * Complex.exp (-(2 * (π : ℂ)) * (y : ℂ))
        + (y : ℂ) ^ ((k₀ : ℂ) / 2) * (Complex.exp (-(2 * (π : ℂ)) * (y : ℂ)) * (-(2 * (π : ℂ)) * 1))) y := by
  have h1 : HasDerivAt (fun t : ℝ => (t : ℂ) ^ ((k₀ : ℂ) / 2)) ((k₀ : ℂ) / 2 * (y : ℂ) ^ ((k₀ : ℂ) / 2 - 1) * 1) y :=
    ((hasDerivAt_id (y : ℂ)).cpow_const (Complex.ofReal_mem_slitPlane.mpr hy)).comp_ofReal
  have h2 := ((hasDerivAt_id y).ofReal_comp.const_mul (-(2 * (π : ℂ)))).cexp
  exact h1.mul h2

private theorem loweringSolution_lowering (k₀ : ℤ) {y : ℝ} (hy : 0 < y) :
    2 * (y : ℂ) * deriv (loweringSolution k₀) y + (4 * (π : ℂ) * (y : ℂ) - (k₀ : ℂ)) * loweringSolution k₀ y = 0 := by
  have hy0 : (y : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hy.ne'
  rw [(hasDerivAt_loweringSolution k₀ hy).deriv, loweringSolution, Complex.cpow_sub _ _ hy0, Complex.cpow_one]
  field_simp
  ring

private theorem loweringSolution_one_ne_zero (k₀ : ℤ) : loweringSolution k₀ 1 ≠ 0 := by
  rw [loweringSolution, Complex.ofReal_one, Complex.one_cpow, one_mul]
  exact Complex.exp_ne_zero _

private theorem eq_zero_of_neg_of_lowering (u : ℂ) (k₀ : ℤ) (F : ℂ → ℂ) (fm : ℝ → ℂ)
    (hFm : ∀ t : ℝ, 0 < t → F (-(t : ℂ)) = ((Real.sqrt t : ℝ) : ℂ) ^ u * fm t)
    (hfm : DifferentiableOn ℝ fm (Set.Ioi 0))
    (hlowm : ∀ y : ℝ, 0 < y → 2 * (y : ℂ) * deriv fm y - (4 * (π : ℂ) * (y : ℂ) + (k₀ : ℂ)) * fm y = 0)
    (hgr : ∃ C N : ℝ, ∀ y : ℝ, 1 ≤ y → ‖fm y‖ ≤ C * y ^ N) :
    ∀ t : ℝ, t < 0 → F (t : ℂ) = 0 := by
  have hWp : ∀ t : ℝ, 0 < t →
      (fun z : ℂ => if 0 < z.re then ((Real.sqrt z.re : ℝ) : ℂ) ^ (u - 1 + 1) * loweringSolution k₀ z.re else F z)
          (t : ℂ)
        = ((Real.sqrt t : ℝ) : ℂ) ^ (u - 1 + 1) * loweringSolution k₀ t := by
    intro t ht
    simp only [Complex.ofReal_re, if_pos ht]
  have hWm : ∀ t : ℝ, 0 < t →
      (fun z : ℂ => if 0 < z.re then ((Real.sqrt z.re : ℝ) : ℂ) ^ (u - 1 + 1) * loweringSolution k₀ z.re else F z)
          (-(t : ℂ))
        = ((Real.sqrt t : ℝ) : ℂ) ^ (u - 1 + 1) * fm t := by
    intro t ht
    have hneg : ¬ 0 < (-(t : ℂ)).re := by
      simp only [Complex.neg_re, Complex.ofReal_re]
      exact not_lt.mpr (neg_nonpos.mpr ht.le)
    simp only [if_neg hneg, sub_add_cancel]
    exact hFm t ht
  have hfp : DifferentiableOn ℝ (loweringSolution k₀) (Set.Ioi 0) := fun t ht =>
    (hasDerivAt_loweringSolution k₀ ht).differentiableAt.differentiableWithinAt
  have hsplice := (LanglandsTunnell.mellin_whittakerProfile_eq_GammaC_of_lowering_eq_zero (u - 1) k₀
    (fun z : ℂ => if 0 < z.re then ((Real.sqrt z.re : ℝ) : ℂ) ^ (u - 1 + 1) * loweringSolution k₀ z.re else F z)
    (loweringSolution k₀) fm hWp hWm hfp hfm (fun y hy => loweringSolution_lowering k₀ hy) hlowm hgr
    ⟨1, one_pos, loweringSolution_one_ne_zero k₀⟩).1
  intro t ht
  have hneg : ¬ 0 < (t : ℂ).re := by
    rw [Complex.ofReal_re]
    exact not_lt.mpr ht.le
  simpa only [if_neg hneg] using hsplice t ht

end NegativeSheetVanishing

section IdeleSplit

private def archProjHom : AdeleRing (𝓞 F) F →* InfiniteAdeleRing F where
  toFun x := x.1
  map_one' := rfl
  map_mul' _ _ := rfl

private def finProjHom : AdeleRing (𝓞 F) F →* FiniteAdeleRing (𝓞 F) F where
  toFun x := x.2
  map_one' := rfl
  map_mul' _ _ := rfl

private noncomputable def archInclHomF : InfiniteAdeleRing F →* AdeleRing (𝓞 F) F where
  toFun x := (x, (1 : FiniteAdeleRing (𝓞 F) F))
  map_one' := rfl
  map_mul' _ _ := Prod.ext rfl (one_mul _).symm

variable {F}

private noncomputable def archPart (a : (AdeleRing (𝓞 F) F)ˣ) : (AdeleRing (𝓞 F) F)ˣ :=
  Units.map (archInclHomF F) (Units.map (archProjHom F) a)

private noncomputable def finPart (a : (AdeleRing (𝓞 F) F)ˣ) : (AdeleRing (𝓞 F) F)ˣ :=
  Units.map (finIncl (𝓞 F) F) (Units.map (finProjHom F) a)

private theorem archPart_coe (a : (AdeleRing (𝓞 F) F)ˣ) :
    ((archPart a : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F) = ((a : AdeleRing (𝓞 F) F).1, 1) := rfl

private theorem finPart_coe (a : (AdeleRing (𝓞 F) F)ˣ) :
    ((finPart a : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F) = (1, (a : AdeleRing (𝓞 F) F).2) := rfl

private theorem finPart_coe_fst
    (a : (AdeleRing (𝓞 F) F)ˣ) : ((finPart a : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).1 = 1 :=
  rfl

private theorem archPart_mul_finPart (a : (AdeleRing (𝓞 F) F)ˣ) : archPart a * finPart a = a := by
  apply Units.ext
  rw [Units.val_mul, archPart_coe, finPart_coe]
  exact Prod.ext (mul_one _) (one_mul _)

private theorem diagOne_mem_finiteAdelicGL2Subgroup_of_fst_eq_one (b : (AdeleRing (𝓞 F) F)ˣ)
    (hb : ((b : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).1 = 1) : diagOne b ∈ finiteAdelicGL2Subgroup F := by
  rw [mem_finiteAdelicGL2Subgroup_iff]
  apply Units.ext
  ext i j
  rw [glArch_apply, diagOne_coe_apply]
  fin_cases i <;> fin_cases j <;> simp [hb] <;> rfl

private theorem diagOne_finPart_mem (a : (AdeleRing (𝓞 F) F)ˣ) : diagOne (finPart a) ∈ finiteAdelicGL2Subgroup F :=
  diagOne_mem_finiteAdelicGL2Subgroup_of_fst_eq_one _ (finPart_coe_fst a)

end IdeleSplit

section IdeleSplitRat

private theorem idele_fst_apply_ne_zero (a : (AdeleRing (𝓞 ℚ) ℚ)ˣ) (w : InfinitePlace ℚ) :
    ((a : AdeleRing (𝓞 ℚ) ℚ).1 w) ≠ 0 := by
  have h : ((a : AdeleRing (𝓞 ℚ) ℚ).1 w) * (((a⁻¹ : (AdeleRing (𝓞 ℚ) ℚ)ˣ) : AdeleRing (𝓞 ℚ) ℚ).1 w) = 1 :=
    congrArg (fun x : AdeleRing (𝓞 ℚ) ℚ => x.1 w) a.mul_inv
  exact left_ne_zero_of_mul_eq_one h

private noncomputable def archReal {w : InfinitePlace ℚ} (hw : w.IsReal) (a : (AdeleRing (𝓞 ℚ) ℚ)ˣ) : ℝ :=
  ringEquivRealOfIsReal hw ((a : AdeleRing (𝓞 ℚ) ℚ).1 w)

private theorem archReal_ne_zero
    {w : InfinitePlace ℚ} (hw : w.IsReal) (a : (AdeleRing (𝓞 ℚ) ℚ)ˣ) : archReal hw a ≠ 0 := by
  unfold archReal
  exact (map_ne_zero_iff _ (ringEquivRealOfIsReal hw).injective).mpr (idele_fst_apply_ne_zero a w)

private theorem archPart_eq_archUnitHom_archRealUnit {w : InfinitePlace ℚ} (hw : w.IsReal) (a : (AdeleRing (𝓞 ℚ) ℚ)ˣ) :
    archPart a = archUnitHom w (archRealUnit hw (archReal hw a) (archReal_ne_zero hw a)) := by
  apply Units.ext
  rw [archPart_coe, archUnitHom_apply]
  refine Prod.ext (funext fun v => ?_) rfl
  change (a : AdeleRing (𝓞 ℚ) ℚ).1 v = _
  rw [Subsingleton.elim v w, archCentralUnit_fst_self, archRealUnit_coe, archReal, RingEquiv.symm_apply_apply]

private theorem eq_archUnitHom_archRealUnit_mul_finPart
    {w : InfinitePlace ℚ} (hw : w.IsReal) (a : (AdeleRing (𝓞 ℚ) ℚ)ˣ) :
    a = archUnitHom w (archRealUnit hw (archReal hw a) (archReal_ne_zero hw a)) * finPart a := by
  rw [← archPart_eq_archUnitHom_archRealUnit hw a, archPart_mul_finPart]

end IdeleSplitRat

end CoefficientFunction

section WeightTransferAndCasimirEquation

private theorem hasArchCharacterAt₀_whittakerCoefficient_fn (F : Type) [Field F] [NumberField F]
    (pins : CarrierPins F) (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (φ : AdelicGL2 (𝓞 F) F → ℂ) (α : F)
    (w : InfinitePlace F) (χ : rowIsometrySubgroup₀ w.Completion →* ℂˣ)
    (hφ : HasArchCharacterAt₀ F w χ φ) :
    HasArchCharacterAt₀ F w χ (whittakerCoefficient F pins ψ φ α) := by
  intro k g
  unfold whittakerCoefficient
  rw [← integral_const_mul]
  congr 1
  funext x
  rw [show unipotentGL2 x * (g * adelicArchGLInclAt F w (k : GL (Fin 2) w.Completion))
        = unipotentGL2 x * g * adelicArchGLInclAt F w (k : GL (Fin 2) w.Completion) from
      (mul_assoc _ _ _).symm,
    hφ k (unipotentGL2 x * g), mul_assoc]

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

private theorem isArchSmoothAt_and_archCasimirAt_whittakerCoefficient_eq_smul
    (D : Set (AdelicGL2 (𝓞 ℚ) ℚ)) (U : Ideal (𝓞 ℚ) → Subgroup (AdelicGL2 (𝓞 ℚ) ℚ))
    (gen : HeightOneSpectrum (𝓞 ℚ) → AdelicGL2 (𝓞 ℚ) ℚ)
    (ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ) (hψ : IsGlobalAddChar ℚ ψ)
    (w : InfinitePlace ℚ) (hw : w.IsReal)
    (φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ) (hsm : IsArchSmoothAt hw φ)
    (hconv : ∃ α : AdelicGL2 (𝓞 ℚ) ℚ → ℂ, IsFactorizableTestFn ℚ α ∧ rightConv ℚ φ α = φ)
    (lam : ℂ) (hΩ : archCasimirAt hw φ = lam • φ) (α : ℚ) :
    IsArchSmoothAt hw (whittakerCoefficient ℚ (productionPinsOf ℚ D U gen (adelicBox ℚ)) ψ φ α) ∧
      archCasimirAt hw (whittakerCoefficient ℚ (productionPinsOf ℚ D U gen (adelicBox ℚ)) ψ φ α)
        = lam • whittakerCoefficient ℚ (productionPinsOf ℚ D U gen (adelicBox ℚ)) ψ φ α := by
  obtain ⟨h₁, -, h₃⟩ := isArchSmoothAt_whittakerCoefficient_and_archDerivAt_comm D U gen ψ hψ.continuous w hw φ
    hsm (isKfSmooth_of_exists_rightConv_eq ℚ φ hconv) α
  exact ⟨h₁, by rw [h₃, hΩ, whittakerCoefficient_smul_fn]⟩

section CoefficientODE

private theorem whittaker_ode_splitTorus_whittakerCoefficient_one_of_isIsotypicCuspFormAt
    (D : Set (AdelicGL2 (𝓞 ℚ) ℚ)) (U : Ideal (𝓞 ℚ) → Subgroup (AdelicGL2 (𝓞 ℚ) ℚ))
    (gen : HeightOneSpectrum (𝓞 ℚ) → AdelicGL2 (𝓞 ℚ) ℚ)
    (ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ) (hψ : IsGlobalAddChar ℚ ψ) {w : InfinitePlace ℚ} (hw : w.IsReal)
    (hψr : ∀ x : InfiniteAdeleRing ℚ, (∀ w' : InfinitePlace ℚ, w' ≠ w → x w' = 0) →
      ψ (⟨x, 0⟩ : AdeleRing (𝓞 ℚ) ℚ) = Complex.exp (2 * Real.pi * Complex.I * extensionEmbedding w (x w)))
    {ξ : (productionPinsOf ℚ D U gen (adelicBox ℚ)).Z →* ℂˣ} {N : Ideal (𝓞 ℚ)} {S : Finset (HeightOneSpectrum (𝓞 ℚ))}
    {Φ : HeckeEigensystem ℚ ℂ} {φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ}
    (hiso : IsIsotypicCuspFormAt ℚ (productionPinsOf ℚ D U gen (adelicBox ℚ)) ξ N S Φ φ)
    (hconv : ∃ α : AdelicGL2 (𝓞 ℚ) ℚ → ℂ, IsFactorizableTestFn ℚ α ∧ rightConv ℚ φ α = φ)
    (hsm : IsArchSmoothAt hw φ) (ν : ℂ) (hΩ : archCasimirAt hw φ = (1 / 4 - ν ^ 2) • φ)
    (k₀ : ℤ) (hwt : HasArchCharacterAt₀ ℚ w (archWeightCharAt hw k₀) φ)
    (W : AdelicGL2 (𝓞 ℚ) ℚ → ℂ) (hW : W = whittakerCoefficient ℚ (productionPinsOf ℚ D U gen (adelicBox ℚ)) ψ φ 1)
    (g : AdelicGL2 (𝓞 ℚ) ℚ) (hg : AdelicLevel.glArch (𝓞 ℚ) ℚ g = 1) :
    (DifferentiableOn ℝ (fun y : ℝ => W (archRealGLAt hw (splitTorusGL2 (Real.log y / 2)) * g)) (Set.Ioi 0) ∧
      DifferentiableOn ℝ (deriv (fun y : ℝ => W (archRealGLAt hw (splitTorusGL2 (Real.log y / 2)) * g)))
        (Set.Ioi 0) ∧
      ∀ y : ℝ, 0 < y →
        (y : ℂ) ^ 2 * deriv (deriv (fun y : ℝ => W (archRealGLAt hw (splitTorusGL2 (Real.log y / 2)) * g))) y
            + (1 / 4 - ν ^ 2 + 2 * (π : ℂ) * ((k₀ : ℝ) : ℂ) * (y : ℂ) - 4 * (π : ℂ) ^ 2 * (y : ℂ) ^ 2)
              * W (archRealGLAt hw (splitTorusGL2 (Real.log y / 2)) * g) = 0) ∧
    (DifferentiableOn ℝ
        (fun y : ℝ => W (archRealGLAt hw (UpperHalfPlane.J * splitTorusGL2 (Real.log y / 2)) * g)) (Set.Ioi 0) ∧
      DifferentiableOn ℝ
        (deriv (fun y : ℝ => W (archRealGLAt hw (UpperHalfPlane.J * splitTorusGL2 (Real.log y / 2)) * g)))
        (Set.Ioi 0) ∧
      ∀ y : ℝ, 0 < y →
        (y : ℂ) ^ 2 * deriv (deriv
              (fun y : ℝ => W (archRealGLAt hw (UpperHalfPlane.J * splitTorusGL2 (Real.log y / 2)) * g))) y
            + (1 / 4 - ν ^ 2 + 2 * (π : ℂ) * (((-k₀ : ℤ) : ℝ) : ℂ) * (y : ℂ)
                - 4 * (π : ℂ) ^ 2 * (y : ℂ) ^ 2)
              * W (archRealGLAt hw (UpperHalfPlane.J * splitTorusGL2 (Real.log y / 2)) * g) = 0) := by
  subst hW
  obtain ⟨hWsm, hWΩ⟩ :=
    isArchSmoothAt_and_archCasimirAt_whittakerCoefficient_eq_smul D U gen ψ hψ w hw φ hsm hconv _ hΩ 1
  have hWk := hasArchCharacterAt₀_whittakerCoefficient_fn ℚ (productionPinsOf ℚ D U gen (adelicBox ℚ)) ψ φ 1 w _ hwt
  have hWψ := apply_archRealGLAt_unipotentGL2_mul_of_forall_unipotentGL2_mul ℚ ψ hw hψr
    (whittakerCoefficient ℚ (productionPinsOf ℚ D U gen (adelicBox ℚ)) ψ φ 1)
    (fun X g' => whittakerCoefficient_one_unipotentGL2_mul_of_isIsotypicCuspFormAt ℚ D U gen ψ hψ hiso X g')
  exact LanglandsTunnell.whittaker_ode_splitTorus_of_isArchSmoothAt_of_archCasimirAt_eq hw _ k₀ ν hWsm hWΩ hWk hWψ g hg

private theorem archCasimirAt_eq_of_laplaceEigenvalue_discrete {w : InfinitePlace ℚ} (hw : w.IsReal)
    {φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ} (u₀ : ℂ) (n : ℕ) (hn : 1 ≤ n)
    (h : archCasimirAt hw φ = (RealArchParam.discrete u₀ n hn).laplaceEigenvalue • φ) :
    archCasimirAt hw φ = (1 / 4 - ((n : ℂ) / 2) ^ 2) • φ := by
  rw [h, RealArchParam.laplaceEigenvalue_discrete]
  congr 1
  ring

private theorem archCasimirAt_eq_of_laplaceEigenvalue_principal {w : InfinitePlace ℚ} (hw : w.IsReal)
    {φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ} (u₁ : ℂ) (a₁ : ZMod 2) (u₂ : ℂ) (a₂ : ZMod 2)
    (h : archCasimirAt hw φ = (RealArchParam.principal u₁ a₁ u₂ a₂).laplaceEigenvalue • φ) :
    archCasimirAt hw φ = (1 / 4 - ((u₁ - u₂) / 2) ^ 2) • φ :=
  h

end CoefficientODE

section Separation

private theorem eq_div_mul_of_whittaker_ode_of_moderateGrowth (ν : ℂ) (k : ℝ) (f g : ℝ → ℂ)
    (hf : DifferentiableOn ℝ f (Set.Ioi 0)) (hf' : DifferentiableOn ℝ (deriv f) (Set.Ioi 0))
    (hfeq : ∀ y : ℝ, 0 < y →
        (y : ℂ) ^ 2 * deriv (deriv f) y
            + (1 / 4 - ν ^ 2 + 2 * (π : ℂ) * (k : ℂ) * (y : ℂ) - 4 * (π : ℂ) ^ 2 * (y : ℂ) ^ 2) * f y = 0)
    (hfgr : ∃ C N : ℝ, ∀ y : ℝ, 1 ≤ y → ‖f y‖ ≤ C * y ^ N)
    (hg : DifferentiableOn ℝ g (Set.Ioi 0)) (hg' : DifferentiableOn ℝ (deriv g) (Set.Ioi 0))
    (hgeq : ∀ y : ℝ, 0 < y →
        (y : ℂ) ^ 2 * deriv (deriv g) y
            + (1 / 4 - ν ^ 2 + 2 * (π : ℂ) * (k : ℂ) * (y : ℂ) - 4 * (π : ℂ) ^ 2 * (y : ℂ) ^ 2) * g y = 0)
    (hggr : ∃ C N : ℝ, ∀ y : ℝ, 1 ≤ y → ‖g y‖ ≤ C * y ^ N)
    (y₀ : ℝ) (hy₀ : 0 < y₀) (hf₀ : f y₀ ≠ 0) :
    ∀ y : ℝ, 0 < y → g y = g y₀ / f y₀ * f y := by
  obtain ⟨c₁, c₂, hc, hlin⟩ :=
    LanglandsTunnell.linearDependent_of_whittaker_ode_of_moderateGrowth_complexParam ν k f g hf hf' hfeq hfgr hg hg'
      hgeq hggr
  have hc₂ : c₂ ≠ 0 := by
    rintro rfl
    have h₀ := hlin y₀ hy₀
    rw [zero_mul, add_zero, mul_eq_zero] at h₀
    rcases h₀ with h₀ | h₀
    · exact hc (by simp [h₀])
    · exact hf₀ h₀
  have hprop : ∀ y : ℝ, 0 < y → g y = -(c₁ / c₂) * f y := by
    intro y hy
    have h := hlin y hy
    field_simp
    linear_combination h
  intro y hy
  rw [hprop y hy, hprop y₀ hy₀, mul_div_assoc, div_self hf₀, mul_one]

end Separation

end WeightTransferAndCasimirEquation

section ReferenceDatumOverRationals

section ReferenceDatumRat₂

private theorem exists_whittakerCoefficient_one_diagOne_archRealUnit_mul_ne_zero (D : Set (AdelicGL2 (𝓞 ℚ) ℚ))
    (U : Ideal (𝓞 ℚ) → Subgroup (AdelicGL2 (𝓞 ℚ) ℚ)) (gen : HeightOneSpectrum (𝓞 ℚ) → AdelicGL2 (𝓞 ℚ) ℚ)
    (ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ) (hψ : IsGlobalAddChar ℚ ψ) {w : InfinitePlace ℚ} (hw : w.IsReal)
    {ξ : (productionPinsOf ℚ D U gen (adelicBox ℚ)).Z →* ℂˣ} {N : Ideal (𝓞 ℚ)} {S : Finset (HeightOneSpectrum (𝓞 ℚ))}
    {Φ : HeckeEigensystem ℚ ℂ} {φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ}
    (hiso : IsIsotypicCuspFormAt ℚ (productionPinsOf ℚ D U gen (adelicBox ℚ)) ξ N S Φ φ)
    {χ : rowIsometrySubgroup₀ w.Completion →* ℂˣ} (hwt : HasArchCharacterAt₀ ℚ w χ φ) {g₀ : AdelicGL2 (𝓞 ℚ) ℚ}
    (hg₀ : whittakerCoefficient ℚ (productionPinsOf ℚ D U gen (adelicBox ℚ)) ψ φ 1 g₀ ≠ 0) :
    ∃ (r : ℝ) (hr : r ≠ 0) (t : AdelicGL2 (𝓞 ℚ) ℚ), t ∈ finiteAdelicGL2Subgroup ℚ ∧
      whittakerCoefficient ℚ (productionPinsOf ℚ D U gen (adelicBox ℚ)) ψ φ 1
        (diagOne (archUnitHom w (archRealUnit hw r hr)) * t) ≠ 0 := by
  obtain ⟨p, k'', hk'', hg⟩ := exists_eq_archRealGLAt_mul_of_glArch_eq_one_rat hw g₀
  obtain ⟨x, δ, v, k, hp⟩ := exists_unipotentGL2_mul_scalar_mul_diagOne_mul_eq p
  obtain ⟨X, -, -, hX⟩ := archRealGLAt_unipotentGL2_eq ℚ hw x
  refine ⟨v, v.ne_zero, k'', hk'', fun h0 => hg₀ ?_⟩
  have hW := hasArchCharacterAt₀_whittakerCoefficient_fn ℚ (productionPinsOf ℚ D U gen (adelicBox ℚ)) ψ φ 1 w χ hwt
  rw [hg, ← hp, ← Units.mk0_val δ δ.ne_zero, ← Units.mk0_val v v.ne_zero, map_mul, map_mul, map_mul, hX,
    archRealGLAt_scalar, archRealGLAt_diagOne, mul_assoc _ (archRealGLAt hw (k : GL (Fin 2) ℝ)) k'',
    archRealGLAt_mul_comm_of_glArch_eq_one hw _ hk'', ← mul_assoc, archRealGLAt_coe_eq_adelicArchGLInclAt_rotAt,
    hW (rotAt hw k), mul_assoc, mul_assoc]
  erw [whittakerCoefficient_one_unipotentGL2_mul_of_isIsotypicCuspFormAt ℚ D U gen ψ hψ hiso]
  rw [show whittakerCoefficient ℚ (productionPinsOf ℚ D U gen (adelicBox ℚ)) ψ φ 1
        (centralScalar (𝓞 ℚ) ℚ (archUnitHom w (archRealUnit hw (δ : ℝ) δ.ne_zero))
          * (diagOne (archUnitHom w (archRealUnit hw (v : ℝ) v.ne_zero)) * k''))
        = ((ξ ⟨archUnitHom w (archRealUnit hw (δ : ℝ) δ.ne_zero), Subgroup.mem_top _⟩ : ℂˣ) : ℂ)
          * whittakerCoefficient ℚ (productionPinsOf ℚ D U gen (adelicBox ℚ)) ψ φ 1
              (diagOne (archUnitHom w (archRealUnit hw (v : ℝ) v.ne_zero)) * k'') from
      whittakerCoefficient_centralScalar_mul ℚ _ ψ (isLsXiFunction_of_isIsotypicCuspFormAt hiso)
        ⟨archUnitHom w (archRealUnit hw (δ : ℝ) δ.ne_zero), Subgroup.mem_top _⟩ 1 _,
    h0, mul_zero, mul_zero, mul_zero]

end ReferenceDatumRat₂

end ReferenceDatumOverRationals

section PolynomialGrowthOfCoefficients

section CharChange

variable (F : Type) [Field F] [NumberField F]

private theorem whittakerCoefficient_one_eq_whittakerCoefficient_of_forall_eq_mul (pins : CarrierPins F)
    (ψ ψ₀ : AddChar (AdeleRing (𝓞 F) F) ℂ) (a : F)
    (hψ : ∀ x : AdeleRing (𝓞 F) F, ψ x = ψ₀ (algebraMap F (AdeleRing (𝓞 F) F) a * x))
    (φ : AdelicGL2 (𝓞 F) F → ℂ) (g : AdelicGL2 (𝓞 F) F) :
    whittakerCoefficient F pins ψ φ 1 g = whittakerCoefficient F pins ψ₀ φ a g := by
  unfold whittakerCoefficient
  simp only [hψ, map_one, one_mul, mul_neg]

end CharChange

section Translate

variable (F : Type) [Field F] [NumberField F]

private theorem whittakerCoefficient_fun_mul (pins : CarrierPins F) (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ)
    (φ : AdelicGL2 (𝓞 F) F → ℂ) (t : AdelicGL2 (𝓞 F) F) (α : F) (g : AdelicGL2 (𝓞 F) F) :
    whittakerCoefficient F pins ψ (fun h => φ (h * t)) α g = whittakerCoefficient F pins ψ φ α (g * t) := by
  unfold whittakerCoefficient
  simp only [mul_assoc]

variable {F}

private theorem exists_isFactorizableTestFn_rightConv_eq_fun_mul {φ α : AdelicGL2 (𝓞 F) F → ℂ}
    (hα : IsFactorizableTestFn F α) (hφ : rightConv F φ α = φ) (t : AdelicGL2 (𝓞 F) F) :
    ∃ α' : AdelicGL2 (𝓞 F) F → ℂ, IsFactorizableTestFn F α' ∧ rightConv F φ α' = fun h => φ (h * t) := by
  refine ⟨fun y => α (t⁻¹ * y), isFactorizableTestFn_comp_inv_mul_of_isFactorizableTestFn F α hα t, ?_⟩
  funext h
  rw [← rightConv_apply_mul_eq_rightConv_comp_inv_mul_apply F φ α h t, hφ]

end Translate

section ArchCut

private noncomputable def weightTypeFamilyRat (k : InfinitePlace ℚ → ℤ) : ArchTypeFamily ℚ :=
  ArchTypeFamily.ofChar ℚ fun w => archWeightCharAt (isReal_infinitePlace_rat w) (k w)

private theorem mem_archCutSubmodule_weightTypeFamilyRat {k : InfinitePlace ℚ → ℤ} {φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ}
    (hk : ∀ (w : InfinitePlace ℚ) (hw : w.IsReal), HasArchCharacterAt₀ ℚ w (archWeightCharAt hw (k w)) φ) :
    φ ∈ archCutSubmodule ℚ (weightTypeFamilyRat k) :=
  (mem_archCutSubmodule_ofChar_iff ℚ _ φ).mpr fun w => hk w (isReal_infinitePlace_rat w)

end ArchCut

section ArchCutTranslate

variable (F : Type) [Field F] [NumberField F]

private theorem commute_rowIsometryInclAt₀_of_mem_finiteAdelicGL2Subgroup {t : AdelicGL2 (𝓞 F) F}
    (ht : t ∈ finiteAdelicGL2Subgroup F) (w : InfinitePlace F) (k : rowIsometrySubgroup₀ w.Completion) :
    Commute t (rowIsometryInclAt₀ F w k) := by
  rw [mem_finiteAdelicGL2Subgroup_iff] at ht
  show t * rowIsometryInclAt₀ F w k = rowIsometryInclAt₀ F w k * t
  refine eq_of_glArch_eq_of_glFin_eq ?_ ?_
  · rw [map_mul, map_mul, ht, one_mul, mul_one]
  · rw [map_mul, map_mul, glFin_rowIsometryInclAt₀ F w k, one_mul, mul_one]

private theorem comp_mul_mem_archCutSubmodule_of_mem_finiteAdelicGL2Subgroup {tys : ArchTypeFamily F}
    {f : AdelicGL2 (𝓞 F) F → ℂ} (hf : f ∈ archCutSubmodule F tys) {t : AdelicGL2 (𝓞 F) F}
    (ht : t ∈ finiteAdelicGL2Subgroup F) :
    (fun x => f (x * t)) ∈ archCutSubmodule F tys := by
  rw [mem_archCutSubmodule_iff] at hf ⊢
  intro w
  refine Submodule.iSup_induction _
    (motive := fun f => (fun x => f (x * t)) ∈
      ⨆ i : Fin (tys.card w), archTypeSubmoduleAt F w (tys.rep w i)) (hf w) ?_ ?_ ?_
  · intro i f hfi
    exact le_iSup (fun j => archTypeSubmoduleAt F w (tys.rep w j)) i
      (comp_mul_mem_typeSubmodule_of_commute hfi t fun k =>
        commute_rowIsometryInclAt₀_of_mem_finiteAdelicGL2Subgroup F ht w k)
  · exact Submodule.zero_mem _
  · exact fun _ _ hu hv => Submodule.add_mem _ hu hv

end ArchCutTranslate

section IndexShift

variable (F : Type) [Field F] [NumberField F]

attribute [local instance] NumberField.AdelicHaar.isAddHaarMeasure_adelicAddHaar in

private theorem setIntegral_adelicBox_unipotent_globalPoints_mul_eq [Countable F]
    (ψ₀ : AddChar (AdeleRing (𝓞 F) F) ℂ) (hψ₀ : IsPrincipalInvariantAddChar F ψ₀)
    (φ : AdelicGL2 (𝓞 F) F → ℂ)
    (hinv : ∀ (γ : Matrix.GeneralLinearGroup (Fin 2) F) (g : AdelicGL2 (𝓞 F) F), φ (globalPoints (𝓞 F) F γ * g) = φ g)
    (hper : ∀ (b : F) (u : AdeleRing (𝓞 F) F) (g : AdelicGL2 (𝓞 F) F),
      φ (unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) b + u) * g) = φ (unipotentGL2 u * g))
    (a : F) (ha : a ≠ 0) (γ : Matrix.GeneralLinearGroup (Fin 2) F)
    (hγ : ∀ u : AdeleRing (𝓞 F) F,
      unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) a * u) * globalPoints (𝓞 F) F γ
        = globalPoints (𝓞 F) F γ * unipotentGL2 u)
    (h : AdelicGL2 (𝓞 F) F) :
    (letI := adeleBorel (𝓞 F) F
      ∫ x in adelicBox F, φ (unipotentGL2 x * (globalPoints (𝓞 F) F γ * h)) * ψ₀ (-x) ∂adelicAddHaar (𝓞 F) F)
      = (letI := adeleBorel (𝓞 F) F
        ∫ u in adelicBox F, φ (unipotentGL2 u * h) * ψ₀ (-(algebraMap F (AdeleRing (𝓞 F) F) a * u))
          ∂adelicAddHaar (𝓞 F) F) := by
  letI : MeasurableSpace (AdeleRing (𝓞 F) F) := adeleBorel (𝓞 F) F
  haveI : BorelSpace (AdeleRing (𝓞 F) F) := borelSpace_adeleBorel (𝓞 F) F
  set A : AdeleRing (𝓞 F) F := algebraMap F (AdeleRing (𝓞 F) F) a with hA
  have hcont : ∀ c : AdeleRing (𝓞 F) F, Measurable fun x : AdeleRing (𝓞 F) F => c * x :=
    fun c => (continuous_const.mul continuous_id).measurable
  let e : AdeleRing (𝓞 F) F ≃ᵐ AdeleRing (𝓞 F) F :=
    { toFun := fun x => A * x
      invFun := fun x => algebraMap F (AdeleRing (𝓞 F) F) a⁻¹ * x
      left_inv := fun x => by
        show algebraMap F (AdeleRing (𝓞 F) F) a⁻¹ * (algebraMap F (AdeleRing (𝓞 F) F) a * x) = x
        rw [← mul_assoc, ← map_mul, inv_mul_cancel₀ ha, map_one, one_mul]
      right_inv := fun x => by
        show algebraMap F (AdeleRing (𝓞 F) F) a * (algebraMap F (AdeleRing (𝓞 F) F) a⁻¹ * x) = x
        rw [← mul_assoc, ← map_mul, mul_inv_cancel₀ ha, map_one, one_mul]
      measurable_toFun := hcont A
      measurable_invFun := hcont _ }
  have hmp : MeasurePreserving e (adelicAddHaar (𝓞 F) F) (adelicAddHaar (𝓞 F) F) :=
    measurePreserving_mul_algebraMap_adelicAddHaar F a ha
  have hpre : IsAddFundamentalDomain (AdeleRing.principalSubgroup (𝓞 F) F) (e ⁻¹' adelicBox F)
      (adelicAddHaar (𝓞 F) F) :=
    isAddFundamentalDomain_preimage_mul_algebraMap_adelicBox F (adelicAddHaar (𝓞 F) F) a ha
  have hbox : IsAddFundamentalDomain (AdeleRing.principalSubgroup (𝓞 F) F) (adelicBox F)
      (adelicAddHaar (𝓞 F) F) :=
    isAddFundamentalDomain_adelicBox_adelicAddHaar F

  have hF₂ : ∀ (b : AdeleRing.principalSubgroup (𝓞 F) F) (u : AdeleRing (𝓞 F) F),
      φ (unipotentGL2 (b +ᵥ u) * h) * ψ₀ (-(A * (b +ᵥ u))) = φ (unipotentGL2 u * h) * ψ₀ (-(A * u)) := by
    rintro ⟨_, b, rfl⟩ u
    show φ (unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) b + u) * h)
        * ψ₀ (-(A * (algebraMap F (AdeleRing (𝓞 F) F) b + u))) = φ (unipotentGL2 u * h) * ψ₀ (-(A * u))
    rw [hper b u h, mul_add, neg_add, hA, ← map_mul, ← map_neg, AddChar.map_add_eq_mul, hψ₀, one_mul]

  have hGe : ∀ u : AdeleRing (𝓞 F) F,
      φ (unipotentGL2 (e u) * (globalPoints (𝓞 F) F γ * h)) * ψ₀ (-(e u))
        = φ (unipotentGL2 u * h) * ψ₀ (-(A * u)) := by
    intro u
    show φ (unipotentGL2 (A * u) * (globalPoints (𝓞 F) F γ * h)) * ψ₀ (-(A * u))
        = φ (unipotentGL2 u * h) * ψ₀ (-(A * u))
    rw [show unipotentGL2 (A * u) * (globalPoints (𝓞 F) F γ * h) = globalPoints (𝓞 F) F γ * (unipotentGL2 u * h) by
      rw [← mul_assoc, hγ u, mul_assoc], hinv γ]
  haveI : Countable (AdeleRing.principalSubgroup (𝓞 F) F) :=
    (Set.countable_range (algebraMap F (AdeleRing (𝓞 F) F))).to_subtype
  haveI : VAddInvariantMeasure (AdeleRing.principalSubgroup (𝓞 F) F) (AdeleRing (𝓞 F) F) (adelicAddHaar (𝓞 F) F) :=
    ⟨fun c s _ => measure_preimage_add _ (c : AdeleRing (𝓞 F) F) s⟩
  calc (∫ x in adelicBox F, φ (unipotentGL2 x * (globalPoints (𝓞 F) F γ * h)) * ψ₀ (-x) ∂adelicAddHaar (𝓞 F) F)
      = ∫ u in e ⁻¹' adelicBox F,
          φ (unipotentGL2 (e u) * (globalPoints (𝓞 F) F γ * h)) * ψ₀ (-(e u)) ∂adelicAddHaar (𝓞 F) F :=
        (hmp.setIntegral_preimage_emb e.measurableEmbedding
          (fun x => φ (unipotentGL2 x * (globalPoints (𝓞 F) F γ * h)) * ψ₀ (-x)) (adelicBox F)).symm
    _ = ∫ u in e ⁻¹' adelicBox F, φ (unipotentGL2 u * h) * ψ₀ (-(A * u)) ∂adelicAddHaar (𝓞 F) F := by
        simp only [hGe]
    _ = ∫ u in adelicBox F, φ (unipotentGL2 u * h) * ψ₀ (-(A * u)) ∂adelicAddHaar (𝓞 F) F :=
        hpre.setIntegral_eq hbox (f := fun u => φ (unipotentGL2 u * h) * ψ₀ (-(A * u))) hF₂

private theorem whittakerCoefficient_one_globalPoints_mul_eq_whittakerCoefficient [Countable F]
    (D : Set (AdelicGL2 (𝓞 F) F)) (U : Ideal (𝓞 F) → Subgroup (AdelicGL2 (𝓞 F) F))
    (gen : IsDedekindDomain.HeightOneSpectrum (𝓞 F) → AdelicGL2 (𝓞 F) F)
    (ψ₀ : AddChar (AdeleRing (𝓞 F) F) ℂ) (hψ₀ : IsPrincipalInvariantAddChar F ψ₀)
    (φ : AdelicGL2 (𝓞 F) F → ℂ)
    (hinv : ∀ (γ : Matrix.GeneralLinearGroup (Fin 2) F) (g : AdelicGL2 (𝓞 F) F), φ (globalPoints (𝓞 F) F γ * g) = φ g)
    (hper : ∀ (b : F) (u : AdeleRing (𝓞 F) F) (g : AdelicGL2 (𝓞 F) F),
      φ (unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) b + u) * g) = φ (unipotentGL2 u * g))
    (a : F) (ha : a ≠ 0) (γ : Matrix.GeneralLinearGroup (Fin 2) F)
    (hγ : ∀ u : AdeleRing (𝓞 F) F,
      unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) a * u) * globalPoints (𝓞 F) F γ
        = globalPoints (𝓞 F) F γ * unipotentGL2 u)
    (h : AdelicGL2 (𝓞 F) F) :
    whittakerCoefficient F (productionPinsOf F D U gen (adelicBox F)) ψ₀ φ 1 (globalPoints (𝓞 F) F γ * h)
      = whittakerCoefficient F (productionPinsOf F D U gen (adelicBox F)) ψ₀ φ a h := by
  have key := setIntegral_adelicBox_unipotent_globalPoints_mul_eq F ψ₀ hψ₀ φ hinv hper a ha γ hγ h
  unfold whittakerCoefficient
  simp only [map_one, one_mul]
  change (∫ x, φ (unipotentGL2 x * (globalPoints (𝓞 F) F γ * h)) * ψ₀ (-x)
      ∂((adelicAddHaar (𝓞 F) F) (adelicBox F))⁻¹ • (adelicAddHaar (𝓞 F) F).restrict (adelicBox F))
    = ∫ x, φ (unipotentGL2 x * h) * ψ₀ (-(algebraMap F (AdeleRing (𝓞 F) F) a * x))
      ∂((adelicAddHaar (𝓞 F) F) (adelicBox F))⁻¹ • (adelicAddHaar (𝓞 F) F).restrict (adelicBox F)
  rw [integral_smul_measure, integral_smul_measure, key]

private noncomputable def diagOneGlobal (a : F) (ha : a ≠ 0) : Matrix.GeneralLinearGroup (Fin 2) F :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![a, 0; 0, 1] (by simp [ha])

private theorem globalPoints_diagOneGlobal_coe (a : F) (ha : a ≠ 0) :
    ((globalPoints (𝓞 F) F (diagOneGlobal F a ha) : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F))
      = !![algebraMap F (AdeleRing (𝓞 F) F) a, 0; 0, 1] := by
  ext i j
  rw [globalPoints_apply]
  change algebraMap F (AdeleRing (𝓞 F) F) ((!![a, 0; 0, 1] : Matrix (Fin 2) (Fin 2) F) i j) = _
  fin_cases i <;> fin_cases j <;> simp

private theorem unipotentGL2_mul_globalPoints_diagOneGlobal (a : F) (ha : a ≠ 0) (u : AdeleRing (𝓞 F) F) :
    unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) a * u) * globalPoints (𝓞 F) F (diagOneGlobal F a ha)
      = globalPoints (𝓞 F) F (diagOneGlobal F a ha) * unipotentGL2 u := by
  apply Units.ext
  show (unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) a * u) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F))
        * (globalPoints (𝓞 F) F (diagOneGlobal F a ha) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F))
      = (globalPoints (𝓞 F) F (diagOneGlobal F a ha) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F))
        * (unipotentGL2 u : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F))
  rw [globalPoints_diagOneGlobal_coe, unipotentGL2_coe, unipotentGL2_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

private theorem whittakerCoefficient_eq_whittakerCoefficient_one_diagOneGlobal_mul [Countable F]
    (D : Set (AdelicGL2 (𝓞 F) F)) (U : Ideal (𝓞 F) → Subgroup (AdelicGL2 (𝓞 F) F))
    (gen : IsDedekindDomain.HeightOneSpectrum (𝓞 F) → AdelicGL2 (𝓞 F) F)
    (ψ₀ : AddChar (AdeleRing (𝓞 F) F) ℂ) (hψ₀ : IsPrincipalInvariantAddChar F ψ₀)
    (φ : AdelicGL2 (𝓞 F) F → ℂ)
    (hinv : ∀ (γ : Matrix.GeneralLinearGroup (Fin 2) F) (g : AdelicGL2 (𝓞 F) F), φ (globalPoints (𝓞 F) F γ * g) = φ g)
    (hper : ∀ (b : F) (u : AdeleRing (𝓞 F) F) (g : AdelicGL2 (𝓞 F) F),
      φ (unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) b + u) * g) = φ (unipotentGL2 u * g))
    (a : F) (ha : a ≠ 0) (h : AdelicGL2 (𝓞 F) F) :
    whittakerCoefficient F (productionPinsOf F D U gen (adelicBox F)) ψ₀ φ a h
      = whittakerCoefficient F (productionPinsOf F D U gen (adelicBox F)) ψ₀ φ 1
          (globalPoints (𝓞 F) F (diagOneGlobal F a ha) * h) :=
  (whittakerCoefficient_one_globalPoints_mul_eq_whittakerCoefficient F D U gen ψ₀ hψ₀ φ hinv hper a ha _
    (unipotentGL2_mul_globalPoints_diagOneGlobal F a ha) h).symm

end IndexShift

section Periodicity

variable (F : Type) [Field F] [NumberField F]

variable {F}

variable (F)

end Periodicity

section Growth

private noncomputable def archInclHom : InfiniteAdeleRing ℚ →* AdeleRing (𝓞 ℚ) ℚ where
  toFun x := (x, (1 : FiniteAdeleRing (𝓞 ℚ) ℚ))
  map_one' := rfl
  map_mul' _ _ := Prod.ext rfl (one_mul _).symm

private noncomputable def archIdele (a : ℚ) (ha : a ≠ 0) : (AdeleRing (𝓞 ℚ) ℚ)ˣ :=
  Units.map archInclHom (Units.map (algebraMap ℚ (InfiniteAdeleRing ℚ)).toMonoidHom (Units.mk0 a ha))

private noncomputable def finIdele (a : ℚ) (ha : a ≠ 0) : (AdeleRing (𝓞 ℚ) ℚ)ˣ :=
  Units.map (finIncl (𝓞 ℚ) ℚ)
    (Units.map (algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ)).toMonoidHom (Units.mk0 a ha))

private theorem archIdele_coe_snd
    (a : ℚ) (ha : a ≠ 0) : ((archIdele a ha : (AdeleRing (𝓞 ℚ) ℚ)ˣ) : AdeleRing (𝓞 ℚ) ℚ).2 = 1 :=
  rfl

private theorem finIdele_coe_fst
    (a : ℚ) (ha : a ≠ 0) : ((finIdele a ha : (AdeleRing (𝓞 ℚ) ℚ)ˣ) : AdeleRing (𝓞 ℚ) ℚ).1 = 1 :=
  rfl

private theorem principal_eq_archIdele_mul_finIdele (a : ℚ) (ha : a ≠ 0) :
    Units.map (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ)).toMonoidHom (Units.mk0 a ha) = archIdele a ha * finIdele a ha := by
  apply Units.ext
  apply Prod.ext
  · show algebraMap ℚ (InfiniteAdeleRing ℚ) a = algebraMap ℚ (InfiniteAdeleRing ℚ) a * 1
    rw [mul_one]
  · show algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) a = 1 * algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) a
    rw [one_mul]

private theorem globalPoints_diagOneGlobal_eq_diagOne (a : ℚ) (ha : a ≠ 0) :
    globalPoints (𝓞 ℚ) ℚ (diagOneGlobal ℚ a ha)
      = diagOne (Units.map (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ)).toMonoidHom (Units.mk0 a ha)) := by
  apply Units.ext
  rw [globalPoints_diagOneGlobal_coe]
  ext i j
  rw [diagOne_coe_apply]
  fin_cases i <;> fin_cases j <;> simp

private theorem diagOne_finIdele_mem (a : ℚ) (ha : a ≠ 0) : diagOne (finIdele a ha) ∈ finiteAdelicGL2Subgroup ℚ := by
  rw [mem_finiteAdelicGL2Subgroup_iff]
  apply Units.ext
  ext i j
  rw [glArch_apply, diagOne_coe_apply]
  fin_cases i <;> fin_cases j <;> simp [finIdele_coe_fst] <;> rfl

private theorem exists_forall_norm_whittakerCoefficient_one_diagOne_mul_le_mul_ideleNorm_rpow
    (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 ℚ) ℚ)) (hd : d₁ < d₂)
    (hcov : CoversModCentre ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂))
    {ξ : (productionPinsOf ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂)
        (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v)
        (adelicBox ℚ)).Z →* ℂˣ}
    {N : Ideal (𝓞 ℚ)} {S : Finset (HeightOneSpectrum (𝓞 ℚ))} {Φ : HeckeEigensystem ℚ ℂ}
    {φ₁ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ}
    (hiso : IsIsotypicCuspFormAt ℚ (productionPinsOf ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂)
        (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v)
        (adelicBox ℚ)) ξ N S Φ φ₁)
    (hne : φ₁ ≠ 0)
    {α : AdelicGL2 (𝓞 ℚ) ℚ → ℂ} (hα : IsFactorizableTestFn ℚ α) (hconv : rightConv ℚ φ₁ α = φ₁)
    {k : InfinitePlace ℚ → ℤ}
    (hk : ∀ (w : InfinitePlace ℚ) (hw : w.IsReal), HasArchCharacterAt₀ ℚ w (archWeightCharAt hw (k w)) φ₁)
    {ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ} (hψ : IsGlobalAddChar ℚ ψ)
    (w : InfinitePlace ℚ) {t : AdelicGL2 (𝓞 ℚ) ℚ} (ht : t ∈ finiteAdelicGL2Subgroup ℚ) :
    ∃ C M : ℝ, ∀ a : (AdeleRing (𝓞 ℚ) ℚ)ˣ, ((a : AdeleRing (𝓞 ℚ) ℚ)).2 = 1 →
      ‖whittakerCoefficient ℚ (productionPinsOf ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂)
          (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v)
          (adelicBox ℚ)) ψ φ₁ 1 (diagOne a * t)‖ ≤ C * ideleNorm ℚ a ^ M := by

  obtain ⟨a₀, ha₀, hψa₀⟩ := exists_ne_zero_forall_eq_stdAddChar_mul_of_isGlobalAddChar ℚ hψ
  have hstd : IsPrincipalInvariantAddChar ℚ (StandardAddChar.stdAddChar ℚ) :=
    (StandardAddChar.isGlobalAddChar_stdAddChar ℚ).principalInvariant

  have hinv : ∀ (γ : Matrix.GeneralLinearGroup (Fin 2) ℚ) (g : AdelicGL2 (𝓞 ℚ) ℚ),
      φ₁ (globalPoints (𝓞 ℚ) ℚ γ * g) = φ₁ g :=
    (isLsXiFunction_of_isIsotypicCuspFormAt hiso).left_invariant
  have hper : ∀ (b : ℚ) (x : AdeleRing (𝓞 ℚ) ℚ) (g : AdelicGL2 (𝓞 ℚ) ℚ),
      φ₁ (unipotentGL2 (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) b + x) * g) = φ₁ (unipotentGL2 x * g) :=
    fun b x g => (apply_unipotentGL2_algebraMap_add_mul_of_isIsotypicCuspFormAt hiso) b x g

  obtain ⟨hcls, hcts⟩ := isIdeleClassChar_and_continuous_of_isLsXiFunction_of_continuous ℚ ξ φ₁
    (isLsXiFunction_of_isIsotypicCuspFormAt hiso) hiso.continuous (Function.ne_iff.mp hne)
  let e : (AdeleRing (𝓞 ℚ) ℚ)ˣ ≃* (⊤ : Subgroup (AdeleRing (𝓞 ℚ) ℚ)ˣ) := Subgroup.topEquiv.symm
  have hcls' : IsIdeleClassChar (𝓞 ℚ) ℚ (ξ.comp e.toMonoidHom) := fun v => hcls v
  obtain ⟨w₀, hw₀⟩ := RatIdele.exists_norm_apply_eq_ideleNorm_rpow (ξ.comp e.toMonoidHom) hcls' hcts

  have hfin : diagOne (finIdele a₀ ha₀) * t ∈ finiteAdelicGL2Subgroup ℚ :=
    (finiteAdelicGL2Subgroup ℚ).mul_mem (diagOne_finIdele_mem a₀ ha₀) ht
  obtain ⟨α', hα', hα'eq⟩ := exists_isFactorizableTestFn_rightConv_eq_fun_mul hα hconv (diagOne (finIdele a₀ ha₀) * t)
  have hxt : rightConv ℚ φ₁ α' ∈ archCutSubmodule ℚ (weightTypeFamilyRat k) := by
    rw [hα'eq]
    exact comp_mul_mem_archCutSubmodule_of_mem_finiteAdelicGL2Subgroup ℚ
      (mem_archCutSubmodule_weightTypeFamilyRat hk) hfin

  obtain ⟨C, hC⟩ :=
    exists_norm_whittakerCoefficient_rightConv_diagOne_mul_le_ideleNorm_rpow_mul_norm_infinitePlace_rpow_neg
      ℚ c u d₁ d₂ T hd hcov ξ φ₁ hiso.smoothCusp.1 hiso.continuous α' hα' (weightTypeFamilyRat k) hxt w₀
    (fun z => hw₀ z) 0
  refine ⟨C * ideleNorm ℚ (archIdele a₀ ha₀) ^ (w₀ / 2), w₀ / 2, fun a ha => ?_⟩

  have hdatum : globalPoints (𝓞 ℚ) ℚ (diagOneGlobal ℚ a₀ ha₀) * (diagOne a * t)
      = diagOne (archIdele a₀ ha₀ * a) * (diagOne (finIdele a₀ ha₀) * t) := by
    rw [globalPoints_diagOneGlobal_eq_diagOne, principal_eq_archIdele_mul_finIdele, map_mul, map_mul]
    simp only [mul_assoc]
    congr 1
    rw [← mul_assoc, ← map_mul, mul_comm (finIdele a₀ ha₀) a, map_mul, mul_assoc]
  have hsnd : ((archIdele a₀ ha₀ * a : (AdeleRing (𝓞 ℚ) ℚ)ˣ) : AdeleRing (𝓞 ℚ) ℚ).2 = 1 := by
    rw [Units.val_mul]
    show ((archIdele a₀ ha₀ : (AdeleRing (𝓞 ℚ) ℚ)ˣ) : AdeleRing (𝓞 ℚ) ℚ).2
        * ((a : (AdeleRing (𝓞 ℚ) ℚ)ˣ) : AdeleRing (𝓞 ℚ) ℚ).2 = 1
    rw [archIdele_coe_snd, ha, one_mul]
  have hb := hC 1 (map_one _) (fun _ => by rw [map_one, map_one]; exact isRowIsometry_one)
    (archIdele a₀ ha₀ * a) hsnd w
  rw [mul_one, Nat.cast_zero, neg_zero, Real.rpow_zero, mul_one, ideleNorm_mul,
    Real.mul_rpow (ideleNorm_pos _).le (ideleNorm_pos _).le, ← mul_assoc] at hb
  rw [whittakerCoefficient_one_eq_whittakerCoefficient_of_forall_eq_mul ℚ _ ψ (StandardAddChar.stdAddChar ℚ) a₀ hψa₀,
    whittakerCoefficient_eq_whittakerCoefficient_one_diagOneGlobal_mul ℚ _ _ _ (StandardAddChar.stdAddChar ℚ) hstd φ₁
      hinv hper a₀ ha₀, hdatum, ← whittakerCoefficient_fun_mul, ← hα'eq]
  exact hb

end Growth

end PolynomialGrowthOfCoefficients

section SeparationOfVariables

section SeparationAtDatum

private theorem whittakerCoefficient_one_diagOne_archRealUnit_mul_eq_div_mul_pos
    (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 ℚ) ℚ)) (hd : d₁ < d₂)
    (hcov : CoversModCentre ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂))
    (ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ) (hψ : IsGlobalAddChar ℚ ψ) {w : InfinitePlace ℚ} (hw : w.IsReal)
    (hψr : ∀ x : InfiniteAdeleRing ℚ, (∀ w' : InfinitePlace ℚ, w' ≠ w → x w' = 0) →
      ψ (⟨x, 0⟩ : AdeleRing (𝓞 ℚ) ℚ) = Complex.exp (2 * Real.pi * Complex.I * extensionEmbedding w (x w)))
    {ξ : (productionPinsOf ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂)
      (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ)).Z →* ℂˣ}
    {N : Ideal (𝓞 ℚ)} {S : Finset (HeightOneSpectrum (𝓞 ℚ))} {Φ : HeckeEigensystem ℚ ℂ} {φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ}
    (hiso : IsIsotypicCuspFormAt ℚ (productionPinsOf ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂)
      (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ)) ξ N S Φ φ)
    (hne : φ ≠ 0) (hconv : ∃ α : AdelicGL2 (𝓞 ℚ) ℚ → ℂ, IsFactorizableTestFn ℚ α ∧ rightConv ℚ φ α = φ)
    (hsm : IsArchSmoothAt hw φ) (ν : ℂ) (hΩ : archCasimirAt hw φ = (1 / 4 - ν ^ 2) • φ)
    {k : InfinitePlace ℚ → ℤ}
    (hwt : ∀ (w : InfinitePlace ℚ) (hw : w.IsReal), HasArchCharacterAt₀ ℚ w (archWeightCharAt hw (k w)) φ)
    {uc : ℂ} {ac : ℤ} (hcen : IsArchCompAt ℚ (ξ.comp Subgroup.topEquiv.symm.toMonoidHom) w uc ac)
    (W : AdelicGL2 (𝓞 ℚ) ℚ → ℂ)
    (hW : W = whittakerCoefficient ℚ
      (productionPinsOf ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂)
        (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ))
      ψ φ 1)
    {t₀ : AdelicGL2 (𝓞 ℚ) ℚ} (ht₀ : t₀ ∈ finiteAdelicGL2Subgroup ℚ) {y₀ : ℝ} (hy₀ : 0 < y₀)
    (href : W (diagOne (archUnitHom w (archRealUnit hw y₀ hy₀.ne')) * t₀) ≠ 0) :
    ∀ h : AdelicGL2 (𝓞 ℚ) ℚ, h ∈ finiteAdelicGL2Subgroup ℚ → ∀ y : ℝ, ∀ hy : 0 < y,
      W (diagOne (archUnitHom w (archRealUnit hw y hy.ne')) * h)
        = W (diagOne (archUnitHom w (archRealUnit hw y₀ hy₀.ne')) * h)
            / W (diagOne (archUnitHom w (archRealUnit hw y₀ hy₀.ne')) * t₀)
            * W (diagOne (archUnitHom w (archRealUnit hw y hy.ne')) * t₀) := by
  intro h hh y hy
  obtain ⟨α, hα, hα'⟩ := hconv

  have hpeel : ∀ (z : ℝ) (hz : 0 < z) (g : AdelicGL2 (𝓞 ℚ) ℚ),
      W (archRealGLAt hw (splitTorusGL2 (Real.log z / 2)) * g)
        = (((Real.sqrt z)⁻¹ : ℝ) : ℂ) ^ uc * W (diagOne (archUnitHom w (archRealUnit hw z hz.ne')) * g) := by
    intro z hz g
    rw [hW]
    exact whittakerCoefficient_archRealGLAt_splitTorusGL2_half_log_of_isArchCompAt ℚ _ _ _ _ ψ
      (isLsXiFunction_of_isIsotypicCuspFormAt hiso) hw
      hcen 1 z hz g
  have hP : ∀ (z : ℝ), 0 < z → (((Real.sqrt z)⁻¹ : ℝ) : ℂ) ^ uc ≠ 0 := fun z hz =>
    left_ne_zero_of_mul_eq_one (inv_sqrt_cpow_mul_sqrt_cpow uc hz)

  have hgrowth : ∀ g : AdelicGL2 (𝓞 ℚ) ℚ, g ∈ finiteAdelicGL2Subgroup ℚ →
      ∃ C' N' : ℝ, ∀ z : ℝ, 1 ≤ z → ‖W (archRealGLAt hw (splitTorusGL2 (Real.log z / 2)) * g)‖ ≤ C' * z ^ N' := by
    intro g hg
    obtain ⟨C, M, hCM⟩ := exists_forall_norm_whittakerCoefficient_one_diagOne_mul_le_mul_ideleNorm_rpow c u d₁ d₂ T hd
      hcov hiso hne hα hα' hwt hψ w hg
    obtain ⟨C', N', hb⟩ := exists_forall_norm_cpow_mul_le_of_forall_norm_le uc
      (fun z : ℝ => if hz : 0 < z then W (diagOne (archUnitHom w (archRealUnit hw z hz.ne')) * g) else 0) C M
      (fun z hz => by
        simp only [dif_pos hz]
        have := hCM (archUnitHom w (archRealUnit hw z hz.ne')) rfl
        rwa [ideleNorm_archUnitHom_archRealUnit_rat hw, abs_of_pos hz, ← hW] at this)
    refine ⟨C', N', fun z hz => ?_⟩
    have hz0 : 0 < z := lt_of_lt_of_le one_pos hz
    have hbz := hb z hz
    simp only [dif_pos hz0] at hbz
    rw [hpeel z hz0 g]
    exact hbz

  obtain ⟨⟨hf, hf', hfeq⟩, -⟩ := whittaker_ode_splitTorus_whittakerCoefficient_one_of_isIsotypicCuspFormAt
    _ _ _ ψ hψ hw hψr hiso ⟨α, hα, hα'⟩ hsm ν hΩ (k w) (hwt w hw) W hW t₀ ht₀
  obtain ⟨⟨hg, hg', hgeq⟩, -⟩ := whittaker_ode_splitTorus_whittakerCoefficient_one_of_isIsotypicCuspFormAt
    _ _ _ ψ hψ hw hψr hiso ⟨α, hα, hα'⟩ hsm ν hΩ (k w) (hwt w hw) W hW h hh
  have hf₀ : W (archRealGLAt hw (splitTorusGL2 (Real.log y₀ / 2)) * t₀) ≠ 0 := by
    rw [hpeel y₀ hy₀ t₀]
    exact mul_ne_zero (hP y₀ hy₀) href
  have hsep : W (archRealGLAt hw (splitTorusGL2 (Real.log y / 2)) * h)
      = W (archRealGLAt hw (splitTorusGL2 (Real.log y₀ / 2)) * h)
          / W (archRealGLAt hw (splitTorusGL2 (Real.log y₀ / 2)) * t₀)
          * W (archRealGLAt hw (splitTorusGL2 (Real.log y / 2)) * t₀) :=
    eq_div_mul_of_whittaker_ode_of_moderateGrowth ν ((k w : ℤ) : ℝ) _ _ hf hf' hfeq (hgrowth t₀ ht₀) hg hg' hgeq
      (hgrowth h hh) y₀ hy₀ hf₀ y hy
  rw [hpeel y hy h, hpeel y₀ hy₀ h, hpeel y₀ hy₀ t₀, hpeel y hy t₀, mul_div_mul_left _ _ (hP y₀ hy₀)] at hsep
  exact mul_left_cancel₀ (hP y hy) (hsep.trans (mul_left_comm _ _ _))

private theorem whittakerCoefficient_one_diagOne_archRealUnit_neg_mul_eq_div_mul
    (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 ℚ) ℚ)) (hd : d₁ < d₂)
    (hcov : CoversModCentre ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂))
    (ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ) (hψ : IsGlobalAddChar ℚ ψ) {w : InfinitePlace ℚ} (hw : w.IsReal)
    (hψr : ∀ x : InfiniteAdeleRing ℚ, (∀ w' : InfinitePlace ℚ, w' ≠ w → x w' = 0) →
      ψ (⟨x, 0⟩ : AdeleRing (𝓞 ℚ) ℚ) = Complex.exp (2 * Real.pi * Complex.I * extensionEmbedding w (x w)))
    {ξ : (productionPinsOf ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂)
      (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ)).Z →* ℂˣ}
    {N : Ideal (𝓞 ℚ)} {S : Finset (HeightOneSpectrum (𝓞 ℚ))} {Φ : HeckeEigensystem ℚ ℂ} {φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ}
    (hiso : IsIsotypicCuspFormAt ℚ (productionPinsOf ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂)
      (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ)) ξ N S Φ φ)
    (hne : φ ≠ 0) (hconv : ∃ α : AdelicGL2 (𝓞 ℚ) ℚ → ℂ, IsFactorizableTestFn ℚ α ∧ rightConv ℚ φ α = φ)
    (hsm : IsArchSmoothAt hw φ) (ν : ℂ) (hΩ : archCasimirAt hw φ = (1 / 4 - ν ^ 2) • φ)
    {k : InfinitePlace ℚ → ℤ}
    (hwt : ∀ (w : InfinitePlace ℚ) (hw : w.IsReal), HasArchCharacterAt₀ ℚ w (archWeightCharAt hw (k w)) φ)
    {uc : ℂ} {ac : ℤ} (hcen : IsArchCompAt ℚ (ξ.comp Subgroup.topEquiv.symm.toMonoidHom) w uc ac)
    (W : AdelicGL2 (𝓞 ℚ) ℚ → ℂ)
    (hW : W = whittakerCoefficient ℚ
      (productionPinsOf ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂)
        (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ))
      ψ φ 1)
    {t₀ : AdelicGL2 (𝓞 ℚ) ℚ} (ht₀ : t₀ ∈ finiteAdelicGL2Subgroup ℚ) {y₀ : ℝ} (hy₀ : 0 < y₀)
    (href : W (diagOne (archUnitHom w (archRealUnit hw (-y₀) (neg_ne_zero.mpr hy₀.ne'))) * t₀) ≠ 0) :
    ∀ h : AdelicGL2 (𝓞 ℚ) ℚ, h ∈ finiteAdelicGL2Subgroup ℚ → ∀ y : ℝ, ∀ hy : 0 < y,
      W (diagOne (archUnitHom w (archRealUnit hw (-y) (neg_ne_zero.mpr hy.ne'))) * h)
        = W (diagOne (archUnitHom w (archRealUnit hw (-y₀) (neg_ne_zero.mpr hy₀.ne'))) * h)
            / W (diagOne (archUnitHom w (archRealUnit hw (-y₀) (neg_ne_zero.mpr hy₀.ne'))) * t₀)
            * W (diagOne (archUnitHom w (archRealUnit hw (-y) (neg_ne_zero.mpr hy.ne'))) * t₀) := by
  intro h hh y hy
  obtain ⟨α, hα, hα'⟩ := hconv

  have hpeel : ∀ (z : ℝ) (hz : 0 < z) (g : AdelicGL2 (𝓞 ℚ) ℚ),
      W (archRealGLAt hw (UpperHalfPlane.J * splitTorusGL2 (Real.log z / 2)) * g)
        = (((Real.sqrt z)⁻¹ : ℝ) : ℂ) ^ uc
            * W (diagOne (archUnitHom w (archRealUnit hw (-z) (neg_ne_zero.mpr hz.ne'))) * g) := by
    intro z hz g
    rw [hW]
    exact whittakerCoefficient_archRealGLAt_J_mul_splitTorusGL2_half_log_of_isArchCompAt ℚ _ _ _ _ ψ
      (isLsXiFunction_of_isIsotypicCuspFormAt hiso) hw hcen 1 z hz g
  have hP : ∀ (z : ℝ), 0 < z → (((Real.sqrt z)⁻¹ : ℝ) : ℂ) ^ uc ≠ 0 := fun z hz =>
    left_ne_zero_of_mul_eq_one (inv_sqrt_cpow_mul_sqrt_cpow uc hz)

  have hgrowth : ∀ g : AdelicGL2 (𝓞 ℚ) ℚ, g ∈ finiteAdelicGL2Subgroup ℚ →
      ∃ C' N' : ℝ, ∀ z : ℝ, 1 ≤ z →
        ‖W (archRealGLAt hw (UpperHalfPlane.J * splitTorusGL2 (Real.log z / 2)) * g)‖ ≤ C' * z ^ N' := by
    intro g hg
    obtain ⟨C, M, hCM⟩ := exists_forall_norm_whittakerCoefficient_one_diagOne_mul_le_mul_ideleNorm_rpow c u d₁ d₂ T hd
      hcov hiso hne hα hα' hwt hψ w hg
    obtain ⟨C', N', hb⟩ := exists_forall_norm_cpow_mul_le_of_forall_norm_le uc
      (fun z : ℝ =>
        if hz : 0 < z then W (diagOne (archUnitHom w (archRealUnit hw (-z) (neg_ne_zero.mpr hz.ne'))) * g) else 0) C M
      (fun z hz => by
        simp only [dif_pos hz]
        have := hCM (archUnitHom w (archRealUnit hw (-z) (neg_ne_zero.mpr hz.ne'))) rfl
        rwa [ideleNorm_archUnitHom_archRealUnit_rat hw, abs_neg, abs_of_pos hz, ← hW] at this)
    refine ⟨C', N', fun z hz => ?_⟩
    have hz0 : 0 < z := lt_of_lt_of_le one_pos hz
    have hbz := hb z hz
    simp only [dif_pos hz0] at hbz
    rw [hpeel z hz0 g]
    exact hbz

  obtain ⟨-, hf, hf', hfeq⟩ := whittaker_ode_splitTorus_whittakerCoefficient_one_of_isIsotypicCuspFormAt
    _ _ _ ψ hψ hw hψr hiso ⟨α, hα, hα'⟩ hsm ν hΩ (k w) (hwt w hw) W hW t₀ ht₀
  obtain ⟨-, hg, hg', hgeq⟩ := whittaker_ode_splitTorus_whittakerCoefficient_one_of_isIsotypicCuspFormAt
    _ _ _ ψ hψ hw hψr hiso ⟨α, hα, hα'⟩ hsm ν hΩ (k w) (hwt w hw) W hW h hh
  have hf₀ : W (archRealGLAt hw (UpperHalfPlane.J * splitTorusGL2 (Real.log y₀ / 2)) * t₀) ≠ 0 := by
    rw [hpeel y₀ hy₀ t₀]
    exact mul_ne_zero (hP y₀ hy₀) href
  have hsep : W (archRealGLAt hw (UpperHalfPlane.J * splitTorusGL2 (Real.log y / 2)) * h)
      = W (archRealGLAt hw (UpperHalfPlane.J * splitTorusGL2 (Real.log y₀ / 2)) * h)
          / W (archRealGLAt hw (UpperHalfPlane.J * splitTorusGL2 (Real.log y₀ / 2)) * t₀)
          * W (archRealGLAt hw (UpperHalfPlane.J * splitTorusGL2 (Real.log y / 2)) * t₀) :=
    eq_div_mul_of_whittaker_ode_of_moderateGrowth ν ((-(k w) : ℤ) : ℝ) _ _ hf hf' hfeq (hgrowth t₀ ht₀) hg hg' hgeq
      (hgrowth h hh) y₀ hy₀ hf₀ y hy
  rw [hpeel y hy h, hpeel y₀ hy₀ h, hpeel y₀ hy₀ t₀, hpeel y hy t₀, mul_div_mul_left _ _ (hP y₀ hy₀)] at hsep
  exact mul_left_cancel₀ (hP y hy) (hsep.trans (mul_left_comm _ _ _))

end SeparationAtDatum

section FactorizationClause

private theorem extensionEmbedding_eq_ofReal_ringEquivRealOfIsReal
    {w : InfinitePlace ℚ} (hw : w.IsReal) (x : w.Completion) :
    extensionEmbedding w x = ((ringEquivRealOfIsReal hw x : ℝ) : ℂ) := by
  rw [← extensionEmbeddingOfIsReal_apply hw, ← ringEquivRealOfIsReal_apply hw]

private theorem extensionEmbedding_idele_eq_ofReal_archReal
    {w : InfinitePlace ℚ} (hw : w.IsReal) (a : (AdeleRing (𝓞 ℚ) ℚ)ˣ) :
    extensionEmbedding w ((a : AdeleRing (𝓞 ℚ) ℚ).1 w) = ((archReal hw a : ℝ) : ℂ) :=
  extensionEmbedding_eq_ofReal_ringEquivRealOfIsReal hw _

open scoped Classical in

private noncomputable def factorConstant (cst : AdelicGL2 (𝓞 ℚ) ℚ → ℂ) (ρ : ℂ) :
    FiniteAdeleRing (𝓞 ℚ) ℚ → AdelicGL2 (𝓞 ℚ) ℚ → ℂ :=
  fun x g => if hx : IsUnit x then ρ⁻¹ * cst (diagOne (Units.map (finIncl (𝓞 ℚ) ℚ) hx.unit) * g) else 0

private theorem whittakerCoefficient_one_diagOne_mul_eq_prod_mul_factorConstant
    (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 ℚ) ℚ)) (ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ) (φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ)
    {w : InfinitePlace ℚ} (hw : w.IsReal) (Fref : ℂ → ℂ) (cst : AdelicGL2 (𝓞 ℚ) ℚ → ℂ)
    (hprop : ∀ h : AdelicGL2 (𝓞 ℚ) ℚ, h ∈ finiteAdelicGL2Subgroup ℚ → ∀ (r : ℝ) (hr : r ≠ 0),
      whittakerCoefficient ℚ
        (productionPinsOf ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂)
          (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ))
        ψ φ 1
        (diagOne (archUnitHom w (archRealUnit hw r hr)) * h) = cst h * Fref (r : ℂ))
    (ρ : ℂ) (hρ : ρ ≠ 0) :
    ∀ a : (AdeleRing (𝓞 ℚ) ℚ)ˣ, ∀ g : AdelicGL2 (𝓞 ℚ) ℚ, g ∈ finiteAdelicGL2Subgroup ℚ →
      whittakerCoefficient ℚ
        (productionPinsOf ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂)
          (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ))
        ψ φ 1
        (diagOne a * g)
      = (∏ w' : InfinitePlace ℚ, ρ * Fref (extensionEmbedding w' ((a : AdeleRing (𝓞 ℚ) ℚ).1 w')))
          * factorConstant cst ρ (a : AdeleRing (𝓞 ℚ) ℚ).2 g  := by
  intro a g hg
  dsimp only [factorConstant]
  have hunit : IsUnit (a : AdeleRing (𝓞 ℚ) ℚ).2 := ⟨Units.map (finProjHom ℚ) a, rfl⟩
  have hfin : Units.map (finIncl (𝓞 ℚ) ℚ) hunit.unit = finPart a := by
    apply Units.ext
    rw [finPart_coe]
    exact congrArg (fun x : FiniteAdeleRing (𝓞 ℚ) ℚ => ((1 : InfiniteAdeleRing ℚ), x)) hunit.unit_spec
  have hmem : diagOne (finPart a) * g ∈ finiteAdelicGL2Subgroup ℚ := mul_mem (diagOne_finPart_mem a) hg
  have hkey := hprop _ hmem (archReal hw a) (archReal_ne_zero hw a)
  rw [← mul_assoc, ← map_mul, ← eq_archUnitHom_archRealUnit_mul_finPart hw a] at hkey
  rw [hkey, Fintype.prod_subsingleton _ w, dif_pos hunit, hfin, extensionEmbedding_idele_eq_ofReal_archReal hw,
    mul_mul_mul_comm, mul_inv_cancel₀ hρ, one_mul, mul_comm]

private theorem exists_forall_whittakerCoefficient_one_diagOne_mul_eq_prod_mul
    (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 ℚ) ℚ)) (ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ) (φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ)
    {w : InfinitePlace ℚ} (hw : w.IsReal) (Fref : ℂ → ℂ) (cst : AdelicGL2 (𝓞 ℚ) ℚ → ℂ)
    (hprop : ∀ h : AdelicGL2 (𝓞 ℚ) ℚ, h ∈ finiteAdelicGL2Subgroup ℚ → ∀ (r : ℝ) (hr : r ≠ 0),
      whittakerCoefficient ℚ
        (productionPinsOf ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂)
          (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ))
        ψ φ 1
        (diagOne (archUnitHom w (archRealUnit hw r hr)) * h) = cst h * Fref (r : ℂ))
    (ρ : ℂ) (hρ : ρ ≠ 0) :
    ∃ C : FiniteAdeleRing (𝓞 ℚ) ℚ → AdelicGL2 (𝓞 ℚ) ℚ → ℂ,
      ∀ a : (AdeleRing (𝓞 ℚ) ℚ)ˣ, ∀ g : AdelicGL2 (𝓞 ℚ) ℚ, g ∈ finiteAdelicGL2Subgroup ℚ →
        whittakerCoefficient ℚ
          (productionPinsOf ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂)
            (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ))
          ψ φ 1
          (diagOne a * g)
        = (∏ w' : InfinitePlace ℚ, ρ * Fref (extensionEmbedding w' ((a : AdeleRing (𝓞 ℚ) ℚ).1 w')))
            * C (a : AdeleRing (𝓞 ℚ) ℚ).2 g  :=
  ⟨_, whittakerCoefficient_one_diagOne_mul_eq_prod_mul_factorConstant c u d₁ d₂ T ψ φ hw Fref cst hprop ρ hρ⟩

end FactorizationClause

end SeparationOfVariables

section GrowthOfSheetFunctions

section GrowthOfSheets

private theorem exists_forall_norm_splitTorus_le_mul_rpow
    (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 ℚ) ℚ)) (hd : d₁ < d₂)
    (hcov : CoversModCentre ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂))
    (ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ) (hψ : IsGlobalAddChar ℚ ψ) {w : InfinitePlace ℚ} (hw : w.IsReal)
    (hψr : ∀ x : InfiniteAdeleRing ℚ, (∀ w' : InfinitePlace ℚ, w' ≠ w → x w' = 0) →
      ψ (⟨x, 0⟩ : AdeleRing (𝓞 ℚ) ℚ) = Complex.exp (2 * Real.pi * Complex.I * extensionEmbedding w (x w)))
    {ξ : (productionPinsOf ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂)
      (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ)).Z →* ℂˣ}
    {N : Ideal (𝓞 ℚ)} {S : Finset (HeightOneSpectrum (𝓞 ℚ))} {Φ : HeckeEigensystem ℚ ℂ} {φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ}
    (hiso : IsIsotypicCuspFormAt ℚ (productionPinsOf ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂)
      (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ)) ξ N S Φ φ)
    (hne : φ ≠ 0) (hconv : ∃ α : AdelicGL2 (𝓞 ℚ) ℚ → ℂ, IsFactorizableTestFn ℚ α ∧ rightConv ℚ φ α = φ)
    (hsm : IsArchSmoothAt hw φ) (ν : ℂ) (hΩ : archCasimirAt hw φ = (1 / 4 - ν ^ 2) • φ)
    {k : InfinitePlace ℚ → ℤ}
    (hwt : ∀ (w : InfinitePlace ℚ) (hw : w.IsReal), HasArchCharacterAt₀ ℚ w (archWeightCharAt hw (k w)) φ)
    {uc : ℂ} {ac : ℤ} (hcen : IsArchCompAt ℚ (ξ.comp Subgroup.topEquiv.symm.toMonoidHom) w uc ac)
    (W : AdelicGL2 (𝓞 ℚ) ℚ → ℂ)
    (hW : W = whittakerCoefficient ℚ
      (productionPinsOf ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂)
        (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ))
      ψ φ 1)
    (g : AdelicGL2 (𝓞 ℚ) ℚ) (hg : g ∈ finiteAdelicGL2Subgroup ℚ) :
    ∃ C' N' : ℝ, ∀ z : ℝ, 1 ≤ z → ‖W (archRealGLAt hw (splitTorusGL2 (Real.log z / 2)) * g)‖ ≤ C' * z ^ N' := by
  obtain ⟨α, hα, hα'⟩ := hconv
  have hpeel : ∀ (z : ℝ) (hz : 0 < z),
      W (archRealGLAt hw (splitTorusGL2 (Real.log z / 2)) * g)
        = (((Real.sqrt z)⁻¹ : ℝ) : ℂ) ^ uc * W (diagOne (archUnitHom w (archRealUnit hw z hz.ne')) * g) := by
    intro z hz
    rw [hW]
    exact whittakerCoefficient_archRealGLAt_splitTorusGL2_half_log_of_isArchCompAt ℚ _ _ _ _ ψ
      (isLsXiFunction_of_isIsotypicCuspFormAt hiso) hw
      hcen 1 z hz g
  obtain ⟨C, M, hCM⟩ := exists_forall_norm_whittakerCoefficient_one_diagOne_mul_le_mul_ideleNorm_rpow c u d₁ d₂ T hd
    hcov hiso hne hα hα' hwt hψ w hg
  obtain ⟨C', N', hb⟩ := exists_forall_norm_cpow_mul_le_of_forall_norm_le uc
    (fun z : ℝ => if hz : 0 < z then W (diagOne (archUnitHom w (archRealUnit hw z hz.ne')) * g) else 0) C M
    (fun z hz => by
      simp only [dif_pos hz]
      have := hCM (archUnitHom w (archRealUnit hw z hz.ne')) rfl
      rwa [ideleNorm_archUnitHom_archRealUnit_rat hw, abs_of_pos hz, ← hW] at this)
  refine ⟨C', N', fun z hz => ?_⟩
  have hz0 : 0 < z := lt_of_lt_of_le one_pos hz
  have hbz := hb z hz
  simp only [dif_pos hz0] at hbz
  rw [hpeel z hz0]
  exact hbz

private theorem exists_forall_norm_J_splitTorus_le_mul_rpow
    (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 ℚ) ℚ)) (hd : d₁ < d₂)
    (hcov : CoversModCentre ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂))
    (ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ) (hψ : IsGlobalAddChar ℚ ψ) {w : InfinitePlace ℚ} (hw : w.IsReal)
    (hψr : ∀ x : InfiniteAdeleRing ℚ, (∀ w' : InfinitePlace ℚ, w' ≠ w → x w' = 0) →
      ψ (⟨x, 0⟩ : AdeleRing (𝓞 ℚ) ℚ) = Complex.exp (2 * Real.pi * Complex.I * extensionEmbedding w (x w)))
    {ξ : (productionPinsOf ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂)
      (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ)).Z →* ℂˣ}
    {N : Ideal (𝓞 ℚ)} {S : Finset (HeightOneSpectrum (𝓞 ℚ))} {Φ : HeckeEigensystem ℚ ℂ} {φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ}
    (hiso : IsIsotypicCuspFormAt ℚ (productionPinsOf ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂)
      (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ)) ξ N S Φ φ)
    (hne : φ ≠ 0) (hconv : ∃ α : AdelicGL2 (𝓞 ℚ) ℚ → ℂ, IsFactorizableTestFn ℚ α ∧ rightConv ℚ φ α = φ)
    (hsm : IsArchSmoothAt hw φ) (ν : ℂ) (hΩ : archCasimirAt hw φ = (1 / 4 - ν ^ 2) • φ)
    {k : InfinitePlace ℚ → ℤ}
    (hwt : ∀ (w : InfinitePlace ℚ) (hw : w.IsReal), HasArchCharacterAt₀ ℚ w (archWeightCharAt hw (k w)) φ)
    {uc : ℂ} {ac : ℤ} (hcen : IsArchCompAt ℚ (ξ.comp Subgroup.topEquiv.symm.toMonoidHom) w uc ac)
    (W : AdelicGL2 (𝓞 ℚ) ℚ → ℂ)
    (hW : W = whittakerCoefficient ℚ
      (productionPinsOf ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂)
        (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ))
      ψ φ 1)
    (g : AdelicGL2 (𝓞 ℚ) ℚ) (hg : g ∈ finiteAdelicGL2Subgroup ℚ) :
    ∃ C' N' : ℝ, ∀ z : ℝ, 1 ≤ z →
      ‖W (archRealGLAt hw (UpperHalfPlane.J * splitTorusGL2 (Real.log z / 2)) * g)‖ ≤ C' * z ^ N' := by
  obtain ⟨α, hα, hα'⟩ := hconv
  have hpeel : ∀ (z : ℝ) (hz : 0 < z),
      W (archRealGLAt hw (UpperHalfPlane.J * splitTorusGL2 (Real.log z / 2)) * g)
        = (((Real.sqrt z)⁻¹ : ℝ) : ℂ) ^ uc
            * W (diagOne (archUnitHom w (archRealUnit hw (-z) (neg_ne_zero.mpr hz.ne'))) * g) := by
    intro z hz
    rw [hW]
    exact whittakerCoefficient_archRealGLAt_J_mul_splitTorusGL2_half_log_of_isArchCompAt ℚ _ _ _ _ ψ
      (isLsXiFunction_of_isIsotypicCuspFormAt hiso) hw hcen 1 z hz g
  obtain ⟨C, M, hCM⟩ := exists_forall_norm_whittakerCoefficient_one_diagOne_mul_le_mul_ideleNorm_rpow c u d₁ d₂ T hd
    hcov hiso hne hα hα' hwt hψ w hg
  obtain ⟨C', N', hb⟩ := exists_forall_norm_cpow_mul_le_of_forall_norm_le uc
    (fun z : ℝ =>
      if hz : 0 < z then W (diagOne (archUnitHom w (archRealUnit hw (-z) (neg_ne_zero.mpr hz.ne'))) * g) else 0) C M
    (fun z hz => by
      simp only [dif_pos hz]
      have := hCM (archUnitHom w (archRealUnit hw (-z) (neg_ne_zero.mpr hz.ne'))) rfl
      rwa [ideleNorm_archUnitHom_archRealUnit_rat hw, abs_neg, abs_of_pos hz, ← hW] at this)
  refine ⟨C', N', fun z hz => ?_⟩
  have hz0 : 0 < z := lt_of_lt_of_le one_pos hz
  have hbz := hb z hz
  simp only [dif_pos hz0] at hbz
  rw [hpeel z hz0]
  exact hbz

end GrowthOfSheets

end GrowthOfSheetFunctions

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

private def archLowerAt {w : InfinitePlace F} (hw : w.IsReal) (φ : AdelicGL2 (𝓞 F) F → ℂ) : AdelicGL2 (𝓞 F) F → ℂ :=
  archDerivAt hw .H φ - Complex.I • (archDerivAt hw .E φ + archDerivAt hw .Fm φ)

private theorem isArchSmoothAt_archRotDerivAt {w : InfinitePlace F} {hw : w.IsReal} {φ : AdelicGL2 (𝓞 F) F → ℂ}
    (hφ : IsArchSmoothAt hw φ) : IsArchSmoothAt hw (archRotDerivAt hw φ) :=
  (hφ.archDerivAt .E).sub (hφ.archDerivAt .Fm)

private theorem isArchSmoothAt_archRaiseAt {w : InfinitePlace F} {hw : w.IsReal} {φ : AdelicGL2 (𝓞 F) F → ℂ}
    (hφ : IsArchSmoothAt hw φ) : IsArchSmoothAt hw (archRaiseAt hw φ) :=
  (hφ.archDerivAt .H).add (((hφ.archDerivAt .E).add (hφ.archDerivAt .Fm)).smul Complex.I)

private theorem isArchSmoothAt_archLowerAt {w : InfinitePlace F} {hw : w.IsReal} {φ : AdelicGL2 (𝓞 F) F → ℂ}
    (hφ : IsArchSmoothAt hw φ) : IsArchSmoothAt hw (archLowerAt hw φ) :=
  (hφ.archDerivAt .H).sub (((hφ.archDerivAt .E).add (hφ.archDerivAt .Fm)).smul Complex.I)

private theorem isArchSmoothAt_archRaiseAt_archLowerAt {w : InfinitePlace F} {hw : w.IsReal} {φ : AdelicGL2 (𝓞
    F) F → ℂ}
    (hφ : IsArchSmoothAt hw φ) :
    archRaiseAt hw (archLowerAt hw φ) =
      (-4 : ℂ) • archCasimirAt hw φ + archRotDerivAt hw (archRotDerivAt hw φ) -
        (2 * Complex.I) • archRotDerivAt hw φ := by
  have hH := hφ.archDerivAt .H
  have hE := hφ.archDerivAt .E
  have hF := hφ.archDerivAt .Fm
  have hexp : ∀ a : ArchDir, archDerivAt hw a (archLowerAt hw φ) =
      archDerivAt hw a (archDerivAt hw .H φ) -
        Complex.I • (archDerivAt hw a (archDerivAt hw .E φ) + archDerivAt hw a (archDerivAt hw .Fm φ)) := by
    intro a
    rw [archLowerAt, archDerivAt_sub hH ((hE.add hF).smul Complex.I) a, archDerivAt_smul,
      archDerivAt_add hE hF a]
  have hR1 : archDerivAt hw .Fm (archDerivAt hw .E φ) =
      archDerivAt hw .E (archDerivAt hw .Fm φ) - archDerivAt hw .H φ := by
    rw [← (isArchSmoothAt_archDerivAt_E_Fm_sub_archDerivAt_Fm_E hφ)]
    abel
  have hR2 : archDerivAt hw .E (archDerivAt hw .H φ) =
      archDerivAt hw .H (archDerivAt hw .E φ) - (archDerivAt hw .E φ + archDerivAt hw .E φ) := by
    rw [← (isArchSmoothAt_archDerivAt_H_E_sub_archDerivAt_E_H hφ)]
    abel
  have hR3 : archDerivAt hw .Fm (archDerivAt hw .H φ) =
      archDerivAt hw .H (archDerivAt hw .Fm φ) + (archDerivAt hw .Fm φ + archDerivAt hw .Fm φ) := by
    rw [sub_eq_iff_eq_add.mp (isArchSmoothAt_archDerivAt_H_Fm_sub_archDerivAt_Fm_H hφ)]
    abel
  rw [archRaiseAt, hexp, hexp, hexp, AutomorphicForm.archCasimirAt, archRotDerivAt,
    archRotDerivAt, archDerivAt_sub hE hF, archDerivAt_sub hE hF, hR1, hR2, hR3]
  simp only [smul_sub, smul_add, smul_smul, Complex.I_mul_I, neg_one_smul]
  module

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
      | simpa [Pi.neg_def] using (Real.hasDerivAt_sin 0).neg

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

private theorem isArchSmoothAt_archRotDerivAt_eq_of_hasArchCharacterAt₀_one {w : InfinitePlace F} {hw : w.IsReal}
    {φ : AdelicGL2 (𝓞 F) F → ℂ} (hφ : IsArchSmoothAt hw φ) (hwt : HasArchCharacterAt₀ F w (archWeightCharAt hw 1) φ) :
    archRotDerivAt hw φ = Complex.I • φ := by
  funext g
  have hopen := isOpen_setOf_det_ne_zero

  have hcurve : (fun θ : ℝ => φ (g * archRealLiftAt hw (rotationArray θ))) =
      fun θ : ℝ => (⟨Real.cos θ, Real.sin θ⟩ : ℂ) * φ g := by
    funext θ
    rw [archRealLiftAt_rotationArray, archRealGLAt_rotation, hwt (rotationAt hw θ) g, archWeightCharAt_one_rotationAt]

  have hder : HasDerivAt (fun θ : ℝ => (⟨Real.cos θ, Real.sin θ⟩ : ℂ) * φ g) (Complex.I * φ g) 0 := by
    have hfun : (fun θ : ℝ => (⟨Real.cos θ, Real.sin θ⟩ : ℂ) * φ g) =
        fun θ : ℝ => (((Real.cos θ : ℝ) : ℂ) + ((Real.sin θ : ℝ) : ℂ) * Complex.I) * φ g := by
      funext θ
      rw [Complex.mk_eq_add_mul_I]
    have h2 : HasDerivAt (fun θ : ℝ => ((Real.cos θ : ℝ) : ℂ) + ((Real.sin θ : ℝ) : ℂ) * Complex.I)
        (((-Real.sin 0 : ℝ) : ℂ) + ((Real.cos 0 : ℝ) : ℂ) * Complex.I) 0 :=
      ((Real.hasDerivAt_cos 0).ofReal_comp).add ((Real.hasDerivAt_sin 0).ofReal_comp.mul_const Complex.I)
    rw [hfun]
    simpa using h2.mul_const (φ g)

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
  rw [archRotDerivAt, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, (isArchSmoothAt_archDerivAt_apply_eq_fderiv hφ) .E g,
    (isArchSmoothAt_archDerivAt_apply_eq_fderiv hφ) .Fm g, ← _root_.map_sub, hdir]
  have hcomp : (fun e' => φ (g * archRealLiftAt hw e')) ∘ rotationArray =
      fun θ : ℝ => (⟨Real.cos θ, Real.sin θ⟩ : ℂ) * φ g := hcurve
  rw [hcomp] at hchain
  exact hchain.unique hder

private def reflJ : GL (Fin 2) ℝ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![(-1 : ℝ), 0; 0, 1] (by rw [Matrix.det_fin_two_of]; norm_num)

private theorem reflJ_coe : (reflJ : Matrix (Fin 2) (Fin 2) ℝ) = !![(-1 : ℝ), 0; 0, 1] := by
  simp [reflJ, Matrix.GeneralLinearGroup.mkOfDetNeZero]

private theorem reflJ_mul_reflJ : reflJ * reflJ = 1 := by
  refine Units.ext ?_
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [reflJ_coe, Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_fin_two]

private def reflSign : ArchDir → ℝ
  | .H => 1
  | .E => -1
  | .Fm => -1

private theorem archFlowMatrix_mul_reflJ (d : ArchDir) (t : ℝ) :
    archFlowMatrix d t * reflJ = reflJ * archFlowMatrix d (reflSign d * t) := by
  cases d <;> refine Units.ext ?_ <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [archFlowMatrix, reflSign, reflJ_coe, splitTorusGL2_coe, unipotentGL2_coe, lowerUnipotentGL2_coe,
      Matrix.mul_apply, Fin.sum_univ_two]

private theorem archFlowAt_mul_archRealGLAt_reflJ {w : InfinitePlace F} (hw : w.IsReal) (d : ArchDir) (t : ℝ) :
    archFlowAt hw d t * archRealGLAt hw reflJ = archRealGLAt hw reflJ * archFlowAt hw d (reflSign d * t) := by
  simp only [archFlowAt]
  rw [← map_mul, ← map_mul, archFlowMatrix_mul_reflJ]

private def reflAt {w : InfinitePlace F} (hw : w.IsReal) (φ : AdelicGL2 (𝓞 F) F → ℂ) : AdelicGL2 (𝓞 F) F → ℂ :=
  fun g => φ (g * archRealGLAt hw reflJ)

private theorem reflAt_reflAt {w : InfinitePlace F} (hw : w.IsReal) (φ : AdelicGL2 (𝓞 F) F → ℂ) :
    reflAt hw (reflAt hw φ) = φ := by
  funext g
  simp only [reflAt]
  rw [mul_assoc, ← map_mul, reflJ_mul_reflJ, map_one, mul_one]

private theorem archDerivAt_neg {w : InfinitePlace F} (hw : w.IsReal) (d : ArchDir) (φ : AdelicGL2 (𝓞 F) F → ℂ) :
    archDerivAt hw d (-φ) = -archDerivAt hw d φ := by
  rw [← neg_one_smul ℂ φ, archDerivAt_smul, neg_one_smul ℂ]

private theorem archDerivAt_reflAt {w : InfinitePlace F} (hw : w.IsReal) (d : ArchDir) (φ : AdelicGL2 (𝓞 F) F → ℂ) :
    archDerivAt hw d (reflAt hw φ) = reflSign d • reflAt hw (archDerivAt hw d φ) := by
  funext g
  have hfun : (fun t : ℝ => reflAt hw φ (g * archFlowAt hw d t)) =
      fun t : ℝ => φ (g * archRealGLAt hw reflJ * archFlowAt hw d (reflSign d * t)) := by
    funext t
    simp only [reflAt]
    rw [mul_assoc g (archFlowAt hw d t), archFlowAt_mul_archRealGLAt_reflJ, ← mul_assoc]
  show deriv (fun t : ℝ => reflAt hw φ (g * archFlowAt hw d t)) 0 =
    reflSign d • archDerivAt hw d φ (g * archRealGLAt hw reflJ)
  rw [hfun, deriv_comp_mul_left (reflSign d) (fun s : ℝ => φ (g * archRealGLAt hw reflJ * archFlowAt hw d s)) 0,
    mul_zero]
  rfl

private theorem archCasimirAt_reflAt {w : InfinitePlace F} (hw : w.IsReal) (φ : AdelicGL2 (𝓞 F) F → ℂ) :
    archCasimirAt hw (reflAt hw φ) = reflAt hw (archCasimirAt hw φ) := by
  simp only [AutomorphicForm.archCasimirAt, archDerivAt_reflAt, reflSign, one_smul, neg_one_smul, archDerivAt_neg,
    neg_neg]
  funext g
  simp only [reflAt, Pi.neg_apply, Pi.add_apply, Pi.sub_apply, Pi.smul_apply]

private theorem archRotDerivAt_reflAt {w : InfinitePlace F} (hw : w.IsReal) (φ : AdelicGL2 (𝓞 F) F → ℂ) :
    archRotDerivAt hw (reflAt hw φ) = -reflAt hw (archRotDerivAt hw φ) := by
  simp only [archRotDerivAt, archDerivAt_reflAt, reflSign, neg_one_smul]
  funext g
  simp only [reflAt, Pi.neg_apply, Pi.sub_apply]
  ring

private theorem archLowerAt_reflAt {w : InfinitePlace F} (hw : w.IsReal) (φ : AdelicGL2 (𝓞 F) F → ℂ) :
    archLowerAt hw (reflAt hw φ) = reflAt hw (archRaiseAt hw φ) := by
  simp only [archLowerAt, archRaiseAt, archDerivAt_reflAt, reflSign, one_smul,
    neg_one_smul]
  funext g
  simp only [reflAt, Pi.neg_apply, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

private theorem isArchSmoothAt_reflAt {w : InfinitePlace F} {hw : w.IsReal} {φ : AdelicGL2 (𝓞 F) F → ℂ}
    (hφ : IsArchSmoothAt hw φ) : IsArchSmoothAt hw (reflAt hw φ) := by
  intro g
  have hdetJ : ((reflJ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ).det ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det _).1 reflJ.isUnit).ne_zero
  have hmaps : Set.MapsTo (fun e : Fin 2 → Fin 2 → ℝ =>
      (Matrix.of.symm (Matrix.of e * (reflJ : Matrix (Fin 2) (Fin 2) ℝ)) : Fin 2 → Fin 2 → ℝ))
      {e | (Matrix.of e).det ≠ 0} {e | (Matrix.of e).det ≠ 0} := by
    intro e he
    show (Matrix.of (Matrix.of.symm (Matrix.of e * (reflJ : Matrix (Fin 2) (Fin 2) ℝ)))).det ≠ 0
    rw [Equiv.apply_symm_apply, Matrix.det_mul]
    exact mul_ne_zero he hdetJ
  refine ((hφ g).comp ((contDiff_of_symm_mul_const (reflJ : Matrix (Fin 2) (Fin 2) ℝ)).contDiffOn) hmaps).congr ?_
  intro e he
  show φ (g * archRealLiftAt hw e * archRealGLAt hw reflJ) =
    φ (g * archRealLiftAt hw (Matrix.of.symm (Matrix.of e * (reflJ : Matrix (Fin 2) (Fin 2) ℝ))))
  rw [mul_assoc, archRealLiftAt_mul_archRealGLAt hw he]

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

private theorem isArchSmoothAt_archCasimirAt_archDerivAt_H {w : InfinitePlace F} {hw : w.IsReal} {φ : AdelicGL2
    (𝓞 F) F → ℂ}
    (hφ : IsArchSmoothAt hw φ) :
    archCasimirAt hw (archDerivAt hw .H φ) = archDerivAt hw .H (archCasimirAt hw φ) := by
  have hH := hφ.archDerivAt .H
  have hF := hφ.archDerivAt .Fm
  have hHH := hH.archDerivAt .H
  have hEF := hF.archDerivAt .E
  simp only [AutomorphicForm.archCasimirAt, archDerivAt_neg, archDerivAt_smul,
    archDerivAt_add ((hHH.smul (1 / 4 : ℂ)).sub (hH.smul (1 / 2 : ℂ))) hEF .H,
    archDerivAt_sub (hHH.smul (1 / 4 : ℂ)) (hH.smul (1 / 2 : ℂ)) .H, (isArchSmoothAt_archDerivAt_Fm_H hφ),
    archDerivAt_add (hF.archDerivAt .H) (hF.add hF) .E, archDerivAt_add hF hF .E, (isArchSmoothAt_archDerivAt_E_H hF)]
  funext g
  simp only [Pi.neg_apply, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

private theorem isArchSmoothAt_archCasimirAt_archDerivAt_E {w : InfinitePlace F} {hw : w.IsReal} {φ : AdelicGL2
    (𝓞 F) F → ℂ}
    (hφ : IsArchSmoothAt hw φ) :
    archCasimirAt hw (archDerivAt hw .E φ) = archDerivAt hw .E (archCasimirAt hw φ) := by
  have hH := hφ.archDerivAt .H
  have hE := hφ.archDerivAt .E
  have hF := hφ.archDerivAt .Fm
  have hHH := hH.archDerivAt .H
  have hEF := hF.archDerivAt .E
  simp only [AutomorphicForm.archCasimirAt, archDerivAt_neg, archDerivAt_smul,
    archDerivAt_add ((hHH.smul (1 / 4 : ℂ)).sub (hH.smul (1 / 2 : ℂ))) hEF .E,
    archDerivAt_sub (hHH.smul (1 / 4 : ℂ)) (hH.smul (1 / 2 : ℂ)) .E, (isArchSmoothAt_archDerivAt_E_H hH),
        (isArchSmoothAt_archDerivAt_E_H hφ),
    archDerivAt_sub (hE.archDerivAt .H) (hE.add hE) .H, archDerivAt_add hE hE .H, (isArchSmoothAt_archDerivAt_Fm_E hφ),
    archDerivAt_sub hEF hH .E]
  funext g
  simp only [Pi.neg_apply, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

private theorem isArchSmoothAt_archCasimirAt_archDerivAt_Fm {w : InfinitePlace F} {hw : w.IsReal} {φ : AdelicGL2
    (𝓞 F) F → ℂ}
    (hφ : IsArchSmoothAt hw φ) :
    archCasimirAt hw (archDerivAt hw .Fm φ) = archDerivAt hw .Fm (archCasimirAt hw φ) := by
  have hH := hφ.archDerivAt .H
  have hF := hφ.archDerivAt .Fm
  have hHH := hH.archDerivAt .H
  have hEF := hF.archDerivAt .E
  simp only [AutomorphicForm.archCasimirAt, archDerivAt_neg, archDerivAt_smul,
    archDerivAt_add ((hHH.smul (1 / 4 : ℂ)).sub (hH.smul (1 / 2 : ℂ))) hEF .Fm,
    archDerivAt_sub (hHH.smul (1 / 4 : ℂ)) (hH.smul (1 / 2 : ℂ)) .Fm, (isArchSmoothAt_archDerivAt_Fm_H hH),
        (isArchSmoothAt_archDerivAt_Fm_H hφ),
    archDerivAt_add (hF.archDerivAt .H) (hF.add hF) .H, archDerivAt_add hF hF .H, (isArchSmoothAt_archDerivAt_Fm_E hF)]
  funext g
  simp only [Pi.neg_apply, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

private theorem archCasimirAt_sub {w : InfinitePlace F} {hw : w.IsReal} {φ ψ : AdelicGL2 (𝓞 F) F → ℂ}
    (hφ : IsArchSmoothAt hw φ) (hψ : IsArchSmoothAt hw ψ) :
    archCasimirAt hw (φ - ψ) = archCasimirAt hw φ - archCasimirAt hw ψ := by
  rw [sub_eq_add_neg φ ψ, ← neg_one_smul ℂ ψ, archCasimirAt_add hφ (hψ.smul (-1)), archCasimirAt_smul, neg_one_smul ℂ]
  exact (sub_eq_add_neg _ _).symm

private theorem isArchSmoothAt_archCasimirAt_archLowerAt {w : InfinitePlace F} {hw : w.IsReal} {φ : AdelicGL2 (𝓞
    F) F → ℂ}
    (hφ : IsArchSmoothAt hw φ) :
    archCasimirAt hw (archLowerAt hw φ) = archLowerAt hw (archCasimirAt hw φ) := by
  have hH := hφ.archDerivAt .H
  have hE := hφ.archDerivAt .E
  have hF := hφ.archDerivAt .Fm
  show archCasimirAt hw (archDerivAt hw .H φ - Complex.I • (archDerivAt hw .E φ + archDerivAt hw .Fm φ)) =
    archLowerAt hw (archCasimirAt hw φ)
  rw [archCasimirAt_sub hH ((hE.add hF).smul Complex.I), archCasimirAt_smul, archCasimirAt_add hE hF,
    (isArchSmoothAt_archCasimirAt_archDerivAt_H hφ), (isArchSmoothAt_archCasimirAt_archDerivAt_E hφ),
        (isArchSmoothAt_archCasimirAt_archDerivAt_Fm hφ)]
  rfl

private theorem archLowerAt_smul {w : InfinitePlace F} (hw : w.IsReal) (c : ℂ) (φ : AdelicGL2 (𝓞 F) F → ℂ) :
    archLowerAt hw (c • φ) = c • archLowerAt hw φ := by
  simp only [archLowerAt, archDerivAt_smul]
  module

private theorem reflAt_smul {w : InfinitePlace F} (hw : w.IsReal) (c : ℂ) (φ : AdelicGL2 (𝓞 F) F → ℂ) :
    reflAt hw (c • φ) = c • reflAt hw φ := rfl

private theorem isArchSmoothAt_archCasimirAt_reflAt_archLowerAt {w : InfinitePlace F} {hw : w.IsReal}
    {φ : AdelicGL2 (𝓞 F) F → ℂ} (hφ : IsArchSmoothAt hw φ) {lam : ℂ} (hlam : archCasimirAt hw φ = lam • φ) :
    archCasimirAt hw (reflAt hw (archLowerAt hw φ)) = lam • reflAt hw (archLowerAt hw φ) := by
  rw [archCasimirAt_reflAt, (isArchSmoothAt_archCasimirAt_archLowerAt hφ), hlam, archLowerAt_smul, reflAt_smul]

private theorem isArchSmoothAt_archRotDerivAt_archLowerAt {w : InfinitePlace F} {hw : w.IsReal} {φ : AdelicGL2
    (𝓞 F) F → ℂ}
    (hφ : IsArchSmoothAt hw φ) :
    archRotDerivAt hw (archLowerAt hw φ) =
      archLowerAt hw (archRotDerivAt hw φ) - (2 * Complex.I) • archLowerAt hw φ := by
  have hH := hφ.archDerivAt .H
  have hE := hφ.archDerivAt .E
  have hF := hφ.archDerivAt .Fm
  simp only [archRotDerivAt, archLowerAt, archDerivAt_smul,
    archDerivAt_sub hH ((hE.add hF).smul Complex.I) .E, archDerivAt_sub hH ((hE.add hF).smul Complex.I) .Fm,
    archDerivAt_add hE hF .E, archDerivAt_add hE hF .Fm, archDerivAt_sub hE hF .H, archDerivAt_sub hE hF .E,
    archDerivAt_sub hE hF .Fm, (isArchSmoothAt_archDerivAt_E_H hφ), (isArchSmoothAt_archDerivAt_Fm_H hφ),
        (isArchSmoothAt_archDerivAt_Fm_E hφ)]
  funext g
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  linear_combination (-2 * (archDerivAt hw .E φ g + archDerivAt hw .Fm φ g)) * Complex.I_sq

private theorem isArchSmoothAt_archRotDerivAt_archLowerAt_of_eq {w : InfinitePlace F} {hw : w.IsReal}
    {φ : AdelicGL2 (𝓞 F) F → ℂ} (hφ : IsArchSmoothAt hw φ) (hW : archRotDerivAt hw φ = Complex.I • φ) :
    archRotDerivAt hw (archLowerAt hw φ) = (-Complex.I) • archLowerAt hw φ := by
  rw [(isArchSmoothAt_archRotDerivAt_archLowerAt hφ), hW, archLowerAt_smul]
  module

private theorem isArchSmoothAt_archRotDerivAt_reflAt_archLowerAt {w : InfinitePlace F} {hw : w.IsReal}
    {φ : AdelicGL2 (𝓞 F) F → ℂ} (hφ : IsArchSmoothAt hw φ) (hW : archRotDerivAt hw φ = Complex.I • φ) :
    archRotDerivAt hw (reflAt hw (archLowerAt hw φ)) = Complex.I • reflAt hw (archLowerAt hw φ) := by
  rw [archRotDerivAt_reflAt, (isArchSmoothAt_archRotDerivAt_archLowerAt_of_eq hφ) hW, reflAt_smul]
  module

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
      | simpa [Pi.neg_def] using (Real.hasDerivAt_sin θ).neg

private theorem mulRightArrayCLM_E_sub_Fm_rotationArray (θ : ℝ) :
    mulRightArrayCLM (archDirMatrix .E) (rotationArray θ) - mulRightArrayCLM (archDirMatrix .Fm) (rotationArray θ) =
      (![![-Real.sin θ, Real.cos θ], ![-Real.cos θ, -Real.sin θ]] : Fin 2 → Fin 2 → ℝ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [mulRightArrayCLM_apply, archDirMatrix, rotationArray, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.of_apply, Matrix.of_symm_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one]

private theorem exp_neg_ofReal_mul_I_mul_exp (θ : ℝ) :
    Complex.exp ((θ : ℂ) * Complex.I) * Complex.exp (-((θ : ℂ) * Complex.I)) = 1 := by
  rw [← Complex.exp_add, add_neg_cancel, Complex.exp_zero]

private theorem exp_ofReal_mul_I_eq_mk (θ : ℝ) : Complex.exp ((θ : ℂ) * Complex.I) = ⟨Real.cos θ, Real.sin θ⟩ := by
  refine Complex.ext ?_ ?_
  · exact Complex.exp_ofReal_mul_I_re θ
  · exact Complex.exp_ofReal_mul_I_im θ

private theorem isArchSmoothAt_apply_mul_archRealLiftAt_rotationArray {w : InfinitePlace F} {hw : w.IsReal}
    {φ : AdelicGL2 (𝓞 F) F → ℂ} (hφ : IsArchSmoothAt hw φ) (hW : archRotDerivAt hw φ = Complex.I • φ)
    (θ : ℝ) (g : AdelicGL2 (𝓞 F) F) :
    φ (g * archRealLiftAt hw (rotationArray θ)) = (⟨Real.cos θ, Real.sin θ⟩ : ℂ) * φ g := by
  have hopen := isOpen_setOf_det_ne_zero
  set f : ℝ → ℂ := fun θ => φ (g * archRealLiftAt hw (rotationArray θ)) with hf

  have hf' : ∀ θ : ℝ, HasDerivAt f (Complex.I * f θ) θ := by
    intro θ
    have hΦ : HasFDerivAt (fun e' => φ (g * archRealLiftAt hw e'))
        (fderiv ℝ (fun e' => φ (g * archRealLiftAt hw e')) (rotationArray θ)) (rotationArray θ) :=
      (((hφ g).contDiffAt (hopen.mem_nhds (det_of_rotationArray θ))).differentiableAt (by simp)).hasFDerivAt
    have hchain := hΦ.comp_hasDerivAt θ (hasDerivAt_rotationArray' θ)
    have hkey : fderiv ℝ (fun e' => φ (g * archRealLiftAt hw e')) (rotationArray θ)
        (![![-Real.sin θ, Real.cos θ], ![-Real.cos θ, -Real.sin θ]] : Fin 2 → Fin 2 → ℝ) = Complex.I * f θ := by
      rw [← mulRightArrayCLM_E_sub_Fm_rotationArray, _root_.map_sub,
        ← (isArchSmoothAt_archDerivAt_apply_mul_archRealLiftAt hφ) .E g (det_of_rotationArray θ),
        ← (isArchSmoothAt_archDerivAt_apply_mul_archRealLiftAt hφ) .Fm g (det_of_rotationArray θ)]
      have h := congrFun hW (g * archRealLiftAt hw (rotationArray θ))
      simp only [archRotDerivAt, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at h
      exact h
    rw [hkey] at hchain
    exact hchain

  have hu : ∀ θ : ℝ,
      HasDerivAt (fun θ : ℝ => Complex.exp (-((θ : ℂ) * Complex.I)) * f θ)
        (Complex.exp (-((θ : ℂ) * Complex.I)) * -(((1 : ℝ) : ℂ) * Complex.I) * f θ +
          Complex.exp (-((θ : ℂ) * Complex.I)) * (Complex.I * f θ)) θ := by
    intro θ
    exact ((((hasDerivAt_id θ).ofReal_comp).mul_const Complex.I).neg.cexp).mul (hf' θ)
  have hconst : ∀ θ : ℝ, Complex.exp (-((θ : ℂ) * Complex.I)) * f θ = f 0 := by
    intro θ
    have h := is_const_of_deriv_eq_zero (fun θ => (hu θ).differentiableAt) (fun θ => by
      rw [(hu θ).deriv]
      push_cast
      ring) θ 0
    simpa using h
  have hf0 : f 0 = φ g := by
    simp only [hf, rotationArray_zero, archRealLiftAt_of_symm_one, mul_one]
  calc f θ = Complex.exp ((θ : ℂ) * Complex.I) * (Complex.exp (-((θ : ℂ) * Complex.I)) * f θ) := by
        rw [← mul_assoc, exp_neg_ofReal_mul_I_mul_exp, one_mul]
    _ = (⟨Real.cos θ, Real.sin θ⟩ : ℂ) * φ g := by rw [hconst θ, hf0, exp_ofReal_mul_I_eq_mk]

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

private theorem isArchSmoothAt_hasArchCharacterAt₀_one_of_archRotDerivAt {w : InfinitePlace F} {hw : w.IsReal}
    {φ : AdelicGL2 (𝓞 F) F → ℂ} (hφ : IsArchSmoothAt hw φ) (hW : archRotDerivAt hw φ = Complex.I • φ) :
    HasArchCharacterAt₀ F w (archWeightCharAt hw 1) φ := by
  intro k g
  obtain ⟨θ, rfl⟩ := exists_rotationAt_eq hw k
  rw [archWeightCharAt_one_rotationAt, ← archRealGLAt_rotation, ← archRealLiftAt_rotationArray]
  exact (isArchSmoothAt_apply_mul_archRealLiftAt_rotationArray hφ) hW θ g

private theorem isArchSmoothAt_hasArchCharacterAt₀_one_reflAt_archLowerAt {w : InfinitePlace F} {hw : w.IsReal}
    {φ : AdelicGL2 (𝓞 F) F → ℂ} (hφ : IsArchSmoothAt hw φ) (hwt : HasArchCharacterAt₀ F w (archWeightCharAt hw 1) φ) :
    HasArchCharacterAt₀ F w (archWeightCharAt hw 1) (reflAt hw (archLowerAt hw φ)) :=
  (isArchSmoothAt_hasArchCharacterAt₀_one_of_archRotDerivAt ((isArchSmoothAt_reflAt (isArchSmoothAt_archLowerAt hφ))))
    ((isArchSmoothAt_archRotDerivAt_reflAt_archLowerAt hφ)
        ((isArchSmoothAt_archRotDerivAt_eq_of_hasArchCharacterAt₀_one hφ) hwt))

private def archT {w : InfinitePlace F} (hw : w.IsReal) (φ : AdelicGL2 (𝓞 F) F → ℂ) : AdelicGL2 (𝓞 F) F → ℂ :=
  reflAt hw (archLowerAt hw φ)

private theorem isArchSmoothAt_archT {w : InfinitePlace F} {hw : w.IsReal} {φ : AdelicGL2 (𝓞 F) F → ℂ}
    (hφ : IsArchSmoothAt hw φ) : IsArchSmoothAt hw (archT hw φ) :=
  (isArchSmoothAt_reflAt (isArchSmoothAt_archLowerAt hφ))

private theorem archLowerAt_add {w : InfinitePlace F} {hw : w.IsReal} {φ ψ : AdelicGL2 (𝓞 F) F → ℂ}
    (hφ : IsArchSmoothAt hw φ) (hψ : IsArchSmoothAt hw ψ) :
    archLowerAt hw (φ + ψ) = archLowerAt hw φ + archLowerAt hw ψ := by
  simp only [archLowerAt, archDerivAt_add hφ hψ]
  module

private theorem reflAt_add {w : InfinitePlace F} (hw : w.IsReal) (φ ψ : AdelicGL2 (𝓞 F) F → ℂ) :
    reflAt hw (φ + ψ) = reflAt hw φ + reflAt hw ψ := rfl

private theorem archT_add {w : InfinitePlace F} {hw : w.IsReal} {φ ψ : AdelicGL2 (𝓞 F) F → ℂ}
    (hφ : IsArchSmoothAt hw φ) (hψ : IsArchSmoothAt hw ψ) : archT hw (φ + ψ) = archT hw φ + archT hw ψ := by
  simp only [archT, archLowerAt_add hφ hψ, reflAt_add]

private theorem archT_smul {w : InfinitePlace F} (hw : w.IsReal) (c : ℂ) (φ : AdelicGL2 (𝓞 F) F → ℂ) :
    archT hw (c • φ) = c • archT hw φ := by
  simp only [archT, archLowerAt_smul, reflAt_smul]

private theorem archRotDerivAt_smul {w : InfinitePlace F} (hw : w.IsReal) (c : ℂ) (φ : AdelicGL2 (𝓞 F) F → ℂ) :
    archRotDerivAt hw (c • φ) = c • archRotDerivAt hw φ := by
  simp only [archRotDerivAt, archDerivAt_smul]
  exact (smul_sub c _ _).symm

private theorem isArchSmoothAt_archCasimirAt_archT {w : InfinitePlace F} {hw : w.IsReal} {φ : AdelicGL2 (𝓞 F) F → ℂ}
    (hφ : IsArchSmoothAt hw φ) {lam : ℂ} (hlam : archCasimirAt hw φ = lam • φ) :
    archCasimirAt hw (archT hw φ) = lam • archT hw φ :=
  (isArchSmoothAt_archCasimirAt_reflAt_archLowerAt hφ) hlam

private theorem isArchSmoothAt_hasArchCharacterAt₀_one_archT {w : InfinitePlace F} {hw : w.IsReal}
    {φ : AdelicGL2 (𝓞 F) F → ℂ} (hφ : IsArchSmoothAt hw φ) (hwt : HasArchCharacterAt₀ F w (archWeightCharAt hw 1) φ) :
    HasArchCharacterAt₀ F w (archWeightCharAt hw 1) (archT hw φ) :=
  (isArchSmoothAt_hasArchCharacterAt₀_one_reflAt_archLowerAt hφ) hwt

private theorem isArchSmoothAt_archT_archT {w : InfinitePlace F} {hw : w.IsReal} {φ : AdelicGL2 (𝓞 F) F → ℂ}
    (hφ : IsArchSmoothAt hw φ) {lam : ℂ} (hlam : archCasimirAt hw φ = lam • φ)
    (hW : archRotDerivAt hw φ = Complex.I • φ) : archT hw (archT hw φ) = (1 - 4 * lam) • φ := by
  simp only [archT]
  rw [archLowerAt_reflAt, reflAt_reflAt, (isArchSmoothAt_archRaiseAt_archLowerAt hφ), hlam, hW,
      archRotDerivAt_smul, hW]
  funext g
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  linear_combination (-(φ g)) * Complex.I_mul_I

private theorem mul_self_sub_eq_one_sub_four_mul_laplaceEigenvalue (u₁ : ℂ) (a₁ : ZMod 2) (u₂ : ℂ) (a₂ : ZMod 2) :
    (u₁ - u₂) * (u₁ - u₂) =
      1 - 4 * LanglandsTunnell.RealArchParam.laplaceEigenvalue
        (LanglandsTunnell.RealArchParam.principal u₁ a₁ u₂ a₂) := by
  rw [LanglandsTunnell.RealArchParam.laplaceEigenvalue_principal]
  ring

section Eigenvectors

variable {w : InfinitePlace F} {hw : w.IsReal} {φ : AdelicGL2 (𝓞 F) F → ℂ}

private theorem isArchSmoothAt_add_smul_archT (hφ : IsArchSmoothAt hw φ) (c : ℂ) : IsArchSmoothAt hw (φ + c •
    archT hw φ) :=
  hφ.add ((isArchSmoothAt_archT hφ).smul c)

private theorem isArchSmoothAt_archCasimirAt_add_smul_archT (hφ : IsArchSmoothAt hw φ) {lam : ℂ}
    (hlam : archCasimirAt hw φ = lam • φ) (c : ℂ) :
    archCasimirAt hw (φ + c • archT hw φ) = lam • (φ + c • archT hw φ) := by
  rw [archCasimirAt_add hφ ((isArchSmoothAt_archT hφ).smul c), archCasimirAt_smul,
      (isArchSmoothAt_archCasimirAt_archT hφ) hlam, hlam]
  module

private theorem hasArchCharacterAt₀_add {χ : rowIsometrySubgroup₀ w.Completion →* ℂˣ} {φ ψ : AdelicGL2 (𝓞 F) F → ℂ}
    (h₁ : HasArchCharacterAt₀ F w χ φ) (h₂ : HasArchCharacterAt₀ F w χ ψ) : HasArchCharacterAt₀ F w χ (φ + ψ) := by
  intro k g
  rw [Pi.add_apply, Pi.add_apply, h₁ k g, h₂ k g]
  ring

private theorem hasArchCharacterAt₀_smul {χ : rowIsometrySubgroup₀ w.Completion →* ℂˣ} {φ : AdelicGL2 (𝓞 F) F →
    ℂ} (c : ℂ)
    (h : HasArchCharacterAt₀ F w χ φ) : HasArchCharacterAt₀ F w χ (c • φ) := by
  intro k g
  rw [Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul, h k g]
  ring

private theorem isArchSmoothAt_hasArchCharacterAt₀_one_add_smul_archT (hφ : IsArchSmoothAt hw φ)
    (hwt : HasArchCharacterAt₀ F w (archWeightCharAt hw 1) φ) (c : ℂ) :
    HasArchCharacterAt₀ F w (archWeightCharAt hw 1) (φ + c • archT hw φ) :=
  hasArchCharacterAt₀_add hwt (hasArchCharacterAt₀_smul c ((isArchSmoothAt_hasArchCharacterAt₀_one_archT hφ) hwt))

private theorem isArchSmoothAt_archT_add_inv_smul_archT (hφ : IsArchSmoothAt hw φ) {lam : ℂ}
    (hlam : archCasimirAt hw φ = lam • φ) (hW : archRotDerivAt hw φ = Complex.I • φ) {μ : ℂ}
    (hμ : μ * μ = 1 - 4 * lam) (hμ0 : μ ≠ 0) :
    archT hw (φ + μ⁻¹ • archT hw φ) = μ • (φ + μ⁻¹ • archT hw φ) := by
  rw [archT_add hφ ((isArchSmoothAt_archT hφ).smul μ⁻¹), archT_smul, (isArchSmoothAt_archT_archT hφ) hlam hW,
      ← hμ, smul_smul,
    inv_mul_cancel_left₀ hμ0, smul_add, smul_smul, mul_inv_cancel₀ hμ0, one_smul, add_comm]

private theorem add_inv_smul_archT_add_add_neg_inv_smul_archT (μ : ℂ) :
    (φ + μ⁻¹ • archT hw φ) + (φ + (-μ)⁻¹ • archT hw φ) = (2 : ℂ) • φ := by
  rw [inv_neg]
  module

private theorem neg_mul_neg_eq_of_mul_self_eq {μ κ : ℂ} (hμ : μ * μ = κ) : -μ * -μ = κ := by
  rw [neg_mul_neg, hμ]

end Eigenvectors

section CoefficientIdentities

open MeasureTheory

private theorem whittakerCoefficient_apply_mul (pins : CarrierPins F) (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ)
    (φ : AdelicGL2 (𝓞 F) F → ℂ) (α : F) (g t : AdelicGL2 (𝓞 F) F) :
    whittakerCoefficient F pins ψ φ α (g * t) = whittakerCoefficient F pins ψ (fun h => φ (h * t)) α g := by
  unfold whittakerCoefficient
  simp only [mul_assoc]

private theorem whittakerCoefficient_const_mul (pins : CarrierPins F) (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (c : ℂ)
    (φ : AdelicGL2 (𝓞 F) F → ℂ) (α : F) (g : AdelicGL2 (𝓞 F) F) :
    whittakerCoefficient F pins ψ (fun h => c * φ h) α g = c * whittakerCoefficient F pins ψ φ α g := by
  simp only [whittakerCoefficient, mul_assoc, integral_const_mul]

private theorem whittakerCoefficient_smul (pins : CarrierPins F) (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (c : ℂ)
    (φ : AdelicGL2 (𝓞 F) F → ℂ) (α : F) (g : AdelicGL2 (𝓞 F) F) :
    whittakerCoefficient F pins ψ (c • φ) α g = c * whittakerCoefficient F pins ψ φ α g :=
  whittakerCoefficient_const_mul pins ψ c φ α g

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

private theorem hasArchCharacterAt₀_whittakerCoefficient (pins : CarrierPins F) (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ)
    {w : InfinitePlace F} {χ : rowIsometrySubgroup₀ w.Completion →* ℂˣ} {φ : AdelicGL2 (𝓞 F) F → ℂ}
    (hφ : HasArchCharacterAt₀ F w χ φ) (α : F) : HasArchCharacterAt₀ F w χ (whittakerCoefficient F pins ψ φ α) := by
  intro k g
  rw [whittakerCoefficient_apply_mul, funext (hφ k), whittakerCoefficient_const_mul]

end CoefficientIdentities

section TorusCalculus

variable {w : InfinitePlace F} {hw : w.IsReal}

private theorem archLowerAt_eq_of_archRotDerivAt_eq {φ : AdelicGL2 (𝓞 F) F → ℂ} (hW : archRotDerivAt hw φ =
    Complex.I • φ) :
    archLowerAt hw φ = archDerivAt hw .H φ - (2 * Complex.I) • archDerivAt hw .E φ - φ := by
  have hF : archDerivAt hw .Fm φ = archDerivAt hw .E φ - Complex.I • φ := by
    rw [← hW, archRotDerivAt, sub_sub_cancel]
  rw [archLowerAt, hF]
  funext g
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  linear_combination (φ g) * Complex.I_mul_I

private theorem archDerivAt_H_apply_eq_of_forall_flow {Wc : AdelicGL2 (𝓞 F) F → ℂ} {h : AdelicGL2 (𝓞 F) F} {u :
    ℂ} {s : ℝ}
    {P : ℝ → ℂ} {P' : ℂ} (hP : HasDerivAt P P' s)
    (hflow : ∀ t : ℝ, Wc (h * archFlowAt hw .H t) = Complex.exp (-(t : ℂ) * u) * P (s * Real.exp (2 * t))) :
    archDerivAt hw .H Wc h = 2 * s * P' - u * P s := by
  show deriv (fun t : ℝ => Wc (h * archFlowAt hw .H t)) 0 = _
  rw [funext hflow]
  have h1 : HasDerivAt (fun t : ℝ => Complex.exp (-(t : ℂ) * u))
      (Complex.exp (-((0 : ℝ) : ℂ) * u) * (-((1 : ℝ) : ℂ) * u)) 0 :=
    (((hasDerivAt_id (0 : ℝ)).ofReal_comp).neg.mul_const u).cexp
  have hc : HasDerivAt (fun t : ℝ => s * Real.exp (2 * t)) (s * (Real.exp (2 * 0) * (2 * 1))) 0 :=
    (((hasDerivAt_id' (0 : ℝ)).const_mul (2 : ℝ)).exp).const_mul s
  have hs0 : s * Real.exp (2 * 0) = s := by simp
  have hP₀ : HasDerivAt P P' (s * Real.exp (2 * 0)) := by rwa [hs0]
  have h2 : HasDerivAt (fun t : ℝ => P (s * Real.exp (2 * t))) ((s * (Real.exp (2 * 0) * (2 * 1))) • P') 0 :=
    hP₀.scomp (0 : ℝ) hc
  rw [show (fun t : ℝ => Complex.exp (-(t : ℂ) * u) * P (s * Real.exp (2 * t)))
      = (fun t : ℝ => Complex.exp (-(t : ℂ) * u)) * (fun t : ℝ => P (s * Real.exp (2 * t))) from rfl,
    (h1.mul h2).deriv]
  simp only [Complex.ofReal_zero, neg_zero, zero_mul, Complex.exp_zero, Complex.ofReal_one, mul_zero, Real.exp_zero,
    mul_one, one_mul, Complex.real_smul]
  push_cast
  ring

private theorem archDerivAt_E_apply_eq_of_forall_flow {Wc : AdelicGL2 (𝓞 F) F → ℂ} {h : AdelicGL2 (𝓞 F) F} {s : ℝ}
    (hflow : ∀ x : ℝ, Wc (h * archFlowAt hw .E x) =
      Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((s * x : ℝ) : ℂ)) * Wc h) :
    archDerivAt hw .E Wc h = 2 * (Real.pi : ℂ) * Complex.I * (s : ℂ) * Wc h := by
  show deriv (fun x : ℝ => Wc (h * archFlowAt hw .E x)) 0 = _
  rw [funext hflow]
  have h1 : HasDerivAt (fun x : ℝ => Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((s * x : ℝ) : ℂ)))
      (Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((s * 0 : ℝ) : ℂ)) *
        (2 * (Real.pi : ℂ) * Complex.I * ((s * 1 : ℝ) : ℂ))) 0 :=
    ((((hasDerivAt_id' (0 : ℝ)).const_mul s).ofReal_comp).const_mul (2 * (Real.pi : ℂ) * Complex.I)).cexp
  rw [(h1.mul_const (Wc h)).deriv]
  norm_num

private theorem lowering_relation_of_archLowerAt_apply {Wc : AdelicGL2 (𝓞 F) F → ℂ} {h : AdelicGL2 (𝓞 F) F} {u c
    Q P' : ℂ}
    {s : ℝ} {P : ℝ → ℂ} (hW : archRotDerivAt hw Wc = Complex.I • Wc)
    (hH : archDerivAt hw .H Wc h = 2 * s * P' - u * P s)
    (hE : archDerivAt hw .E Wc h = 2 * (Real.pi : ℂ) * Complex.I * (s : ℂ) * Wc h) (hWc : Wc h = P s)
    (hX : archLowerAt hw Wc h = c * Q) :
    c * Q = 2 * s * P' + (4 * (Real.pi : ℂ) * s - u - 1) * P s := by
  rw [← hX, archLowerAt_eq_of_archRotDerivAt_eq hW, Pi.sub_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hH, hE,
    hWc]
  linear_combination (-(4 * (Real.pi : ℂ) * s * P s)) * Complex.I_mul_I

private theorem lowering_expression_mul_of_two_mul_deriv_eq {R f : ℝ → ℂ} {R' f' u : ℂ} {t : ℝ} (hR : HasDerivAt
    R R' t)
    (hf : HasDerivAt f f' t) (hhom : 2 * t * R' = u * R t) :
    2 * t * (R' * f t + R t * f') + (4 * (Real.pi : ℂ) * t - u - 1) * (R t * f t) =
      R t * (2 * t * f' + (4 * (Real.pi : ℂ) * t - 1) * f t) ∧
    HasDerivAt (fun y => R y * f y) (R' * f t + R t * f') t :=
  ⟨by linear_combination (f t) * hhom, hR.mul hf⟩

private theorem exists_hasDerivAt_sqrt_cpow (e : ℂ) {t : ℝ} (ht : 0 < t) :
    ∃ R' : ℂ, HasDerivAt (fun y : ℝ => ((Real.sqrt y : ℝ) : ℂ) ^ e) R' t ∧
      2 * (t : ℂ) * R' = e * ((Real.sqrt t : ℝ) : ℂ) ^ e := by
  by_cases he : e = 0
  · refine ⟨0, ?_, by simp [he]⟩
    simp only [he, Complex.cpow_zero]
    exact hasDerivAt_const t (1 : ℂ)
  · have hs : Real.sqrt t ≠ 0 := (Real.sqrt_pos.mpr ht).ne'
    have hs' : ((Real.sqrt t : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hs
    have hsq : HasDerivAt (fun y : ℝ => Real.sqrt y) (1 / (2 * Real.sqrt t)) t := (hasDerivAt_id' t).sqrt ht.ne'
    have hcomp := (hasDerivAt_ofReal_cpow_const hs he).scomp t hsq
    refine ⟨_, hcomp, ?_⟩
    have htt : (t : ℂ) = ((Real.sqrt t : ℝ) : ℂ) * ((Real.sqrt t : ℝ) : ℂ) := by
      rw [← Complex.ofReal_mul, Real.mul_self_sqrt ht.le]
    have hpow : ((Real.sqrt t : ℝ) : ℂ) ^ (e - 1) * ((Real.sqrt t : ℝ) : ℂ) = ((Real.sqrt t : ℝ) : ℂ) ^ e := by
      rw [Complex.cpow_sub _ _ hs', Complex.cpow_one, div_mul_cancel₀ _ hs']
    rw [Complex.real_smul, htt, ← hpow]
    push_cast
    field_simp

private theorem lowering_relation_peeled {Wc : AdelicGL2 (𝓞 F) F → ℂ} {h : ℝ → AdelicGL2 (𝓞 F) F} {Fp f : ℝ → ℂ}
    {u₁ u₂ c : ℂ} (hW : archRotDerivAt hw Wc = Complex.I • Wc) (hT : archLowerAt hw Wc = c • reflAt hw Wc)
    (hval : ∀ s : ℝ, 0 < s → Wc (h s) = Fp s) (hrefl : ∀ s : ℝ, 0 < s → reflAt hw Wc (h s) = Fp (-s))
    (hflowH : ∀ s : ℝ, 0 < s → ∀ t : ℝ,
      Wc (h s * archFlowAt hw .H t) = Complex.exp (-(t : ℂ) * (u₁ + u₂ + 1)) * Fp (s * Real.exp (2 * t)))
    (hflowE : ∀ s : ℝ, 0 < s → ∀ x : ℝ,
      Wc (h s * archFlowAt hw .E x) = Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((s * x : ℝ) : ℂ)) * Wc (h s))
    (hpeel : ∀ t : ℝ, 0 < t → Fp t = ((Real.sqrt t : ℝ) : ℂ) ^ (u₁ + u₂ + 1) * f t)
    (hf : DifferentiableOn ℝ f (Set.Ioi 0)) :
    ∀ t : ℝ, 0 < t → c * Fp (-t) = ((Real.sqrt t : ℝ) : ℂ) ^ (u₁ + u₂ + 1)
      * (2 * (t : ℂ) * deriv f t + (4 * (Real.pi : ℂ) * (t : ℂ) - 1) * f t) := by
  intro t ht
  obtain ⟨R', hR, hhom⟩ := exists_hasDerivAt_sqrt_cpow (u₁ + u₂ + 1) ht
  have hft : HasDerivAt f (deriv f t) t := (hf.differentiableAt (Ioi_mem_nhds ht)).hasDerivAt
  obtain ⟨hexpr, hprod⟩ := lowering_expression_mul_of_two_mul_deriv_eq hR hft hhom
  have hFp : HasDerivAt Fp (R' * f t + ((Real.sqrt t : ℝ) : ℂ) ^ (u₁ + u₂ + 1) * deriv f t) t :=
    hprod.congr_of_eventuallyEq (Filter.eventuallyEq_of_mem (Ioi_mem_nhds ht) fun y hy => hpeel y hy)
  have hH := archDerivAt_H_apply_eq_of_forall_flow hFp (hflowH t ht)
  have hE := archDerivAt_E_apply_eq_of_forall_flow (hflowE t ht)
  have hX : archLowerAt hw Wc (h t) = c * Fp (-t) := by
    rw [hT, Pi.smul_apply, smul_eq_mul, hrefl t ht]
  have hrel := lowering_relation_of_archLowerAt_apply hW hH hE (hval t ht) hX
  rw [hpeel t ht] at hrel
  rw [hrel]
  exact hexpr

end TorusCalculus

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

private theorem tensorTestFn_add_smul (fa₁ fa₂ : GL (Fin 2) (InfiniteAdeleRing F) → ℂ)
    (ff : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F) → ℂ) (c : ℂ) :
    tensorTestFn fa₁ ff + c • tensorTestFn fa₂ ff = tensorTestFn (fa₁ + c • fa₂) ff := by
  funext g
  simp only [Pi.add_apply, Pi.smul_apply, tensorTestFn_apply, smul_eq_mul]
  ring

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

private theorem tensorTestFn_comp_inv_mul_of_glFin_eq_one (fa : GL (Fin 2) (InfiniteAdeleRing F) → ℂ)
    (ff : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F) → ℂ) {t : GL (Fin 2) (AdeleRing (𝓞 F) F)} (ht : glFin (𝓞 F) F t = 1) :
    (fun y => tensorTestFn fa ff (t⁻¹ * y)) = tensorTestFn (fun x => fa ((glArch (𝓞 F) F t)⁻¹ * x)) ff := by
  funext y
  simp only [tensorTestFn_apply, map_mul, map_inv, ht, inv_one, one_mul]

private theorem tensorTestFn_comp_inv_mul_adelicArchGLIncl (fa : GL (Fin 2) (InfiniteAdeleRing F) → ℂ)
    (ff : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F) → ℂ) (k : GL (Fin 2) (InfiniteAdeleRing F)) :
    (fun y => tensorTestFn fa ff ((adelicArchGLIncl F k)⁻¹ * y)) = tensorTestFn (fun x => fa (k⁻¹ * x)) ff := by
  funext y
  simp only [tensorTestFn_apply, map_mul, map_inv, glArch_adelicArchGLIncl, glFin_adelicArchGLIncl, inv_one, one_mul]

private def entryMulLeft (a : Fin 2 → Fin 2 → mixedEmbedding.mixedSpace F) :
    (Fin 2 → Fin 2 → mixedEmbedding.mixedSpace F) →ₗ[ℝ] (Fin 2 → Fin 2 → mixedEmbedding.mixedSpace F) where
  toFun e := fun i j => ∑ k, a i k * e k j
  map_add' e₁ e₂ := by
    funext i j
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' r e := by
    funext i j
    simp only [Pi.smul_apply, RingHom.id_apply, Finset.smul_sum, mul_smul_comm]

omit [NumberField F] in
private theorem archEntries_mul (m g : GL (Fin 2) (InfiniteAdeleRing F)) :
    archEntries F (m * g) = entryMulLeft (archEntries F m) (archEntries F g) := by
  funext i j
  simp only [archEntries_apply, entryMulLeft, LinearMap.coe_mk, AddHom.coe_mk, Units.val_mul, Matrix.mul_apply,
    map_sum, map_mul]

open scoped Classical in

private theorem isArchTestFactor_comp_mul_left {fa : GL (Fin 2) (InfiniteAdeleRing F) → ℂ} (h : IsArchTestFactor F fa)
    (m : GL (Fin 2) (InfiniteAdeleRing F)) : IsArchTestFactor F (fun x => fa (m * x)) := by
  obtain ⟨⟨Φ, hΦ, hfa⟩, hc⟩ := h
  refine ⟨⟨Φ ∘ LinearMap.toContinuousLinearMap (entryMulLeft (archEntries F m)),
    hΦ.comp (LinearMap.toContinuousLinearMap (entryMulLeft (archEntries F m))).contDiff, fun g => ?_⟩, ?_⟩
  · exact (hfa (m * g)).trans (congrArg Φ (archEntries_mul m g))
  · exact hc.comp_homeomorph (Homeomorph.mulLeft m)

private theorem isFactorizableTestFn_comp_inv_mul_adelicArchGLIncl_tensorTestFn {fa : GL (Fin 2)
    (InfiniteAdeleRing F) → ℂ}
    {ff : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F) → ℂ} (hfa : IsArchTestFactor F fa) (hff : IsFinTestFactor F ff)
    (k : GL (Fin 2) (InfiniteAdeleRing F)) :
    IsFactorizableTestFn F (fun y => tensorTestFn fa ff ((adelicArchGLIncl F k)⁻¹ * y)) := by
  rw [tensorTestFn_comp_inv_mul_adelicArchGLIncl]
  exact isFactorizableTestFn_tensorTestFn ((isArchTestFactor_comp_mul_left hfa) k⁻¹) hff

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

private theorem isIsotypicCuspFormAt_add_smul_comb_of_rightConv_tensorTestFn
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
    (hrep : rightConv ℚ φ (tensorTestFn fa ff) = φ) {w : InfinitePlace ℚ} (hw : w.IsReal) (cH cE cF c₀ : ℂ)
    {t : AdelicGL2 (𝓞 ℚ) ℚ} (ht : glFin (𝓞 ℚ) ℚ t = 1) :
    IsIsotypicCuspFormAt ℚ
      (productionPinsOf ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂)
        (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ))
      ξ Φ.level S Φ
      (φ + c₀ • fun g =>
        (cH • archDerivAt hw .H φ + cE • archDerivAt hw .E φ + cF • archDerivAt hw .Fm φ) (g * t)) := by

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

  have htr : (fun g => rightConv ℚ φ (tensorTestFn (cH • fH + cE • fE + cF • fF) ff) (g * t)) =
      rightConv ℚ φ (tensorTestFn (fun x => (cH • fH + cE • fE + cF • fF) ((glArch (𝓞 ℚ) ℚ t)⁻¹ * x)) ff) := by
    funext g
    rw [rightConv_apply_mul_eq_rightConv_comp_inv_mul_apply]
    exact congrFun (congrArg (rightConv ℚ φ) (tensorTestFn_comp_inv_mul_of_glFin_eq_one _ _ ht)) g
  have hXt : IsArchTestFactor ℚ fun x => (cH • fH + cE • fE + cF • fF) ((glArch (𝓞 ℚ) ℚ t)⁻¹ * x) :=
    (isArchTestFactor_comp_mul_left hfX) (glArch (𝓞 ℚ) ℚ t)⁻¹

  have hfinal : rightConv ℚ φ
      (tensorTestFn (fa + c₀ • fun x => (cH • fH + cE • fE + cF • fF) ((glArch (𝓞 ℚ) ℚ t)⁻¹ * x)) ff) =
        φ + c₀ • fun g =>
          (cH • archDerivAt hw .H φ + cE • archDerivAt hw .E φ + cF • archDerivAt hw .Fm φ) (g * t) := by
    rw [tensorTestFn_add,
        rightConv_add_right hφ.continuous (hcs _ hfa).1 (hcs _ hfa).2 (hcs _ ((isArchTestFactor_smul hXt) c₀)).1
      (hcs _ ((isArchTestFactor_smul hXt) c₀)).2, hrep, tensorTestFn_smul, rightConv_smul_right, ← hcomb, ← htr]
  rw [← hfinal]
  exact isIsotypicCuspFormAt_rightConv_of_isIsotypicCuspFormAt c u d₁ d₂ T hd hcov Φ hφ hne _
    (isFactorizableTestFn_tensorTestFn ((isArchTestFactor_add hfa) ((isArchTestFactor_smul hXt) c₀)) hff)
        (tensorTestFn_support_of_forall hffs)

end IsotypyOfConvolutions

end

end IsotypicReproduction

section CoefficientIntegrands

open MeasureTheory

variable {F : Type} [Field F] [NumberField F]

private theorem archFlowAt_H_eq {w : InfinitePlace F} (hw : w.IsReal) (t : ℝ) :
    archFlowAt hw .H t = archRealGLAt hw (splitTorusGL2 t) := rfl

private theorem archFlowAt_E_eq {w : InfinitePlace F} (hw : w.IsReal) (x : ℝ) :
    archFlowAt hw .E x = archRealGLAt hw (unipotentGL2 x) := rfl

private theorem whittakerCoefficientIntegrable_sub (pins : CarrierPins F) (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ)
    {φ₁ φ₂ : AdelicGL2 (𝓞 F) F → ℂ} {α : F} {g : AdelicGL2 (𝓞 F) F}
    (h₁ : WhittakerCoefficientIntegrable F pins ψ φ₁ α g) (h₂ : WhittakerCoefficientIntegrable F pins ψ φ₂ α g) :
    WhittakerCoefficientIntegrable F pins ψ (φ₁ - φ₂) α g := by
  unfold WhittakerCoefficientIntegrable at h₁ h₂ ⊢
  simp only [Pi.sub_apply, sub_mul]
  exact h₁.sub h₂

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

section SheetMatrices

private theorem splitTorusGL2_mul_unipotentGL2 (a x : ℝ) :
    splitTorusGL2 a * unipotentGL2 x = unipotentGL2 (Real.exp (2 * a) * x) * splitTorusGL2 a := by
  have h2a : Real.exp (2 * a) = Real.exp a * Real.exp a := by
    rw [← Real.exp_add]
    congr 1
    ring
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [splitTorusGL2, unipotentGL2, Matrix.mul_apply, Fin.sum_univ_two, h2a, Real.exp_neg] <;>
    first | done | (field_simp; done) | (field_simp; ring1)

private theorem J_mul_unipotentGL2 (z : ℝ) :
    UpperHalfPlane.J * unipotentGL2 z = unipotentGL2 (-z) * UpperHalfPlane.J := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [unipotentGL2, Matrix.mul_apply, Fin.sum_univ_two]

private theorem one_mul_unipotentGL2_eq (z : ℝ) :
    (1 : GL (Fin 2) ℝ) * unipotentGL2 z = unipotentGL2 (1 * z) * 1 := by
  simp

private theorem J_mul_unipotentGL2_eq (z : ℝ) :
    UpperHalfPlane.J * unipotentGL2 z = unipotentGL2 (-1 * z) * UpperHalfPlane.J := by
  rw [neg_one_mul]
  exact J_mul_unipotentGL2 z

end SheetMatrices

section SheetFlows

variable (F : Type) [Field F] [NumberField F]
variable {F}

private theorem sheetDatum_mul_archFlowAt_H
    {w : InfinitePlace F} (hw : w.IsReal) (m : GL (Fin 2) ℝ) {g : AdelicGL2 (𝓞 F) F}
    (hg : AdelicLevel.glArch (𝓞 F) F g = 1) {y : ℝ} (hy : 0 < y) (t : ℝ) :
    archRealGLAt hw (m * splitTorusGL2 (Real.log y / 2)) * g * archFlowAt hw .H t
      = archRealGLAt hw (m * splitTorusGL2 (Real.log (y * Real.exp (2 * t)) / 2)) * g := by
  have hlog : Real.log (y * Real.exp (2 * t)) / 2 = Real.log y / 2 + t := by
    rw [Real.log_mul hy.ne' (Real.exp_pos _).ne', Real.log_exp]
    ring
  show archRealGLAt hw (m * splitTorusGL2 (Real.log y / 2)) * g * archRealGLAt hw (splitTorusGL2 t) = _
  rw [mul_assoc, ← archRealGLAt_mul_comm_of_glArch_eq_one hw (splitTorusGL2 t) hg, ← mul_assoc,
    ← map_mul (archRealGLAt hw) (m * splitTorusGL2 (Real.log y / 2)) (splitTorusGL2 t), mul_assoc,
    ← splitTorusGL2_add, hlog]

private theorem sheetDatum_mul_archFlowAt_E {w : InfinitePlace F} (hw : w.IsReal) {m : GL (Fin 2) ℝ} {ε : ℝ}
    (hm : ∀ z : ℝ, m * unipotentGL2 z = unipotentGL2 (ε * z) * m) {g : AdelicGL2 (𝓞 F) F}
    (hg : AdelicLevel.glArch (𝓞 F) F g = 1) {y : ℝ} (hy : 0 < y) (x : ℝ) :
    archRealGLAt hw (m * splitTorusGL2 (Real.log y / 2)) * g * archFlowAt hw .E x
      = archRealGLAt hw (unipotentGL2 (ε * (y * x))) * (archRealGLAt hw (m * splitTorusGL2 (Real.log y / 2)) * g) := by
  have hexp : Real.exp (2 * (Real.log y / 2)) = y := by
    rw [show 2 * (Real.log y / 2) = Real.log y by ring, Real.exp_log hy]
  show archRealGLAt hw (m * splitTorusGL2 (Real.log y / 2)) * g * archRealGLAt hw (unipotentGL2 x) = _
  rw [mul_assoc, ← archRealGLAt_mul_comm_of_glArch_eq_one hw (unipotentGL2 x) hg, ← mul_assoc,
    ← map_mul (archRealGLAt hw) (m * splitTorusGL2 (Real.log y / 2)) (unipotentGL2 x), mul_assoc m,
    splitTorusGL2_mul_unipotentGL2, hexp, ← mul_assoc m, hm, mul_assoc,
    map_mul (archRealGLAt hw) (unipotentGL2 (ε * (y * x))) (m * splitTorusGL2 (Real.log y / 2)), mul_assoc]

end SheetFlows

section SheetValues

variable (F : Type) [Field F] [NumberField F]
variable {F}

private theorem archDerivAt_H_apply_sheetDatum {w : InfinitePlace F} (hw : w.IsReal) (W : AdelicGL2 (𝓞 F) F → ℂ)
    (m : GL (Fin 2) ℝ) {g : AdelicGL2 (𝓞 F) F} (hg : AdelicLevel.glArch (𝓞 F) F g = 1) {y : ℝ} (hy : 0 < y)
    (hdiff : DifferentiableAt ℝ (fun z : ℝ => W (archRealGLAt hw (m * splitTorusGL2 (Real.log z / 2)) * g)) y) :
    archDerivAt hw .H W (archRealGLAt hw (m * splitTorusGL2 (Real.log y / 2)) * g)
      = 2 * (y : ℂ) * deriv (fun z : ℝ => W (archRealGLAt hw (m * splitTorusGL2 (Real.log z / 2)) * g)) y := by
  show deriv (fun t : ℝ => W (archRealGLAt hw (m * splitTorusGL2 (Real.log y / 2)) * g * archFlowAt hw .H t)) 0 = _
  have hflow : (fun t : ℝ => W (archRealGLAt hw (m * splitTorusGL2 (Real.log y / 2)) * g * archFlowAt hw .H t))
      = fun t : ℝ => W (archRealGLAt hw (m * splitTorusGL2 (Real.log (y * Real.exp (2 * t)) / 2)) * g) := by
    funext t
    rw [sheetDatum_mul_archFlowAt_H hw m hg hy t]
  rw [hflow]
  have hc : HasDerivAt (fun t : ℝ => y * Real.exp (2 * t)) (y * (Real.exp (2 * 0) * (2 * 1))) 0 :=
    (((hasDerivAt_id' (0 : ℝ)).const_mul (2 : ℝ)).exp).const_mul y
  have hy0 : y * Real.exp (2 * 0) = y := by simp
  have hF₀ : HasDerivAt (fun z : ℝ => W (archRealGLAt hw (m * splitTorusGL2 (Real.log z / 2)) * g))
      (deriv (fun z : ℝ => W (archRealGLAt hw (m * splitTorusGL2 (Real.log z / 2)) * g)) y)
      (y * Real.exp (2 * 0)) := by
    rw [hy0]
    exact hdiff.hasDerivAt
  have h2 := hF₀.scomp (0 : ℝ) hc
  have h3 : deriv (fun t : ℝ => W (archRealGLAt hw (m * splitTorusGL2 (Real.log (y * Real.exp (2 * t)) / 2)) * g)) 0
      = (y * (Real.exp (2 * 0) * (2 * 1)))
        • deriv (fun z : ℝ => W (archRealGLAt hw (m * splitTorusGL2 (Real.log z / 2)) * g)) y :=
    h2.deriv
  rw [h3]
  simp only [mul_zero, Real.exp_zero, mul_one, one_mul, Complex.real_smul]
  push_cast
  ring

private theorem archDerivAt_E_apply_sheetDatum {w : InfinitePlace F} (hw : w.IsReal) (W : AdelicGL2 (𝓞 F) F → ℂ)
    (hWψ : ∀ (x : ℝ) (p : AdelicGL2 (𝓞 F) F),
      W (archRealGLAt hw (unipotentGL2 x) * p) = Complex.exp (2 * Real.pi * Complex.I * x) * W p)
    {m : GL (Fin 2) ℝ} {ε : ℝ} (hm : ∀ z : ℝ, m * unipotentGL2 z = unipotentGL2 (ε * z) * m) {g : AdelicGL2 (𝓞 F) F}
    (hg : AdelicLevel.glArch (𝓞 F) F g = 1) {y : ℝ} (hy : 0 < y) :
    archDerivAt hw .E W (archRealGLAt hw (m * splitTorusGL2 (Real.log y / 2)) * g)
      = 2 * (Real.pi : ℂ) * Complex.I * ((ε * y : ℝ) : ℂ)
          * W (archRealGLAt hw (m * splitTorusGL2 (Real.log y / 2)) * g) := by
  show deriv (fun x : ℝ => W (archRealGLAt hw (m * splitTorusGL2 (Real.log y / 2)) * g * archFlowAt hw .E x)) 0 = _
  have hflow : (fun x : ℝ => W (archRealGLAt hw (m * splitTorusGL2 (Real.log y / 2)) * g * archFlowAt hw .E x))
      = fun x : ℝ => Complex.exp (2 * Real.pi * Complex.I * ((ε * (y * x) : ℝ) : ℂ))
          * W (archRealGLAt hw (m * splitTorusGL2 (Real.log y / 2)) * g) := by
    funext x
    rw [sheetDatum_mul_archFlowAt_E hw hm hg hy x, hWψ]
  rw [hflow]
  have h1 : HasDerivAt (fun x : ℝ => Complex.exp (2 * Real.pi * Complex.I * ((ε * (y * x) : ℝ) : ℂ)))
      (Complex.exp (2 * Real.pi * Complex.I * ((ε * (y * 0) : ℝ) : ℂ))
        * (2 * Real.pi * Complex.I * ((ε * (y * 1) : ℝ) : ℂ))) 0 :=
    (((((hasDerivAt_id' (0 : ℝ)).const_mul y).const_mul ε).ofReal_comp).const_mul
      (2 * (Real.pi : ℂ) * Complex.I)).cexp
  rw [(h1.mul_const (W (archRealGLAt hw (m * splitTorusGL2 (Real.log y / 2)) * g))).deriv]
  simp

end SheetValues

section SheetAlgebra

private theorem two_mul_deriv_sub_eq_zero_of_J_sheet_lowering (DH DE DF Wh f' fy : ℂ) (y : ℝ) (k : ℤ)
    (hlow : DH - Complex.I * (DE + DF) = 0)
    (hE : DE = 2 * (Real.pi : ℂ) * Complex.I * ((-1 * y : ℝ) : ℂ) * Wh)
    (hwt : DE - DF = (k : ℂ) * Complex.I * Wh) (hH : DH = 2 * (y : ℂ) * f') (hWh : Wh = fy) :
    2 * (y : ℂ) * f' - (4 * (Real.pi : ℂ) * (y : ℂ) + (k : ℂ)) * fy = 0 := by
  rw [hWh] at hE hwt
  push_cast at hE
  have hDF : DF = DE - (k : ℂ) * Complex.I * fy := by linear_combination -hwt
  rw [hH, hDF, hE] at hlow
  linear_combination hlow - (4 * (Real.pi : ℂ) * (y : ℂ) + (k : ℂ)) * fy * Complex.I_mul_I

end SheetAlgebra

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

section NegativeSheetOfLoweredVectors

private theorem whittakerCoefficient_one_diagOne_archRealUnit_neg_eq_zero_of_lowering
    (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 ℚ) ℚ)) (hd : d₁ < d₂)
    (hcov : CoversModCentre ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂))
    (ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ) (hψ : IsGlobalAddChar ℚ ψ) {w : InfinitePlace ℚ} (hw : w.IsReal)
    (hψr : ∀ x : InfiniteAdeleRing ℚ, (∀ w' : InfinitePlace ℚ, w' ≠ w → x w' = 0) →
      ψ (⟨x, 0⟩ : AdeleRing (𝓞 ℚ) ℚ) = Complex.exp (2 * Real.pi * Complex.I * extensionEmbedding w (x w)))
    {ξ : (productionPinsOf ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂)
      (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ)).Z →* ℂˣ}
    {N : Ideal (𝓞 ℚ)} {S : Finset (HeightOneSpectrum (𝓞 ℚ))} {Φ : HeckeEigensystem ℚ ℂ} {φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ}
    (hiso : IsIsotypicCuspFormAt ℚ (productionPinsOf ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂)
      (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ)) ξ N S Φ φ)
    (hne : φ ≠ 0) (hconv : ∃ α : AdelicGL2 (𝓞 ℚ) ℚ → ℂ, IsFactorizableTestFn ℚ α ∧ rightConv ℚ φ α = φ)
    (hsm : IsArchSmoothAt hw φ) (ν : ℂ) (hΩ : archCasimirAt hw φ = (1 / 4 - ν ^ 2) • φ)
    {k : InfinitePlace ℚ → ℤ}
    (hwt : ∀ (w : InfinitePlace ℚ) (hw : w.IsReal), HasArchCharacterAt₀ ℚ w (archWeightCharAt hw (k w)) φ)
    {uc : ℂ} {ac : ℤ} (hcen : IsArchCompAt ℚ (ξ.comp Subgroup.topEquiv.symm.toMonoidHom) w uc ac)
    (W : AdelicGL2 (𝓞 ℚ) ℚ → ℂ)
    (hW : W = whittakerCoefficient ℚ
      (productionPinsOf ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂)
        (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ))
      ψ φ 1)
    (hlowW : ∀ p : AdelicGL2 (𝓞 ℚ) ℚ,
      archDerivAt hw .H W p - Complex.I * (archDerivAt hw .E W p + archDerivAt hw .Fm W p) = 0) :
    ∀ g : AdelicGL2 (𝓞 ℚ) ℚ, g ∈ finiteAdelicGL2Subgroup ℚ → ∀ (t : ℝ) (ht : t < 0),
      W (diagOne (archUnitHom w (archRealUnit hw t ht.ne)) * g) = 0 := by
  intro g hg t ht

  have hWsm : IsArchSmoothAt hw W := by
    rw [hW]
    exact (isArchSmoothAt_and_archCasimirAt_whittakerCoefficient_eq_smul
      (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂) (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ)
      (fun v => heckeGen (𝓞 ℚ) ℚ v) ψ hψ w hw φ hsm hconv _ hΩ 1).1
  have hWk : HasArchCharacterAt₀ ℚ w (archWeightCharAt hw (k w)) W := by
    rw [hW]
    exact hasArchCharacterAt₀_whittakerCoefficient_fn ℚ _ ψ φ 1 w _ (hwt w hw)
  have hWψ : ∀ (x : ℝ) (p : AdelicGL2 (𝓞 ℚ) ℚ),
      W (archRealGLAt hw (unipotentGL2 x) * p) = Complex.exp (2 * Real.pi * Complex.I * x) * W p := by
    intro x p
    rw [hW]
    exact apply_archRealGLAt_unipotentGL2_mul_of_forall_unipotentGL2_mul ℚ ψ hw hψr _
      (fun X g' => whittakerCoefficient_one_unipotentGL2_mul_of_isIsotypicCuspFormAt ℚ
        (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂) (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ)
        (fun v => heckeGen (𝓞 ℚ) ℚ v) ψ hψ hiso X g') x p

  obtain ⟨-, hfJ, -, -⟩ := whittaker_ode_splitTorus_whittakerCoefficient_one_of_isIsotypicCuspFormAt _ _ _ ψ hψ hw hψr
    hiso hconv hsm ν hΩ (k w) (hwt w hw) W hW g hg

  have hlowm : ∀ y : ℝ, 0 < y →
      2 * (y : ℂ) * deriv (fun z : ℝ => W (archRealGLAt hw (UpperHalfPlane.J * splitTorusGL2 (Real.log z / 2)) * g)) y
          - (4 * (Real.pi : ℂ) * (y : ℂ) + (k w : ℂ))
              * W (archRealGLAt hw (UpperHalfPlane.J * splitTorusGL2 (Real.log y / 2)) * g) = 0 := by
    intro y hy
    have hdiff : DifferentiableAt ℝ
        (fun z : ℝ => W (archRealGLAt hw (UpperHalfPlane.J * splitTorusGL2 (Real.log z / 2)) * g)) y :=
      hfJ.differentiableAt (Ioi_mem_nhds hy)
    exact two_mul_deriv_sub_eq_zero_of_J_sheet_lowering _ _ _ _ _ _ y (k w) (hlowW _)
      (archDerivAt_E_apply_sheetDatum hw W hWψ J_mul_unipotentGL2_eq hg hy)
      (archDerivAt_E_sub_Fm_apply_of_hasArchCharacterAt₀ hWsm (k w) hWk _)
      (archDerivAt_H_apply_sheetDatum hw W UpperHalfPlane.J hg hy hdiff) rfl

  have hgr := exists_forall_norm_J_splitTorus_le_mul_rpow c u d₁ d₂ T hd hcov ψ hψ hw hψr hiso hne hconv hsm ν hΩ hwt
    hcen W hW g hg

  have hFm : ∀ s : ℝ, 0 < s →
      (fun z : ℂ => if hz : z.re ≠ 0 then W (diagOne (archUnitHom w (archRealUnit hw z.re hz)) * g) else 0) (-(s : ℂ))
        = ((Real.sqrt s : ℝ) : ℂ) ^ uc
            * W (archRealGLAt hw (UpperHalfPlane.J * splitTorusGL2 (Real.log s / 2)) * g) := by
    intro s hs
    have hre : (-(s : ℂ)).re = -s := by rw [Complex.neg_re, Complex.ofReal_re]
    simp only [hre]
    rw [dif_pos (neg_ne_zero.mpr hs.ne'), hW,
      whittakerCoefficient_archRealGLAt_J_mul_splitTorusGL2_half_log_of_isArchCompAt ℚ _ _ _ _ ψ
        (isLsXiFunction_of_isIsotypicCuspFormAt hiso) hw hcen 1 s hs g,
      ← mul_assoc, mul_comm (((Real.sqrt s : ℝ) : ℂ) ^ uc), inv_sqrt_cpow_mul_sqrt_cpow uc hs, one_mul]
  have h4c := eq_zero_of_neg_of_lowering uc (k w)
    (fun z : ℂ => if hz : z.re ≠ 0 then W (diagOne (archUnitHom w (archRealUnit hw z.re hz)) * g) else 0)
    (fun z : ℝ => W (archRealGLAt hw (UpperHalfPlane.J * splitTorusGL2 (Real.log z / 2)) * g)) hFm hfJ hlowm hgr t ht
  simp only [Complex.ofReal_re] at h4c
  rwa [dif_pos ht.ne] at h4c

end NegativeSheetOfLoweredVectors

section ConclusionOfTheTheorem

private def FactorizationConclusion (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 ℚ) ℚ)) (Φ : HeckeEigensystem ℚ ℂ)
    (R : SmoothCuspRealizationAt ℚ
      (productionPinsOf ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂)
        (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v)
        (adelicBox ℚ))
      Φ.toRawCentral)
    (ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ) (S : Finset (HeightOneSpectrum (𝓞 ℚ)))
    (archR : ∀ w : InfinitePlace ℚ, w.IsReal → RealArchParam) : Prop :=
    ∃ C : FiniteAdeleRing (𝓞 ℚ) ℚ → AdelicGL2 (𝓞 ℚ) ℚ → ℂ,
    ∀ par : InfinitePlace ℚ → ZMod 2,
      ∃ (φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ) (Wr : InfinitePlace ℚ → ℂ → ℂ) (k : InfinitePlace ℚ → ℤ),
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
            (k w : ℂ) = signShift (a₁ + par w) + signShift (a₂ + par w)) ∧
        (∀ (w : InfinitePlace ℚ) (hw : w.IsReal) (u₀ : ℂ) (n : ℕ) (hn : 1 ≤ n),
          archR w hw = RealArchParam.discrete u₀ n hn → k w = (n : ℤ) + 1) ∧
        (∀ a : (AdeleRing (𝓞 ℚ) ℚ)ˣ, ∀ g : AdelicGL2 (𝓞 ℚ) ℚ, g ∈ finiteAdelicGL2Subgroup ℚ →
            whittakerCoefficient ℚ
                (productionPinsOf ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂)
                  (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ)
                  (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ))
                ψ φ 1 (diagOne a * g)
              = (∏ w : InfinitePlace ℚ, Wr w (extensionEmbedding w ((a : AdeleRing (𝓞 ℚ) ℚ).1 w)))
                  * C (a : AdeleRing (𝓞 ℚ) ℚ).2 g) ∧
        (∀ (w : InfinitePlace ℚ) (hw : w.IsReal) (u₁ u₂ : ℂ) (a₁ : ZMod 2),
          archR w hw = RealArchParam.principal u₁ a₁ u₂ a₁ → par w = a₁ →
            ∀ t : ℝ, Wr w (-t) = (-1 : ℂ) ^ a₁.val * Wr w t) ∧
        (∀ (w : InfinitePlace ℚ) (hw : w.IsReal) (u₀ : ℂ) (n : ℕ) (hn : 1 ≤ n),
          archR w hw = RealArchParam.discrete u₀ n hn → ∀ t : ℝ, t < 0 → Wr w t = 0) ∧
        (∀ (w : InfinitePlace ℚ) (hw : w.IsReal) (u₁ u₂ : ℂ) (a₁ : ZMod 2),
          archR w hw = RealArchParam.principal u₁ a₁ u₂ a₁ → par w = a₁ + 1 →
            ∃ s₀ : ℝ, ∀ s : ℂ, s₀ < s.re →
              MellinConvergent
                  (fun t : ℝ => (Wr w t + (-1 : ℂ) ^ a₁.val * Wr w (-t)) / (t : ℂ)) s ∧
                mellin (fun t : ℝ => (Wr w t + (-1 : ℂ) ^ a₁.val * Wr w (-t)) / (t : ℂ)) s
                  = (2 * s + u₁ + u₂ - 1) / (4 * (Real.pi : ℂ))
                      * ((archR w hw).twist 0 a₁).archFactor s) ∧
        (∀ (w : InfinitePlace ℚ) (hw : w.IsReal) (b : ZMod 2),
          (b = par w ∨ b = par w + (archR w hw).centralSign) →
            ∃ s₀ : ℝ, ∀ s : ℂ, s₀ < s.re →
              MellinConvergent
                  (fun t : ℝ => (Wr w t + (-1 : ℂ) ^ b.val * Wr w (-t)) / (t : ℂ)) s ∧
                mellin (fun t : ℝ => (Wr w t + (-1 : ℂ) ^ b.val * Wr w (-t)) / (t : ℂ)) s
                  = ((archR w hw).twist 0 b).archFactor s)

end ConclusionOfTheTheorem

section PositiveSheetAlgebra

private theorem two_mul_deriv_add_eq_zero_of_one_sheet_lowering (DH DE DF Wh f' fy : ℂ) (y : ℝ) (k : ℤ)
    (hlow : DH - Complex.I * (DE + DF) = 0)
    (hE : DE = 2 * (Real.pi : ℂ) * Complex.I * (y : ℂ) * Wh)
    (hwt : DE - DF = (k : ℂ) * Complex.I * Wh) (hH : DH = 2 * (y : ℂ) * f') (hWh : Wh = fy) :
    2 * (y : ℂ) * f' + (4 * (Real.pi : ℂ) * (y : ℂ) - (k : ℂ)) * fy = 0 := by
  rw [hWh] at hE hwt
  have hDF : DF = DE - (k : ℂ) * Complex.I * fy := by linear_combination -hwt
  rw [hH, hDF, hE] at hlow
  linear_combination hlow + (4 * (Real.pi : ℂ) * (y : ℂ) - (k : ℂ)) * fy * Complex.I_mul_I

end PositiveSheetAlgebra

section SheetRelations

private theorem sqrt_cpow_mul_inv_sqrt_cpow (u : ℂ) {y : ℝ} (hy : 0 < y) :
    ((Real.sqrt y : ℝ) : ℂ) ^ u * (((Real.sqrt y)⁻¹ : ℝ) : ℂ) ^ u = 1 := by
  rw [mul_comm]
  exact inv_sqrt_cpow_mul_sqrt_cpow u hy

variable (F : Type) [Field F] [NumberField F]
variable {F}

private theorem one_sheet_lowering_relation {w : InfinitePlace F} (hw : w.IsReal) {W : AdelicGL2 (𝓞 F) F → ℂ}
    (hWsm : IsArchSmoothAt hw W) {k : ℤ} (hWk : HasArchCharacterAt₀ F w (archWeightCharAt hw k) W)
    (hWψ : ∀ (x : ℝ) (p : AdelicGL2 (𝓞 F) F),
      W (archRealGLAt hw (unipotentGL2 x) * p) = Complex.exp (2 * Real.pi * Complex.I * x) * W p)
    (hlowW : ∀ p : AdelicGL2 (𝓞 F) F,
      archDerivAt hw .H W p - Complex.I * (archDerivAt hw .E W p + archDerivAt hw .Fm W p) = 0)
    {g : AdelicGL2 (𝓞 F) F} (hg : AdelicLevel.glArch (𝓞 F) F g = 1)
    (hf : DifferentiableOn ℝ (fun z : ℝ => W (archRealGLAt hw (splitTorusGL2 (Real.log z / 2)) * g)) (Set.Ioi 0))
    {y : ℝ} (hy : 0 < y) :
    2 * (y : ℂ) * deriv (fun z : ℝ => W (archRealGLAt hw (splitTorusGL2 (Real.log z / 2)) * g)) y
        + (4 * (Real.pi : ℂ) * (y : ℂ) - (k : ℂ)) * W (archRealGLAt hw (splitTorusGL2 (Real.log y / 2)) * g) = 0 := by
  have hdiff : DifferentiableAt ℝ
      (fun z : ℝ => W (archRealGLAt hw ((1 : GL (Fin 2) ℝ) * splitTorusGL2 (Real.log z / 2)) * g)) y := by
    simpa only [one_mul] using hf.differentiableAt (Ioi_mem_nhds hy)
  have hH := archDerivAt_H_apply_sheetDatum hw W 1 hg hy hdiff
  have hE := archDerivAt_E_apply_sheetDatum hw W hWψ one_mul_unipotentGL2_eq hg hy
  simp only [one_mul] at hH hE
  exact two_mul_deriv_add_eq_zero_of_one_sheet_lowering _ _ _ _ _ _ y k (hlowW _) hE
    (archDerivAt_E_sub_Fm_apply_of_hasArchCharacterAt₀ hWsm k hWk _) hH rfl

private theorem J_sheet_lowering_relation {w : InfinitePlace F} (hw : w.IsReal) {W : AdelicGL2 (𝓞 F) F → ℂ}
    (hWsm : IsArchSmoothAt hw W) {k : ℤ} (hWk : HasArchCharacterAt₀ F w (archWeightCharAt hw k) W)
    (hWψ : ∀ (x : ℝ) (p : AdelicGL2 (𝓞 F) F),
      W (archRealGLAt hw (unipotentGL2 x) * p) = Complex.exp (2 * Real.pi * Complex.I * x) * W p)
    (hlowW : ∀ p : AdelicGL2 (𝓞 F) F,
      archDerivAt hw .H W p - Complex.I * (archDerivAt hw .E W p + archDerivAt hw .Fm W p) = 0)
    {g : AdelicGL2 (𝓞 F) F} (hg : AdelicLevel.glArch (𝓞 F) F g = 1)
    (hfJ : DifferentiableOn ℝ
      (fun z : ℝ => W (archRealGLAt hw (UpperHalfPlane.J * splitTorusGL2 (Real.log z / 2)) * g)) (Set.Ioi 0))
    {y : ℝ} (hy : 0 < y) :
    2 * (y : ℂ) * deriv (fun z : ℝ => W (archRealGLAt hw (UpperHalfPlane.J * splitTorusGL2 (Real.log z / 2)) * g)) y
        - (4 * (Real.pi : ℂ) * (y : ℂ) + (k : ℂ))
            * W (archRealGLAt hw (UpperHalfPlane.J * splitTorusGL2 (Real.log y / 2)) * g) = 0 :=
  two_mul_deriv_sub_eq_zero_of_J_sheet_lowering _ _ _ _ _ _ y k (hlowW _)
    (archDerivAt_E_apply_sheetDatum hw W hWψ J_mul_unipotentGL2_eq hg hy)
    (archDerivAt_E_sub_Fm_apply_of_hasArchCharacterAt₀ hWsm k hWk _)
    (archDerivAt_H_apply_sheetDatum hw W UpperHalfPlane.J hg hy (hfJ.differentiableAt (Ioi_mem_nhds hy))) rfl

end SheetRelations

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

private theorem archDerivAt_H_whittakerCoefficient_one_sub_eq_zero_of_lowering (D : Set (AdelicGL2 (𝓞 ℚ) ℚ))
    (U : Ideal (𝓞 ℚ) → Subgroup (AdelicGL2 (𝓞 ℚ) ℚ)) (gen : HeightOneSpectrum (𝓞 ℚ) → AdelicGL2 (𝓞 ℚ) ℚ)
    (ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ) (hψ : IsGlobalAddChar ℚ ψ) {w : InfinitePlace ℚ} (hw : w.IsReal)
    {φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ} (hcont : Continuous φ)
    (hleft : ∀ (β : ℚ) (g : AdelicGL2 (𝓞 ℚ) ℚ), φ (unipotentGL2 (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) β) * g) = φ g)
    (hconv : ∃ α : AdelicGL2 (𝓞 ℚ) ℚ → ℂ, IsFactorizableTestFn ℚ α ∧ rightConv ℚ φ α = φ) (hsm : IsArchSmoothAt hw φ)
    (hlow : archDerivAt hw .H φ - Complex.I • (archDerivAt hw .E φ + archDerivAt hw .Fm φ) = 0)
    (p : AdelicGL2 (𝓞 ℚ) ℚ) :
    archDerivAt hw .H (whittakerCoefficient ℚ (productionPinsOf ℚ D U gen (adelicBox ℚ)) ψ φ 1) p
      - Complex.I * (archDerivAt hw .E (whittakerCoefficient ℚ (productionPinsOf ℚ D U gen (adelicBox ℚ)) ψ φ 1) p
          + archDerivAt hw .Fm (whittakerCoefficient ℚ (productionPinsOf ℚ D U gen (adelicBox ℚ)) ψ φ 1) p) = 0 := by
  obtain ⟨-, hint⟩ := whittakerCoefficientIntegrable_self_and_archDerivAt D U gen ψ hψ hw hcont hleft hconv hsm
  have hH : archDerivAt hw .H φ = Complex.I • (archDerivAt hw .E φ + archDerivAt hw .Fm φ) := sub_eq_zero.mp hlow
  rw [archDerivAt_whittakerCoefficient_one_eq D U gen ψ hψ hw hsm hconv .H,
    archDerivAt_whittakerCoefficient_one_eq D U gen ψ hψ hw hsm hconv .E,
    archDerivAt_whittakerCoefficient_one_eq D U gen ψ hψ hw hsm hconv .Fm, hH, whittakerCoefficient_smul_fn,
    Pi.smul_apply, smul_eq_mul, whittakerCoefficient_add _ ψ (hint .E 1 p) (hint .Fm 1 p), sub_self]

end LoweringTransfer

section ArchimedeanFactors

open LanglandsTunnell.RealArchParam in

private theorem archFactor_twist_zero_discrete (u₀ : ℂ) (n : ℕ) (hn : 1 ≤ n) (b : ZMod 2) (s : ℂ) :
    ((RealArchParam.discrete u₀ n hn).twist 0 b).archFactor s = Complex.Gammaℂ (s + (u₀ + (n : ℂ) / 2)) := by
  simp [twist, archFactor, gammaR, gammaC]

private theorem zmod_two_add_eq_one_of_ne {x y : ZMod 2} (hxy : x ≠ y) : x + y = 1 := by
  have key : ∀ x y : ZMod 2, x ≠ y → x + y = 1 := by decide
  exact key x y hxy

private theorem signShift_eq_of_ne {x y : ZMod 2} (hxy : x ≠ y) :
    signShift x = 0 ∧ signShift y = 1 ∨ signShift x = 1 ∧ signShift y = 0 := by
  have key : ∀ x y : ZMod 2, x ≠ y → x = 0 ∧ y = 1 ∨ x = 1 ∧ y = 0 := by decide
  rcases key x y hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact Or.inl ⟨signShift_zero, signShift_one⟩
  · exact Or.inr ⟨signShift_one, signShift_zero⟩

open LanglandsTunnell.RealArchParam Complex in

private theorem archFactor_twist_zero_principal_of_ne (u₀ : ℂ) {a₁ a₂ : ZMod 2} (h : a₁ ≠ a₂) (b : ZMod 2) (s : ℂ) :
    ((RealArchParam.principal u₀ a₁ u₀ a₂).twist 0 b).archFactor s = Gammaℂ (s + u₀) := by
  have hne : a₁ + b ≠ a₂ + b := fun e => h (add_right_cancel e)
  have e1 : ((RealArchParam.principal u₀ a₁ u₀ a₂).twist 0 b).archFactor s
      = Gammaℝ (s + (u₀ + signShift (a₁ + b))) * Gammaℝ (s + (u₀ + signShift (a₂ + b))) := by
    simp [twist, archFactor, gammaR, gammaC]
  rw [e1]
  rcases signShift_eq_of_ne hne with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [h1, h2, add_zero, ← add_assoc]
    exact Gammaℝ_mul_Gammaℝ_add_one (s + u₀)
  · rw [h1, h2, add_zero, ← add_assoc, mul_comm]
    exact Gammaℝ_mul_Gammaℝ_add_one (s + u₀)

private theorem signShift_add_signShift_eq_one_of_ne {a₁ a₂ : ZMod 2} (h : a₁ ≠ a₂) (p : ZMod 2) :
    signShift (a₁ + p) + signShift (a₂ + p) = 1 := by
  have hne : a₁ + p ≠ a₂ + p := fun e => h (add_right_cancel e)
  rcases signShift_eq_of_ne hne with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2] <;> ring

private theorem signShift_add_signShift_self (a : ZMod 2) : signShift (a + a) + signShift (a + a) = 0 := by
  have h : a + a = 0 := by
    revert a
    decide
  rw [h, signShift_zero, add_zero]

private theorem signShift_add_signShift_add_one (a : ZMod 2) :
    signShift (a + (a + 1)) + signShift (a + (a + 1)) = 2 := by
  have h : a + (a + 1) = 1 := by
    revert a
    decide
  rw [h, signShift_one]
  norm_num

private theorem centralSign_principal_same_parity (u₁ u₂ : ℂ) (a : ZMod 2) :
    (RealArchParam.principal u₁ a u₂ a).centralSign = 0 := by
  show a + a = 0
  revert a
  decide

private theorem signShift_re_nonneg (b : ZMod 2) : 0 ≤ (signShift b).re := by
  unfold signShift
  split_ifs <;> simp

private theorem archFactor_twist_zero_principal_same_parity (u₁ u₂ : ℂ) (a b : ZMod 2) (s : ℂ) :
    ((RealArchParam.principal u₁ a u₂ a).twist 0 b).archFactor s
      = Complex.Gammaℝ (s + (u₁ + signShift (a + b))) * Complex.Gammaℝ (s + (u₂ + signShift (a + b))) := by
  simp [RealArchParam.twist, RealArchParam.archFactor, RealArchParam.gammaR, RealArchParam.gammaC]

private theorem archFactor_twist_zero_principal_same_parity_ne_zero (u₁ u₂ : ℂ) (a b : ZMod 2) {s : ℂ}
    (hs : max (-u₁.re) (-u₂.re) < s.re) : ((RealArchParam.principal u₁ a u₂ a).twist 0 b).archFactor s ≠ 0 := by
  obtain ⟨h₁, h₂⟩ := max_lt_iff.mp hs
  have hb := signShift_re_nonneg (a + b)
  rw [archFactor_twist_zero_principal_same_parity]
  refine mul_ne_zero (Complex.Gammaℝ_ne_zero_of_re_pos ?_) (Complex.Gammaℝ_ne_zero_of_re_pos ?_)
  · rw [Complex.add_re, Complex.add_re]
    linarith
  · rw [Complex.add_re, Complex.add_re]
    linarith

private theorem two_mul_add_add_sub_one_div_ne_zero (u₁ u₂ : ℂ) :
    (2 * ((max (-u₁.re) (-u₂.re) + 1 : ℝ) : ℂ) + u₁ + u₂ - 1) / (4 * (Real.pi : ℂ)) ≠ 0 := by
  have hm₁ := le_max_left (-u₁.re) (-u₂.re)
  have hm₂ := le_max_right (-u₁.re) (-u₂.re)
  refine div_ne_zero ?_ (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_pos.ne'))
  intro h0
  have hre := congrArg Complex.re h0
  simp only [Complex.sub_re, Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.zero_re,
    Complex.one_re] at hre
  norm_num at hre
  linarith

private theorem zmod_two_ne_add_one (a : ZMod 2) : a ≠ a + 1 := by
  revert a
  decide

private theorem zmod_two_eq_or_eq_add_one (p a : ZMod 2) : p = a ∨ p = a + 1 := by
  revert p a
  decide

private theorem zmod_two_add_self (a : ZMod 2) : a + a = 0 := by
  revert a
  decide

end ArchimedeanFactors

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
    have h := ((((hasDerivAt_id' θ).ofReal_comp.mul_const Complex.I).const_mul k).neg.cexp).mul (hf' θ)
    convert h using 1 <;> first | (with_reducible_and_instances rfl) | rfl | (push_cast; ring)
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

section ReflectionOfTheProfile

variable (F : Type) [Field F] [NumberField F]
variable {F}

private theorem diagOne_archUnitHom_archRealUnit_neg_one {w : InfinitePlace F} (hw : w.IsReal) :
    diagOne (archUnitHom w (archRealUnit hw (-1) (neg_ne_zero.mpr one_ne_zero)))
      = archRealGLAt hw UpperHalfPlane.J := by
  rw [← archRealGLAt_diagOne F hw (-1) (neg_ne_zero.mpr one_ne_zero)]
  congr 1
  ext i j
  fin_cases i <;> fin_cases j <;> simp [diagOne_coe_apply]

private theorem archRealUnit_neg_eq_mul {w : InfinitePlace F} (hw : w.IsReal) (t : ℝ) (ht : t ≠ 0) (ht' : -t ≠ 0) :
    archRealUnit hw (-t) ht' = archRealUnit hw t ht * archRealUnit hw (-1) (neg_ne_zero.mpr one_ne_zero) := by
  apply Units.ext
  rw [Units.val_mul, archRealUnit_coe, archRealUnit_coe, archRealUnit_coe, ← map_mul]
  congr 1
  ring

private theorem diagOne_archUnitHom_archRealUnit_neg {w : InfinitePlace F} (hw : w.IsReal) (t : ℝ) (ht : t ≠ 0)
    (ht' : -t ≠ 0) :
    diagOne (archUnitHom w (archRealUnit hw (-t) ht'))
      = diagOne (archUnitHom w (archRealUnit hw t ht)) * archRealGLAt hw UpperHalfPlane.J := by
  rw [archRealUnit_neg_eq_mul hw t ht ht', map_mul, map_mul, diagOne_archUnitHom_archRealUnit_neg_one]

private theorem whittakerCoefficient_one_mul_eq_of_forall_apply_mul
    (pins : CarrierPins F) (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ)
    {φ : AdelicGL2 (𝓞 F) F → ℂ} {m : AdelicGL2 (𝓞 F) F} {cJ : ℂ} (hφ : ∀ g, φ (g * m) = cJ * φ g)
    (x : AdelicGL2 (𝓞 F) F) :
    whittakerCoefficient F pins ψ φ 1 (x * m) = cJ * whittakerCoefficient F pins ψ φ 1 x := by
  rw [← whittakerCoefficient_fun_mul F pins ψ φ m 1 x]
  have hfun : (fun h => φ (h * m)) = cJ • φ := funext fun h => (hφ h).trans rfl
  rw [hfun]
  exact congrFun (whittakerCoefficient_smul_fn F pins ψ cJ φ 1) x

private theorem apply_diagOne_archRealUnit_neg_mul_eq {w : InfinitePlace F} (hw : w.IsReal) {W : AdelicGL2 (𝓞 F) F → ℂ}
    {cJ : ℂ} (hWJ : ∀ x, W (x * archRealGLAt hw UpperHalfPlane.J) = cJ * W x) {h : AdelicGL2 (𝓞 F) F}
    (hh : AdelicLevel.glArch (𝓞 F) F h = 1) (t : ℝ) (ht : t ≠ 0) (ht' : -t ≠ 0) :
    W (diagOne (archUnitHom w (archRealUnit hw (-t) ht')) * h)
      = cJ * W (diagOne (archUnitHom w (archRealUnit hw t ht)) * h) := by
  rw [diagOne_archUnitHom_archRealUnit_neg hw t ht ht', mul_assoc,
    archRealGLAt_mul_comm_of_glArch_eq_one hw UpperHalfPlane.J hh, ← mul_assoc, hWJ]

omit [NumberField F] in
private theorem archRealUnit_congr
    {w : InfinitePlace F} (hw : w.IsReal) {r s : ℝ} (hrs : r = s) (hr : r ≠ 0) (hs : s ≠ 0) :
    archRealUnit hw r hr = archRealUnit hw s hs := by
  subst hrs
  rfl

private theorem apply_diagOne_archRealUnit_mul_eq_mul_apply_neg {w : InfinitePlace F} (hw : w.IsReal)
    {W : AdelicGL2 (𝓞 F) F → ℂ} {cJ : ℂ} (hWJ : ∀ x, W (x * archRealGLAt hw UpperHalfPlane.J) = cJ * W x)
    {h : AdelicGL2 (𝓞 F) F} (hh : AdelicLevel.glArch (𝓞 F) F h = 1) (r : ℝ) (hr : r ≠ 0) (hr' : -r ≠ 0) :
    W (diagOne (archUnitHom w (archRealUnit hw r hr)) * h)
      = cJ * W (diagOne (archUnitHom w (archRealUnit hw (-r) hr')) * h) := by
  rw [archRealUnit_congr hw (neg_neg r).symm hr (neg_ne_zero.mpr hr')]
  exact apply_diagOne_archRealUnit_neg_mul_eq hw hWJ hh (-r) hr' (neg_ne_zero.mpr hr')

end ReflectionOfTheProfile

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

private theorem whittakerCoefficient_zero_fn (pins : CarrierPins F) (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (α : F) :
    whittakerCoefficient F pins ψ (0 : AdelicGL2 (𝓞 F) F → ℂ) α = 0 := by
  have h := whittakerCoefficient_smul_fn F pins ψ 0 (0 : AdelicGL2 (𝓞 F) F → ℂ) α
  simp only [zero_smul] at h
  exact h

private theorem J_mul_splitTorusGL2
    (t : ℝ) : UpperHalfPlane.J * splitTorusGL2 t = splitTorusGL2 t * UpperHalfPlane.J := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [splitTorusGL2, Matrix.mul_apply, Fin.sum_univ_two]

private theorem apply_archRealGLAt_J_mul_splitTorusGL2_mul
    {w : InfinitePlace F} (hw : w.IsReal) {W : AdelicGL2 (𝓞 F) F → ℂ}
    {cJ : ℂ} (hWJ : ∀ x, W (x * archRealGLAt hw UpperHalfPlane.J) = cJ * W x) {h : AdelicGL2 (𝓞 F) F}
    (hh : AdelicLevel.glArch (𝓞 F) F h = 1) (t : ℝ) :
    W (archRealGLAt hw (UpperHalfPlane.J * splitTorusGL2 t) * h) = cJ * W (archRealGLAt hw (splitTorusGL2 t) * h) := by
  rw [J_mul_splitTorusGL2, map_mul, mul_assoc, archRealGLAt_mul_comm_of_glArch_eq_one hw UpperHalfPlane.J hh,
    ← mul_assoc, hWJ]

private theorem deriv_fun_const_mul (cs : ℂ) (f : ℝ → ℂ) (t : ℝ) : deriv (fun z => cs * f z) t = cs * deriv f t :=
  deriv_const_mul_field cs

private theorem deriv_eq_of_forall_pos_eq {f g : ℝ → ℂ} (hfg : ∀ z : ℝ, 0 < z → f z = g z) {t : ℝ} (ht : 0 < t) :
    deriv f t = deriv g t := by
  apply Filter.EventuallyEq.deriv_eq
  filter_upwards [Ioi_mem_nhds ht] with z hz using hfg z hz

private theorem sqrt_cpow_ne_zero (e : ℂ) {z : ℝ} (hz : 0 < z) : ((Real.sqrt z : ℝ) : ℂ) ^ e ≠ 0 := fun h0 =>
  (Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hz).ne') ((Complex.cpow_eq_zero_iff _ _).mp h0).1

private theorem eq_mul_of_sqrt_cpow_mul_eq (e : ℂ) {z : ℝ} (hz : 0 < z) {a b cs : ℂ}
    (h : ((Real.sqrt z : ℝ) : ℂ) ^ e * a = cs * (((Real.sqrt z : ℝ) : ℂ) ^ e * b)) : a = cs * b := by
  rw [mul_left_comm] at h
  exact mul_left_cancel₀ (sqrt_cpow_ne_zero e hz) h

end RaisedCoefficient

section RaisedSheetValues

variable (F : Type) [Field F] [NumberField F]
variable {F}

private theorem archRaise_expression_apply_sheetDatum {w : InfinitePlace F} (hw : w.IsReal) (W : AdelicGL2 (𝓞 F) F → ℂ)
    (hWψ : ∀ (x : ℝ) (p : AdelicGL2 (𝓞 F) F),
      W (archRealGLAt hw (unipotentGL2 x) * p) = Complex.exp (2 * Real.pi * Complex.I * x) * W p)
    (hDFm : ∀ p, archDerivAt hw .Fm W p = archDerivAt hw .E W p)
    {m : GL (Fin 2) ℝ} {ε : ℝ} (hm : ∀ z : ℝ, m * unipotentGL2 z = unipotentGL2 (ε * z) * m) {g : AdelicGL2 (𝓞 F) F}
    (hg : AdelicLevel.glArch (𝓞 F) F g = 1) {y : ℝ} (hy : 0 < y)
    (hdiff : DifferentiableAt ℝ (fun z : ℝ => W (archRealGLAt hw (m * splitTorusGL2 (Real.log z / 2)) * g)) y) :
    archDerivAt hw .H W (archRealGLAt hw (m * splitTorusGL2 (Real.log y / 2)) * g)
        + Complex.I * (archDerivAt hw .E W (archRealGLAt hw (m * splitTorusGL2 (Real.log y / 2)) * g)
          + archDerivAt hw .Fm W (archRealGLAt hw (m * splitTorusGL2 (Real.log y / 2)) * g))
      = 2 * (y : ℂ) * deriv (fun z : ℝ => W (archRealGLAt hw (m * splitTorusGL2 (Real.log z / 2)) * g)) y
          - 4 * (Real.pi : ℂ) * ((ε * y : ℝ) : ℂ)
              * W (archRealGLAt hw (m * splitTorusGL2 (Real.log y / 2)) * g) := by
  rw [hDFm, archDerivAt_H_apply_sheetDatum hw W m hg hy hdiff, archDerivAt_E_apply_sheetDatum hw W hWψ hm hg hy]
  linear_combination (4 * (Real.pi : ℂ) * ((ε * y : ℝ) : ℂ)
    * W (archRealGLAt hw (m * splitTorusGL2 (Real.log y / 2)) * g)) * Complex.I_sq

end RaisedSheetValues

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

section DiscreteParameter

private theorem factorizationConclusion_of_discrete
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
    (ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ) (_hψ : IsGlobalAddChar ℚ ψ)
    (_hψr : ∀ (w : InfinitePlace ℚ), w.IsReal → ∀ x : InfiniteAdeleRing ℚ,
      (∀ w' : InfinitePlace ℚ, w' ≠ w → x w' = 0) →
        ψ (⟨x, 0⟩ : AdeleRing (𝓞 ℚ) ℚ)
          = Complex.exp (2 * Real.pi * Complex.I * extensionEmbedding w (x w)))
    (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (archR : ∀ w : InfinitePlace ℚ, w.IsReal → RealArchParam)
    (_hS : R.exceptionalSet ⊆ S)
    (_htype : ∀ (w : InfinitePlace ℚ) (hw : w.IsReal) (u₁ u₂ : ℂ) (a₁ a₂ : ZMod 2),
      archR w hw = RealArchParam.principal u₁ a₁ u₂ a₂ → |(u₁ - u₂).re| < 1)
    (_hcen : ∀ (w : InfinitePlace ℚ) (hw : w.IsReal),
      IsArchCompAt ℚ (R.centralChar.comp Subgroup.topEquiv.symm.toMonoidHom) w
        ((archR w hw).centralExponent + 1) ((archR w hw).centralSign.val : ℤ))
    (φ₁ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ) (k₁ : InfinitePlace ℚ → ℤ)
    (_hiso : IsIsotypicCuspFormAt ℚ
        (productionPinsOf ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂)
          (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ)
          (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ))
        R.centralChar Φ.level S Φ φ₁)
    (_hne : φ₁ ≠ 0)
    (_hconv : ∃ α : AdelicGL2 (𝓞 ℚ) ℚ → ℂ, IsFactorizableTestFn ℚ α ∧ rightConv ℚ φ₁ α = φ₁)
    (_hwt : ∀ (w : InfinitePlace ℚ) (hw : w.IsReal),
      HasArchCharacterAt₀ ℚ w (archWeightCharAt hw (k₁ w)) φ₁)
    (_hminp : ∀ (w : InfinitePlace ℚ) (hw : w.IsReal) (u₁ u₂ : ℂ) (a₁ a₂ : ZMod 2),
      archR w hw = RealArchParam.principal u₁ a₁ u₂ a₂ →
        (k₁ w = 0 ∨ k₁ w = 1) ∧ ((k₁ w : ZMod 2) = a₁ + a₂))
    (_hmind : ∀ (w : InfinitePlace ℚ) (hw : w.IsReal) (u₀ : ℂ) (n : ℕ) (hn : 1 ≤ n),
      archR w hw = RealArchParam.discrete u₀ n hn → k₁ w = (n : ℤ) + 1)
    (_hpair : ∀ (w : InfinitePlace ℚ) (hw : w.IsReal),
      IsArchSmoothAt hw φ₁ ∧ archCasimirAt hw φ₁ = (archR w hw).laplaceEigenvalue • φ₁)
    (_hJ : ∀ (w : InfinitePlace ℚ) (hw : w.IsReal) (u₁ u₂ : ℂ) (a₁ : ZMod 2),
      archR w hw = RealArchParam.principal u₁ a₁ u₂ a₁ →
        ∀ g : AdelicGL2 (𝓞 ℚ) ℚ, φ₁ (g * archRealGLAt hw UpperHalfPlane.J) = (-1 : ℂ) ^ a₁.val * φ₁ g)
    (_hlow : ∀ (w : InfinitePlace ℚ) (hw : w.IsReal) (u₀ : ℂ) (n : ℕ) (hn : 1 ≤ n),
      archR w hw = RealArchParam.discrete u₀ n hn →
        archDerivAt hw ArchDir.H φ₁
            - Complex.I • (archDerivAt hw ArchDir.E φ₁ + archDerivAt hw ArchDir.Fm φ₁) = 0)
    (_hlow1 : ∀ (w : InfinitePlace ℚ) (hw : w.IsReal) (u₀ : ℂ) (a₁ a₂ : ZMod 2),
      archR w hw = RealArchParam.principal u₀ a₁ u₀ a₂ → a₁ ≠ a₂ →
        archDerivAt hw ArchDir.H φ₁
            - Complex.I • (archDerivAt hw ArchDir.E φ₁ + archDerivAt hw ArchDir.Fm φ₁) = 0)
    (_heq : ∀ (w : InfinitePlace ℚ) (hw : w.IsReal) (u₁ u₂ : ℂ) (a₁ a₂ : ZMod 2),
      archR w hw = RealArchParam.principal u₁ a₁ u₂ a₂ → a₁ = a₂ ∨ u₁ = u₂)
    (w₀ : InfinitePlace ℚ) (hw₀ : w₀.IsReal) (u₀ : ℂ) (n : ℕ) (hn : 1 ≤ n)
    (hR : ∀ (w : InfinitePlace ℚ) (hw : w.IsReal), archR w hw = RealArchParam.discrete u₀ n hn) :
    FactorizationConclusion c u d₁ d₂ T Φ R ψ S archR := by

  obtain ⟨W, hW⟩ : ∃ W : AdelicGL2 (𝓞 ℚ) ℚ → ℂ, W = whittakerCoefficient ℚ
      (productionPinsOf ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂)
        (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ))
      ψ φ₁ 1 := ⟨_, rfl⟩

  have hsm : IsArchSmoothAt hw₀ φ₁ := (_hpair w₀ hw₀).1
  have hΩ : archCasimirAt hw₀ φ₁ = (1 / 4 - ((n : ℂ) / 2) ^ 2) • φ₁ := by
    have h := (_hpair w₀ hw₀).2
    rw [hR w₀ hw₀] at h
    exact archCasimirAt_eq_of_laplaceEigenvalue_discrete hw₀ u₀ n hn h
  have hcen₀ := _hcen w₀ hw₀
  rw [hR w₀ hw₀] at hcen₀
  simp only [RealArchParam.centralExponent] at hcen₀
  have hk : k₁ w₀ = (n : ℤ) + 1 := _hmind w₀ hw₀ u₀ n hn (hR w₀ hw₀)
  have hψr₀ := _hψr w₀ hw₀

  have hlowW : ∀ p : AdelicGL2 (𝓞 ℚ) ℚ,
      archDerivAt hw₀ .H W p - Complex.I * (archDerivAt hw₀ .E W p + archDerivAt hw₀ .Fm W p) = 0 := by
    intro p
    rw [hW]
    exact archDerivAt_H_whittakerCoefficient_one_sub_eq_zero_of_lowering _ _ _ ψ _hψ hw₀ _hiso.continuous
      (fun β g => apply_unipotentGL2_algebraMap_mul_of_isIsotypicCuspFormAt _hiso β g) _hconv hsm
      (_hlow w₀ hw₀ u₀ n hn (hR w₀ hw₀)) p

  have hWsm : IsArchSmoothAt hw₀ W := by
    rw [hW]
    exact (isArchSmoothAt_and_archCasimirAt_whittakerCoefficient_eq_smul
      (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂) (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ)
      (fun v => heckeGen (𝓞 ℚ) ℚ v) ψ _hψ w₀ hw₀ φ₁ hsm _hconv _ hΩ 1).1
  have hWk : HasArchCharacterAt₀ ℚ w₀ (archWeightCharAt hw₀ (k₁ w₀)) W := by
    rw [hW]
    exact hasArchCharacterAt₀_whittakerCoefficient_fn ℚ _ ψ φ₁ 1 w₀ _ (_hwt w₀ hw₀)
  have hWψ : ∀ (x : ℝ) (p : AdelicGL2 (𝓞 ℚ) ℚ),
      W (archRealGLAt hw₀ (unipotentGL2 x) * p) = Complex.exp (2 * Real.pi * Complex.I * x) * W p := by
    intro x p
    rw [hW]
    exact apply_archRealGLAt_unipotentGL2_mul_of_forall_unipotentGL2_mul ℚ ψ hw₀ hψr₀ _
      (fun X g' => whittakerCoefficient_one_unipotentGL2_mul_of_isIsotypicCuspFormAt ℚ
        (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂) (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ)
        (fun v => heckeGen (𝓞 ℚ) ℚ v) ψ _hψ _hiso X g') x p

  have hneg := whittakerCoefficient_one_diagOne_archRealUnit_neg_eq_zero_of_lowering c u d₁ d₂ T _hd _hcov ψ _hψ hw₀
    hψr₀ _hiso _hne _hconv hsm _ hΩ _hwt hcen₀ W hW hlowW

  obtain ⟨g₀, hg₀⟩ := exists_whittakerCoefficient_one_ne_zero_of_isIsotypicCuspFormAt _ _ _ ψ _hψ hw₀ _hiso hsm _hne
  obtain ⟨r₀, hr₀, t₀, ht₀, href⟩ :=
    exists_whittakerCoefficient_one_diagOne_archRealUnit_mul_ne_zero _ _ _ ψ _hψ hw₀ _hiso (_hwt w₀ hw₀) hg₀
  rw [← hW] at href
  have hr₀pos : 0 < r₀ := by
    rcases lt_or_gt_of_ne hr₀ with h | h
    · exact absurd (hneg t₀ ht₀ r₀ h) href
    · exact h

  have hsep := whittakerCoefficient_one_diagOne_archRealUnit_mul_eq_div_mul_pos c u d₁ d₂ T _hd _hcov ψ _hψ hw₀ hψr₀
    _hiso _hne _hconv hsm _ hΩ _hwt hcen₀ W hW ht₀ hr₀pos href

  have hpeel : ∀ (h : AdelicGL2 (𝓞 ℚ) ℚ) (t : ℝ) (ht : 0 < t),
      W (diagOne (archUnitHom w₀ (archRealUnit hw₀ t ht.ne')) * h)
        = ((Real.sqrt t : ℝ) : ℂ) ^ (2 * u₀ + 1) * W (archRealGLAt hw₀ (splitTorusGL2 (Real.log t / 2)) * h) := by
    intro h t ht
    rw [hW, whittakerCoefficient_archRealGLAt_splitTorusGL2_half_log_of_isArchCompAt ℚ _ _ _ _ ψ
      (isLsXiFunction_of_isIsotypicCuspFormAt _hiso) hw₀ hcen₀ 1 t ht h, ← mul_assoc, sqrt_cpow_mul_inv_sqrt_cpow _ ht,
      one_mul]
  have hpeelJ : ∀ (h : AdelicGL2 (𝓞 ℚ) ℚ) (t : ℝ) (ht : 0 < t),
      W (diagOne (archUnitHom w₀ (archRealUnit hw₀ (-t) (neg_ne_zero.mpr ht.ne'))) * h)
        = ((Real.sqrt t : ℝ) : ℂ) ^ (2 * u₀ + 1)
            * W (archRealGLAt hw₀ (UpperHalfPlane.J * splitTorusGL2 (Real.log t / 2)) * h) := by
    intro h t ht
    rw [hW, whittakerCoefficient_archRealGLAt_J_mul_splitTorusGL2_half_log_of_isArchCompAt ℚ _ _ _ _ ψ
      (isLsXiFunction_of_isIsotypicCuspFormAt _hiso) hw₀ hcen₀ 1 t ht h, ← mul_assoc, sqrt_cpow_mul_inv_sqrt_cpow _ ht,
      one_mul]

  obtain ⟨Fref, hFref⟩ : ∃ Fref : ℂ → ℂ, ∀ z : ℂ,
      Fref z = if hz : z.re ≠ 0 then W (diagOne (archUnitHom w₀ (archRealUnit hw₀ z.re hz)) * t₀) else 0 :=
    ⟨_, fun _ => rfl⟩
  have hFpos : ∀ t : ℝ, 0 < t → Fref t
      = ((Real.sqrt t : ℝ) : ℂ) ^ (2 * u₀ + 1 - 1 + 1)
          * W (archRealGLAt hw₀ (splitTorusGL2 (Real.log t / 2)) * t₀) := by
    intro t ht
    rw [hFref, sub_add_cancel]
    simp only [Complex.ofReal_re]
    rw [dif_pos ht.ne']
    exact hpeel t₀ t ht
  have hFneg : ∀ t : ℝ, 0 < t → Fref (-t)
      = ((Real.sqrt t : ℝ) : ℂ) ^ (2 * u₀ + 1 - 1 + 1)
          * W (archRealGLAt hw₀ (UpperHalfPlane.J * splitTorusGL2 (Real.log t / 2)) * t₀) := by
    intro t ht
    rw [hFref, sub_add_cancel]
    simp only [Complex.neg_re, Complex.ofReal_re]
    rw [dif_pos (neg_ne_zero.mpr ht.ne')]
    exact hpeelJ t₀ t ht

  obtain ⟨hfp, -, -⟩ := (whittaker_ode_splitTorus_whittakerCoefficient_one_of_isIsotypicCuspFormAt _ _ _ ψ _hψ hw₀
    hψr₀ _hiso _hconv hsm _ hΩ (k₁ w₀) (_hwt w₀ hw₀) W hW t₀ ht₀).1
  obtain ⟨hfm, -, -⟩ := (whittaker_ode_splitTorus_whittakerCoefficient_one_of_isIsotypicCuspFormAt _ _ _ ψ _hψ hw₀
    hψr₀ _hiso _hconv hsm _ hΩ (k₁ w₀) (_hwt w₀ hw₀) W hW t₀ ht₀).2
  have hgr := exists_forall_norm_J_splitTorus_le_mul_rpow c u d₁ d₂ T _hd _hcov ψ _hψ hw₀ hψr₀ _hiso _hne _hconv hsm _
    hΩ _hwt hcen₀ W hW t₀ ht₀
  have hfp_ne : ∃ y : ℝ, 0 < y ∧ W (archRealGLAt hw₀ (splitTorusGL2 (Real.log y / 2)) * t₀) ≠ 0 := by
    refine ⟨r₀, hr₀pos, fun h0 => href ?_⟩
    rw [hpeel t₀ r₀ hr₀pos, h0, mul_zero]

  obtain ⟨hvan, ρ, hρ, hmel⟩ := mellin_whittakerProfile_eq_GammaC_of_lowering_eq_zero (2 * u₀ + 1 - 1) (k₁ w₀) Fref
    (fun y : ℝ => W (archRealGLAt hw₀ (splitTorusGL2 (Real.log y / 2)) * t₀))
    (fun y : ℝ => W (archRealGLAt hw₀ (UpperHalfPlane.J * splitTorusGL2 (Real.log y / 2)) * t₀)) hFpos hFneg hfp hfm
    (fun _ hy => one_sheet_lowering_relation hw₀ hWsm hWk hWψ hlowW ht₀ hfp hy)
    (fun _ hy => J_sheet_lowering_relation hw₀ hWsm hWk hWψ hlowW ht₀ hfm hy) hgr hfp_ne

  obtain ⟨cst, hcst⟩ : ∃ cst : AdelicGL2 (𝓞 ℚ) ℚ → ℂ, ∀ h : AdelicGL2 (𝓞 ℚ) ℚ, cst h
      = W (diagOne (archUnitHom w₀ (archRealUnit hw₀ r₀ hr₀pos.ne')) * h)
          / W (diagOne (archUnitHom w₀ (archRealUnit hw₀ r₀ hr₀pos.ne')) * t₀) := ⟨_, fun _ => rfl⟩
  have hprop : ∀ h : AdelicGL2 (𝓞 ℚ) ℚ, h ∈ finiteAdelicGL2Subgroup ℚ → ∀ (r : ℝ) (hr : r ≠ 0),
      W (diagOne (archUnitHom w₀ (archRealUnit hw₀ r hr)) * h) = cst h * Fref (r : ℂ) := by
    intro h hh r hr
    have hFr : Fref (r : ℂ) = W (diagOne (archUnitHom w₀ (archRealUnit hw₀ r hr)) * t₀) := by
      rw [hFref]
      simp only [Complex.ofReal_re]
      rw [dif_pos hr]
    rw [hFr, hcst]
    rcases lt_or_gt_of_ne hr with hneg_r | hpos_r
    · rw [hneg h hh r hneg_r, hneg t₀ ht₀ r hneg_r, mul_zero]
    · exact hsep h hh r hpos_r
  rw [hW] at hprop
  obtain ⟨C, hC⟩ :=
    exists_forall_whittakerCoefficient_one_diagOne_mul_eq_prod_mul c u d₁ d₂ T ψ φ₁ hw₀ Fref cst hprop ρ hρ

  refine ⟨C, fun _ => ⟨φ₁, fun _ z => ρ * Fref z, k₁, _hiso, _hne, _hconv, _hwt, ?_, ?_, hC, ?_, ?_, ?_, ?_⟩⟩
  · intro w hw u₁ u₂ a₁ a₂ h
    rw [hR] at h
    cases h
  · intro w hw u₀' n' hn' h
    rw [hR] at h
    cases h
    exact _hmind w hw _ _ _ (hR w hw)
  · intro w hw u₁ u₂ a₁ h
    rw [hR] at h
    cases h
  · intro w hw u₀' n' hn' h t ht
    exact mul_eq_zero_of_right ρ (hvan t ht)
  · intro w hw u₁ u₂ a₁ h
    rw [hR] at h
    cases h
  · intro w hw b _
    refine ⟨_, fun s hs => ⟨(hmel b s hs).1, ?_⟩⟩
    refine (hmel b s hs).2.trans ?_
    rw [hR w hw, archFactor_twist_zero_discrete, hk]
    congr 1
    push_cast
    ring

end DiscreteParameter

section OddPrincipalParameter

private theorem factorizationConclusion_of_oddPrincipal
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
    (ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ) (_hψ : IsGlobalAddChar ℚ ψ)
    (_hψr : ∀ (w : InfinitePlace ℚ), w.IsReal → ∀ x : InfiniteAdeleRing ℚ,
      (∀ w' : InfinitePlace ℚ, w' ≠ w → x w' = 0) →
        ψ (⟨x, 0⟩ : AdeleRing (𝓞 ℚ) ℚ)
          = Complex.exp (2 * Real.pi * Complex.I * extensionEmbedding w (x w)))
    (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (archR : ∀ w : InfinitePlace ℚ, w.IsReal → RealArchParam)
    (_hS : R.exceptionalSet ⊆ S)
    (_htype : ∀ (w : InfinitePlace ℚ) (hw : w.IsReal) (u₁ u₂ : ℂ) (a₁ a₂ : ZMod 2),
      archR w hw = RealArchParam.principal u₁ a₁ u₂ a₂ → |(u₁ - u₂).re| < 1)
    (_hcen : ∀ (w : InfinitePlace ℚ) (hw : w.IsReal),
      IsArchCompAt ℚ (R.centralChar.comp Subgroup.topEquiv.symm.toMonoidHom) w
        ((archR w hw).centralExponent + 1) ((archR w hw).centralSign.val : ℤ))
    (φ₁ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ) (k₁ : InfinitePlace ℚ → ℤ)
    (_hiso : IsIsotypicCuspFormAt ℚ
        (productionPinsOf ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂)
          (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ)
          (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ))
        R.centralChar Φ.level S Φ φ₁)
    (_hne : φ₁ ≠ 0)
    (_hconv : ∃ α : AdelicGL2 (𝓞 ℚ) ℚ → ℂ, IsFactorizableTestFn ℚ α ∧ rightConv ℚ φ₁ α = φ₁)
    (_hwt : ∀ (w : InfinitePlace ℚ) (hw : w.IsReal),
      HasArchCharacterAt₀ ℚ w (archWeightCharAt hw (k₁ w)) φ₁)
    (_hminp : ∀ (w : InfinitePlace ℚ) (hw : w.IsReal) (u₁ u₂ : ℂ) (a₁ a₂ : ZMod 2),
      archR w hw = RealArchParam.principal u₁ a₁ u₂ a₂ →
        (k₁ w = 0 ∨ k₁ w = 1) ∧ ((k₁ w : ZMod 2) = a₁ + a₂))
    (_hmind : ∀ (w : InfinitePlace ℚ) (hw : w.IsReal) (u₀ : ℂ) (n : ℕ) (hn : 1 ≤ n),
      archR w hw = RealArchParam.discrete u₀ n hn → k₁ w = (n : ℤ) + 1)
    (_hpair : ∀ (w : InfinitePlace ℚ) (hw : w.IsReal),
      IsArchSmoothAt hw φ₁ ∧ archCasimirAt hw φ₁ = (archR w hw).laplaceEigenvalue • φ₁)
    (_hJ : ∀ (w : InfinitePlace ℚ) (hw : w.IsReal) (u₁ u₂ : ℂ) (a₁ : ZMod 2),
      archR w hw = RealArchParam.principal u₁ a₁ u₂ a₁ →
        ∀ g : AdelicGL2 (𝓞 ℚ) ℚ, φ₁ (g * archRealGLAt hw UpperHalfPlane.J) = (-1 : ℂ) ^ a₁.val * φ₁ g)
    (_hlow : ∀ (w : InfinitePlace ℚ) (hw : w.IsReal) (u₀ : ℂ) (n : ℕ) (hn : 1 ≤ n),
      archR w hw = RealArchParam.discrete u₀ n hn →
        archDerivAt hw ArchDir.H φ₁
            - Complex.I • (archDerivAt hw ArchDir.E φ₁ + archDerivAt hw ArchDir.Fm φ₁) = 0)
    (_hlow1 : ∀ (w : InfinitePlace ℚ) (hw : w.IsReal) (u₀ : ℂ) (a₁ a₂ : ZMod 2),
      archR w hw = RealArchParam.principal u₀ a₁ u₀ a₂ → a₁ ≠ a₂ →
        archDerivAt hw ArchDir.H φ₁
            - Complex.I • (archDerivAt hw ArchDir.E φ₁ + archDerivAt hw ArchDir.Fm φ₁) = 0)
    (_heq : ∀ (w : InfinitePlace ℚ) (hw : w.IsReal) (u₁ u₂ : ℂ) (a₁ a₂ : ZMod 2),
      archR w hw = RealArchParam.principal u₁ a₁ u₂ a₂ → a₁ = a₂ ∨ u₁ = u₂)
    (w₀ : InfinitePlace ℚ) (hw₀ : w₀.IsReal) (u₀ : ℂ) {a₁ a₂ : ZMod 2} (hne : a₁ ≠ a₂)
    (hR : ∀ (w : InfinitePlace ℚ) (hw : w.IsReal), archR w hw = RealArchParam.principal u₀ a₁ u₀ a₂) :
    FactorizationConclusion c u d₁ d₂ T Φ R ψ S archR := by

  obtain ⟨W, hW⟩ : ∃ W : AdelicGL2 (𝓞 ℚ) ℚ → ℂ, W = whittakerCoefficient ℚ
      (productionPinsOf ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂)
        (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ))
      ψ φ₁ 1 := ⟨_, rfl⟩

  have hsm : IsArchSmoothAt hw₀ φ₁ := (_hpair w₀ hw₀).1
  have hΩ : archCasimirAt hw₀ φ₁ = (1 / 4 - ((u₀ - u₀) / 2) ^ 2) • φ₁ := by
    have h := (_hpair w₀ hw₀).2
    rw [hR w₀ hw₀] at h
    exact archCasimirAt_eq_of_laplaceEigenvalue_principal hw₀ u₀ a₁ u₀ a₂ h
  have hcen₀ := _hcen w₀ hw₀
  rw [hR w₀ hw₀] at hcen₀
  simp only [RealArchParam.centralExponent] at hcen₀

  have hk₁ : ∀ (w : InfinitePlace ℚ) (hw : w.IsReal), k₁ w = 1 := by
    intro w hw
    obtain ⟨h01, hpar⟩ := _hminp w hw u₀ u₀ a₁ a₂ (hR w hw)
    rcases h01 with h0 | h1
    · rw [h0, zmod_two_add_eq_one_of_ne hne] at hpar
      exact absurd hpar (by decide)
    · exact h1
  have hψr₀ := _hψr w₀ hw₀

  have hlowW : ∀ p : AdelicGL2 (𝓞 ℚ) ℚ,
      archDerivAt hw₀ .H W p - Complex.I * (archDerivAt hw₀ .E W p + archDerivAt hw₀ .Fm W p) = 0 := by
    intro p
    rw [hW]
    exact archDerivAt_H_whittakerCoefficient_one_sub_eq_zero_of_lowering _ _ _ ψ _hψ hw₀ _hiso.continuous
      (fun β g => apply_unipotentGL2_algebraMap_mul_of_isIsotypicCuspFormAt _hiso β g) _hconv hsm
      (_hlow1 w₀ hw₀ u₀ a₁ a₂ (hR w₀ hw₀) hne) p

  have hWsm : IsArchSmoothAt hw₀ W := by
    rw [hW]
    exact (isArchSmoothAt_and_archCasimirAt_whittakerCoefficient_eq_smul
      (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂) (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ)
      (fun v => heckeGen (𝓞 ℚ) ℚ v) ψ _hψ w₀ hw₀ φ₁ hsm _hconv _ hΩ 1).1
  have hWk : HasArchCharacterAt₀ ℚ w₀ (archWeightCharAt hw₀ (k₁ w₀)) W := by
    rw [hW]
    exact hasArchCharacterAt₀_whittakerCoefficient_fn ℚ _ ψ φ₁ 1 w₀ _ (_hwt w₀ hw₀)
  have hWψ : ∀ (x : ℝ) (p : AdelicGL2 (𝓞 ℚ) ℚ),
      W (archRealGLAt hw₀ (unipotentGL2 x) * p) = Complex.exp (2 * Real.pi * Complex.I * x) * W p := by
    intro x p
    rw [hW]
    exact apply_archRealGLAt_unipotentGL2_mul_of_forall_unipotentGL2_mul ℚ ψ hw₀ hψr₀ _
      (fun X g' => whittakerCoefficient_one_unipotentGL2_mul_of_isIsotypicCuspFormAt ℚ
        (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂) (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ)
        (fun v => heckeGen (𝓞 ℚ) ℚ v) ψ _hψ _hiso X g') x p

  have hneg := whittakerCoefficient_one_diagOne_archRealUnit_neg_eq_zero_of_lowering c u d₁ d₂ T _hd _hcov ψ _hψ hw₀
    hψr₀ _hiso _hne _hconv hsm _ hΩ _hwt hcen₀ W hW hlowW

  obtain ⟨g₀, hg₀⟩ := exists_whittakerCoefficient_one_ne_zero_of_isIsotypicCuspFormAt _ _ _ ψ _hψ hw₀ _hiso hsm _hne
  obtain ⟨r₀, hr₀, t₀, ht₀, href⟩ :=
    exists_whittakerCoefficient_one_diagOne_archRealUnit_mul_ne_zero _ _ _ ψ _hψ hw₀ _hiso (_hwt w₀ hw₀) hg₀
  rw [← hW] at href
  have hr₀pos : 0 < r₀ := by
    rcases lt_or_gt_of_ne hr₀ with h | h
    · exact absurd (hneg t₀ ht₀ r₀ h) href
    · exact h

  have hsep := whittakerCoefficient_one_diagOne_archRealUnit_mul_eq_div_mul_pos c u d₁ d₂ T _hd _hcov ψ _hψ hw₀ hψr₀
    _hiso _hne _hconv hsm _ hΩ _hwt hcen₀ W hW ht₀ hr₀pos href

  have hpeel : ∀ (h : AdelicGL2 (𝓞 ℚ) ℚ) (t : ℝ) (ht : 0 < t),
      W (diagOne (archUnitHom w₀ (archRealUnit hw₀ t ht.ne')) * h)
        = ((Real.sqrt t : ℝ) : ℂ) ^ (u₀ + u₀ + 1) * W (archRealGLAt hw₀ (splitTorusGL2 (Real.log t / 2)) * h) := by
    intro h t ht
    rw [hW, whittakerCoefficient_archRealGLAt_splitTorusGL2_half_log_of_isArchCompAt ℚ _ _ _ _ ψ
      (isLsXiFunction_of_isIsotypicCuspFormAt _hiso) hw₀ hcen₀ 1 t ht h, ← mul_assoc, sqrt_cpow_mul_inv_sqrt_cpow _ ht,
      one_mul]
  have hpeelJ : ∀ (h : AdelicGL2 (𝓞 ℚ) ℚ) (t : ℝ) (ht : 0 < t),
      W (diagOne (archUnitHom w₀ (archRealUnit hw₀ (-t) (neg_ne_zero.mpr ht.ne'))) * h)
        = ((Real.sqrt t : ℝ) : ℂ) ^ (u₀ + u₀ + 1)
            * W (archRealGLAt hw₀ (UpperHalfPlane.J * splitTorusGL2 (Real.log t / 2)) * h) := by
    intro h t ht
    rw [hW, whittakerCoefficient_archRealGLAt_J_mul_splitTorusGL2_half_log_of_isArchCompAt ℚ _ _ _ _ ψ
      (isLsXiFunction_of_isIsotypicCuspFormAt _hiso) hw₀ hcen₀ 1 t ht h, ← mul_assoc, sqrt_cpow_mul_inv_sqrt_cpow _ ht,
      one_mul]

  obtain ⟨Fref, hFref⟩ : ∃ Fref : ℂ → ℂ, ∀ z : ℂ,
      Fref z = if hz : z.re ≠ 0 then W (diagOne (archUnitHom w₀ (archRealUnit hw₀ z.re hz)) * t₀) else 0 :=
    ⟨_, fun _ => rfl⟩
  have hFpos : ∀ t : ℝ, 0 < t → Fref t
      = ((Real.sqrt t : ℝ) : ℂ) ^ (u₀ + u₀ + 1 - 1 + 1)
          * W (archRealGLAt hw₀ (splitTorusGL2 (Real.log t / 2)) * t₀) := by
    intro t ht
    rw [hFref, sub_add_cancel]
    simp only [Complex.ofReal_re]
    rw [dif_pos ht.ne']
    exact hpeel t₀ t ht
  have hFneg : ∀ t : ℝ, 0 < t → Fref (-t)
      = ((Real.sqrt t : ℝ) : ℂ) ^ (u₀ + u₀ + 1 - 1 + 1)
          * W (archRealGLAt hw₀ (UpperHalfPlane.J * splitTorusGL2 (Real.log t / 2)) * t₀) := by
    intro t ht
    rw [hFref, sub_add_cancel]
    simp only [Complex.neg_re, Complex.ofReal_re]
    rw [dif_pos (neg_ne_zero.mpr ht.ne')]
    exact hpeelJ t₀ t ht

  obtain ⟨hfp, -, -⟩ := (whittaker_ode_splitTorus_whittakerCoefficient_one_of_isIsotypicCuspFormAt _ _ _ ψ _hψ hw₀
    hψr₀ _hiso _hconv hsm _ hΩ (k₁ w₀) (_hwt w₀ hw₀) W hW t₀ ht₀).1
  obtain ⟨hfm, -, -⟩ := (whittaker_ode_splitTorus_whittakerCoefficient_one_of_isIsotypicCuspFormAt _ _ _ ψ _hψ hw₀
    hψr₀ _hiso _hconv hsm _ hΩ (k₁ w₀) (_hwt w₀ hw₀) W hW t₀ ht₀).2
  have hgr := exists_forall_norm_J_splitTorus_le_mul_rpow c u d₁ d₂ T _hd _hcov ψ _hψ hw₀ hψr₀ _hiso _hne _hconv hsm _
    hΩ _hwt hcen₀ W hW t₀ ht₀
  have hfp_ne : ∃ y : ℝ, 0 < y ∧ W (archRealGLAt hw₀ (splitTorusGL2 (Real.log y / 2)) * t₀) ≠ 0 := by
    refine ⟨r₀, hr₀pos, fun h0 => href ?_⟩
    rw [hpeel t₀ r₀ hr₀pos, h0, mul_zero]

  obtain ⟨-, ρ, hρ, hmel⟩ := mellin_whittakerProfile_eq_GammaC_of_lowering_eq_zero (u₀ + u₀ + 1 - 1) (k₁ w₀) Fref
    (fun y : ℝ => W (archRealGLAt hw₀ (splitTorusGL2 (Real.log y / 2)) * t₀))
    (fun y : ℝ => W (archRealGLAt hw₀ (UpperHalfPlane.J * splitTorusGL2 (Real.log y / 2)) * t₀)) hFpos hFneg hfp hfm
    (fun _ hy => one_sheet_lowering_relation hw₀ hWsm hWk hWψ hlowW ht₀ hfp hy)
    (fun _ hy => J_sheet_lowering_relation hw₀ hWsm hWk hWψ hlowW ht₀ hfm hy) hgr hfp_ne

  obtain ⟨cst, hcst⟩ : ∃ cst : AdelicGL2 (𝓞 ℚ) ℚ → ℂ, ∀ h : AdelicGL2 (𝓞 ℚ) ℚ, cst h
      = W (diagOne (archUnitHom w₀ (archRealUnit hw₀ r₀ hr₀pos.ne')) * h)
          / W (diagOne (archUnitHom w₀ (archRealUnit hw₀ r₀ hr₀pos.ne')) * t₀) := ⟨_, fun _ => rfl⟩
  have hprop : ∀ h : AdelicGL2 (𝓞 ℚ) ℚ, h ∈ finiteAdelicGL2Subgroup ℚ → ∀ (r : ℝ) (hr : r ≠ 0),
      W (diagOne (archUnitHom w₀ (archRealUnit hw₀ r hr)) * h) = cst h * Fref (r : ℂ) := by
    intro h hh r hr
    have hFr : Fref (r : ℂ) = W (diagOne (archUnitHom w₀ (archRealUnit hw₀ r hr)) * t₀) := by
      rw [hFref]
      simp only [Complex.ofReal_re]
      rw [dif_pos hr]
    rw [hFr, hcst]
    rcases lt_or_gt_of_ne hr with hneg_r | hpos_r
    · rw [hneg h hh r hneg_r, hneg t₀ ht₀ r hneg_r, mul_zero]
    · exact hsep h hh r hpos_r
  rw [hW] at hprop
  obtain ⟨C, hC⟩ :=
    exists_forall_whittakerCoefficient_one_diagOne_mul_eq_prod_mul c u d₁ d₂ T ψ φ₁ hw₀ Fref cst hprop ρ hρ

  refine ⟨C, fun par => ⟨φ₁, fun _ z => ρ * Fref z, k₁, _hiso, _hne, _hconv, _hwt, ?_, ?_, hC, ?_, ?_, ?_, ?_⟩⟩
  · intro w hw u₁ u₂ b₁ b₂ h
    rw [hR] at h
    cases h
    rw [hk₁ w hw, signShift_add_signShift_eq_one_of_ne hne (par w)]
    norm_num
  · intro w hw u₀' n' hn' h
    rw [hR] at h
    cases h
  · intro w hw u₁ u₂ b h
    rw [hR] at h
    cases h
    exact absurd rfl hne
  · intro w hw u₀' n' hn' h t ht
    rw [hR] at h
    cases h
  · intro w hw u₁ u₂ b h
    rw [hR] at h
    cases h
    exact absurd rfl hne
  · intro w hw b _
    refine ⟨_, fun s hs => ⟨(hmel b s hs).1, ?_⟩⟩
    refine (hmel b s hs).2.trans ?_
    rw [hR w hw, archFactor_twist_zero_principal_of_ne u₀ hne b, hk₁ w₀ hw₀]
    congr 1
    push_cast
    ring

end OddPrincipalParameter

section EvenPrincipalParameter

private theorem factorizationConclusion_of_evenPrincipal
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
    (ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ) (_hψ : IsGlobalAddChar ℚ ψ)
    (_hψr : ∀ (w : InfinitePlace ℚ), w.IsReal → ∀ x : InfiniteAdeleRing ℚ,
      (∀ w' : InfinitePlace ℚ, w' ≠ w → x w' = 0) →
        ψ (⟨x, 0⟩ : AdeleRing (𝓞 ℚ) ℚ)
          = Complex.exp (2 * Real.pi * Complex.I * extensionEmbedding w (x w)))
    (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (archR : ∀ w : InfinitePlace ℚ, w.IsReal → RealArchParam)
    (_hS : R.exceptionalSet ⊆ S)
    (_htype : ∀ (w : InfinitePlace ℚ) (hw : w.IsReal) (u₁ u₂ : ℂ) (a₁ a₂ : ZMod 2),
      archR w hw = RealArchParam.principal u₁ a₁ u₂ a₂ → |(u₁ - u₂).re| < 1)
    (_hcen : ∀ (w : InfinitePlace ℚ) (hw : w.IsReal),
      IsArchCompAt ℚ (R.centralChar.comp Subgroup.topEquiv.symm.toMonoidHom) w
        ((archR w hw).centralExponent + 1) ((archR w hw).centralSign.val : ℤ))
    (φ₁ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ) (k₁ : InfinitePlace ℚ → ℤ)
    (_hiso : IsIsotypicCuspFormAt ℚ
        (productionPinsOf ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂)
          (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ)
          (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ))
        R.centralChar Φ.level S Φ φ₁)
    (_hne : φ₁ ≠ 0)
    (_hconv : ∃ α : AdelicGL2 (𝓞 ℚ) ℚ → ℂ, IsFactorizableTestFn ℚ α ∧ rightConv ℚ φ₁ α = φ₁)
    (_hwt : ∀ (w : InfinitePlace ℚ) (hw : w.IsReal),
      HasArchCharacterAt₀ ℚ w (archWeightCharAt hw (k₁ w)) φ₁)
    (_hminp : ∀ (w : InfinitePlace ℚ) (hw : w.IsReal) (u₁ u₂ : ℂ) (a₁ a₂ : ZMod 2),
      archR w hw = RealArchParam.principal u₁ a₁ u₂ a₂ →
        (k₁ w = 0 ∨ k₁ w = 1) ∧ ((k₁ w : ZMod 2) = a₁ + a₂))
    (_hmind : ∀ (w : InfinitePlace ℚ) (hw : w.IsReal) (u₀ : ℂ) (n : ℕ) (hn : 1 ≤ n),
      archR w hw = RealArchParam.discrete u₀ n hn → k₁ w = (n : ℤ) + 1)
    (_hpair : ∀ (w : InfinitePlace ℚ) (hw : w.IsReal),
      IsArchSmoothAt hw φ₁ ∧ archCasimirAt hw φ₁ = (archR w hw).laplaceEigenvalue • φ₁)
    (_hJ : ∀ (w : InfinitePlace ℚ) (hw : w.IsReal) (u₁ u₂ : ℂ) (a₁ : ZMod 2),
      archR w hw = RealArchParam.principal u₁ a₁ u₂ a₁ →
        ∀ g : AdelicGL2 (𝓞 ℚ) ℚ, φ₁ (g * archRealGLAt hw UpperHalfPlane.J) = (-1 : ℂ) ^ a₁.val * φ₁ g)
    (_hlow : ∀ (w : InfinitePlace ℚ) (hw : w.IsReal) (u₀ : ℂ) (n : ℕ) (hn : 1 ≤ n),
      archR w hw = RealArchParam.discrete u₀ n hn →
        archDerivAt hw ArchDir.H φ₁
            - Complex.I • (archDerivAt hw ArchDir.E φ₁ + archDerivAt hw ArchDir.Fm φ₁) = 0)
    (_hlow1 : ∀ (w : InfinitePlace ℚ) (hw : w.IsReal) (u₀ : ℂ) (a₁ a₂ : ZMod 2),
      archR w hw = RealArchParam.principal u₀ a₁ u₀ a₂ → a₁ ≠ a₂ →
        archDerivAt hw ArchDir.H φ₁
            - Complex.I • (archDerivAt hw ArchDir.E φ₁ + archDerivAt hw ArchDir.Fm φ₁) = 0)
    (_heq : ∀ (w : InfinitePlace ℚ) (hw : w.IsReal) (u₁ u₂ : ℂ) (a₁ a₂ : ZMod 2),
      archR w hw = RealArchParam.principal u₁ a₁ u₂ a₂ → a₁ = a₂ ∨ u₁ = u₂)
    (w₀ : InfinitePlace ℚ) (hw₀ : w₀.IsReal) (u₁ u₂ : ℂ) (a : ZMod 2)
    (hR : ∀ (w : InfinitePlace ℚ) (hw : w.IsReal), archR w hw = RealArchParam.principal u₁ a u₂ a) :
    FactorizationConclusion c u d₁ d₂ T Φ R ψ S archR := by

  obtain ⟨W, hW⟩ : ∃ W : AdelicGL2 (𝓞 ℚ) ℚ → ℂ, W = whittakerCoefficient ℚ
      (productionPinsOf ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂)
        (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ))
      ψ φ₁ 1 := ⟨_, rfl⟩

  have hsm : IsArchSmoothAt hw₀ φ₁ := (_hpair w₀ hw₀).1
  have hΩ : archCasimirAt hw₀ φ₁ = (1 / 4 - ((u₁ - u₂) / 2) ^ 2) • φ₁ := by
    have h := (_hpair w₀ hw₀).2
    rw [hR w₀ hw₀] at h
    exact archCasimirAt_eq_of_laplaceEigenvalue_principal hw₀ u₁ a u₂ a h
  have hcen₀ := _hcen w₀ hw₀
  rw [hR w₀ hw₀] at hcen₀
  simp only [RealArchParam.centralExponent] at hcen₀
  have hψr₀ := _hψr w₀ hw₀

  have hk₀ : ∀ (w : InfinitePlace ℚ) (hw : w.IsReal), k₁ w = 0 := by
    intro w hw
    obtain ⟨h01, hpar⟩ := _hminp w hw u₁ u₂ a a (hR w hw)
    rcases h01 with h0 | h1
    · exact h0
    · rw [h1, zmod_two_add_self] at hpar
      exact absurd hpar (by decide)
  have hwt₀ : HasArchCharacterAt₀ ℚ w₀ (archWeightCharAt hw₀ 0) φ₁ := by
    have h := _hwt w₀ hw₀
    rwa [hk₀ w₀ hw₀] at h

  have hJ : ∀ g : AdelicGL2 (𝓞 ℚ) ℚ, φ₁ (g * archRealGLAt hw₀ UpperHalfPlane.J) = (-1 : ℂ) ^ a.val * φ₁ g :=
    _hJ w₀ hw₀ u₁ u₂ a (hR w₀ hw₀)
  have hWJ : ∀ x, W (x * archRealGLAt hw₀ UpperHalfPlane.J) = (-1 : ℂ) ^ a.val * W x := by
    intro x
    rw [hW]
    exact whittakerCoefficient_one_mul_eq_of_forall_apply_mul _ ψ hJ x

  have hWsm : IsArchSmoothAt hw₀ W := by
    rw [hW]
    exact (isArchSmoothAt_and_archCasimirAt_whittakerCoefficient_eq_smul
      (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂) (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ)
      (fun v => heckeGen (𝓞 ℚ) ℚ v) ψ _hψ w₀ hw₀ φ₁ hsm _hconv _ hΩ 1).1
  have hWk₀ : HasArchCharacterAt₀ ℚ w₀ (archWeightCharAt hw₀ 0) W := by
    rw [hW]
    exact hasArchCharacterAt₀_whittakerCoefficient_fn ℚ _ ψ φ₁ 1 w₀ _ hwt₀
  have hWψ : ∀ (x : ℝ) (p : AdelicGL2 (𝓞 ℚ) ℚ),
      W (archRealGLAt hw₀ (unipotentGL2 x) * p) = Complex.exp (2 * Real.pi * Complex.I * x) * W p := by
    intro x p
    rw [hW]
    exact apply_archRealGLAt_unipotentGL2_mul_of_forall_unipotentGL2_mul ℚ ψ hw₀ hψr₀ _
      (fun X g' => whittakerCoefficient_one_unipotentGL2_mul_of_isIsotypicCuspFormAt ℚ
        (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂) (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ)
        (fun v => heckeGen (𝓞 ℚ) ℚ v) ψ _hψ _hiso X g') x p
  have hDFm : ∀ p, archDerivAt hw₀ .Fm W p = archDerivAt hw₀ .E W p := by
    intro p
    have h := archDerivAt_E_sub_Fm_apply_of_hasArchCharacterAt₀ hWsm 0 hWk₀ p
    simp only [Int.cast_zero, zero_mul] at h
    exact (sub_eq_zero.mp h).symm

  obtain ⟨g₀, hg₀⟩ := exists_whittakerCoefficient_one_ne_zero_of_isIsotypicCuspFormAt _ _ _ ψ _hψ hw₀ _hiso hsm _hne
  obtain ⟨r₀, hr₀, t₀, ht₀, href⟩ :=
    exists_whittakerCoefficient_one_diagOne_archRealUnit_mul_ne_zero _ _ _ ψ _hψ hw₀ _hiso (_hwt w₀ hw₀) hg₀
  rw [← hW] at href
  obtain ⟨y₀, hy₀, hrefy⟩ : ∃ y₀ : ℝ, ∃ hy₀ : 0 < y₀,
      W (diagOne (archUnitHom w₀ (archRealUnit hw₀ y₀ hy₀.ne')) * t₀) ≠ 0 := by
    rcases lt_or_gt_of_ne hr₀ with hlt | hgt
    · refine ⟨-r₀, neg_pos.mpr hlt, ?_⟩
      rw [apply_diagOne_archRealUnit_neg_mul_eq hw₀ hWJ ht₀ r₀ hr₀ (neg_ne_zero.mpr hr₀)]
      exact mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)) href
    · exact ⟨r₀, hgt, href⟩

  have hsep := whittakerCoefficient_one_diagOne_archRealUnit_mul_eq_div_mul_pos c u d₁ d₂ T _hd _hcov ψ _hψ hw₀ hψr₀
    _hiso _hne _hconv hsm _ hΩ _hwt hcen₀ W hW ht₀ hy₀ hrefy
  have hpeel : ∀ (h : AdelicGL2 (𝓞 ℚ) ℚ) (t : ℝ) (ht : 0 < t),
      W (diagOne (archUnitHom w₀ (archRealUnit hw₀ t ht.ne')) * h)
        = ((Real.sqrt t : ℝ) : ℂ) ^ (u₁ + u₂ + 1) * W (archRealGLAt hw₀ (splitTorusGL2 (Real.log t / 2)) * h) := by
    intro h t ht
    rw [hW, whittakerCoefficient_archRealGLAt_splitTorusGL2_half_log_of_isArchCompAt ℚ _ _ _ _ ψ
      (isLsXiFunction_of_isIsotypicCuspFormAt _hiso) hw₀ hcen₀ 1 t ht h, ← mul_assoc, sqrt_cpow_mul_inv_sqrt_cpow _ ht,
      one_mul]

  have hfJ : ∀ h : AdelicGL2 (𝓞 ℚ) ℚ, h ∈ finiteAdelicGL2Subgroup ℚ → ∀ z : ℝ,
      W (archRealGLAt hw₀ (UpperHalfPlane.J * splitTorusGL2 (Real.log z / 2)) * h)
        = (-1 : ℂ) ^ a.val * W (archRealGLAt hw₀ (splitTorusGL2 (Real.log z / 2)) * h) :=
    fun h hh z => apply_archRealGLAt_J_mul_splitTorusGL2_mul hw₀ hWJ hh (Real.log z / 2)
  obtain ⟨cst, hcst⟩ : ∃ cst : AdelicGL2 (𝓞 ℚ) ℚ → ℂ, ∀ h : AdelicGL2 (𝓞 ℚ) ℚ, cst h
      = W (diagOne (archUnitHom w₀ (archRealUnit hw₀ y₀ hy₀.ne')) * h)
          / W (diagOne (archUnitHom w₀ (archRealUnit hw₀ y₀ hy₀.ne')) * t₀) := ⟨_, fun _ => rfl⟩
  have hfh : ∀ h : AdelicGL2 (𝓞 ℚ) ℚ, h ∈ finiteAdelicGL2Subgroup ℚ → ∀ z : ℝ, 0 < z →
      W (archRealGLAt hw₀ (splitTorusGL2 (Real.log z / 2)) * h)
        = cst h * W (archRealGLAt hw₀ (splitTorusGL2 (Real.log z / 2)) * t₀) := by
    intro h hh z hz
    have h1 := hsep h hh z hz
    rw [hpeel h z hz, hpeel t₀ z hz, ← hcst] at h1
    exact eq_mul_of_sqrt_cpow_mul_eq _ hz h1

  have hode := fun (h : AdelicGL2 (𝓞 ℚ) ℚ) (hh : h ∈ finiteAdelicGL2Subgroup ℚ) =>
    whittaker_ode_splitTorus_whittakerCoefficient_one_of_isIsotypicCuspFormAt _ _ _ ψ _hψ hw₀ hψr₀ _hiso _hconv hsm _
      hΩ 0 hwt₀ W hW h hh
  have hraise : ∀ h : AdelicGL2 (𝓞 ℚ) ℚ, h ∈ finiteAdelicGL2Subgroup ℚ → ∀ s : ℝ, 0 < s →
      archDerivAt hw₀ .H W (archRealGLAt hw₀ (splitTorusGL2 (Real.log s / 2)) * h)
          + Complex.I * (archDerivAt hw₀ .E W (archRealGLAt hw₀ (splitTorusGL2 (Real.log s / 2)) * h)
            + archDerivAt hw₀ .Fm W (archRealGLAt hw₀ (splitTorusGL2 (Real.log s / 2)) * h))
        = 2 * (s : ℂ) * deriv (fun z : ℝ => W (archRealGLAt hw₀ (splitTorusGL2 (Real.log z / 2)) * h)) s
            - 4 * (Real.pi : ℂ) * (s : ℂ) * W (archRealGLAt hw₀ (splitTorusGL2 (Real.log s / 2)) * h) := by
    intro h hh s hs
    have hd := ((hode h hh).1.1 s hs).differentiableAt (Ioi_mem_nhds hs)
    have e := archRaise_expression_apply_sheetDatum hw₀ W hWψ hDFm one_mul_unipotentGL2_eq hh hs
      (by simpa only [one_mul] using hd)
    simpa only [one_mul] using e
  have hraiseJ : ∀ h : AdelicGL2 (𝓞 ℚ) ℚ, h ∈ finiteAdelicGL2Subgroup ℚ → ∀ s : ℝ, 0 < s →
      archDerivAt hw₀ .H W (archRealGLAt hw₀ (UpperHalfPlane.J * splitTorusGL2 (Real.log s / 2)) * h)
          + Complex.I
            * (archDerivAt hw₀ .E W (archRealGLAt hw₀ (UpperHalfPlane.J * splitTorusGL2 (Real.log s / 2)) * h)
              + archDerivAt hw₀ .Fm W (archRealGLAt hw₀ (UpperHalfPlane.J * splitTorusGL2 (Real.log s / 2)) * h))
        = (-1 : ℂ) ^ a.val
            * (2 * (s : ℂ) * deriv (fun z : ℝ => W (archRealGLAt hw₀ (splitTorusGL2 (Real.log z / 2)) * h)) s
              + 4 * (Real.pi : ℂ) * (s : ℂ) * W (archRealGLAt hw₀ (splitTorusGL2 (Real.log s / 2)) * h)) := by
    intro h hh s hs
    have hd := ((hode h hh).2.1 s hs).differentiableAt (Ioi_mem_nhds hs)
    have hfun : (fun z : ℝ => W (archRealGLAt hw₀ (UpperHalfPlane.J * splitTorusGL2 (Real.log z / 2)) * h))
        = fun z : ℝ => (-1 : ℂ) ^ a.val * W (archRealGLAt hw₀ (splitTorusGL2 (Real.log z / 2)) * h) :=
      funext (hfJ h hh)
    rw [archRaise_expression_apply_sheetDatum hw₀ W hWψ hDFm J_mul_unipotentGL2_eq hh hs hd, hfun, deriv_fun_const_mul,
      hfJ h hh s]
    push_cast
    ring

  obtain ⟨φ₂, hφ₂⟩ : ∃ φ₂ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ, φ₂ = (-(1 / (4 * (Real.pi : ℂ)))) • archRaiseAt hw₀ φ₁ :=
    ⟨_, rfl⟩
  have harch₁ : φ₁ ∈ archCutSubmodule ℚ
      (ArchTypeFamily.ofChar ℚ fun w => archWeightCharAt (isReal_infinitePlace_rat w) (k₁ w)) :=
    mem_archCutSubmodule_weightTypeFamilyRat _hwt
  obtain ⟨fa, ff, hfa, hff, hffs, hrep⟩ := exists_tensorTestFn_rightConv_eq_self_of_isIsotypicCuspFormAt c u d₁ d₂ T
    _hd _hcov Φ (fun w => archWeightCharAt (isReal_infinitePlace_rat w) (k₁ w)) _hiso _hne harch₁
  have hiso₂ : IsIsotypicCuspFormAt ℚ
      (productionPinsOf ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂)
        (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ)
        (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ))
      R.centralChar Φ.level S Φ φ₂ := by
    have h := isIsotypicCuspFormAt_smul_comb_of_rightConv_tensorTestFn c u d₁ d₂ T _hd _hcov Φ _hiso _hne hfa hff hffs
      hrep hw₀ 1 Complex.I Complex.I (-(1 / (4 * (Real.pi : ℂ))))
    have hX : archRaiseAt hw₀ φ₁ = (1 : ℂ) • archDerivAt hw₀ .H φ₁ + Complex.I • archDerivAt hw₀ .E φ₁
        + Complex.I • archDerivAt hw₀ .Fm φ₁ := by
      simp only [archRaiseAt, one_smul, smul_add, add_assoc]
    rw [hφ₂, hX]
    exact h
  have hwt₂ : ∀ (w : InfinitePlace ℚ) (hw : w.IsReal), HasArchCharacterAt₀ ℚ w (archWeightCharAt hw 2) φ₂ := by
    intro w hw
    obtain rfl : w = w₀ := Subsingleton.elim w w₀
    have h := hasArchCharacterAt₀_archRaiseAt hsm 0 hwt₀
    simp only [zero_add] at h
    rw [hφ₂]
    exact hasArchCharacterAt₀_smul _ h
  have harch₂ : φ₂ ∈ archCutSubmodule ℚ
      (ArchTypeFamily.ofChar ℚ fun w => archWeightCharAt (isReal_infinitePlace_rat w) ((fun _ => (2 : ℤ)) w)) :=
    mem_archCutSubmodule_weightTypeFamilyRat (k := fun _ => (2 : ℤ)) hwt₂
  obtain ⟨W₂, hW₂⟩ : ∃ W₂ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ, W₂ = whittakerCoefficient ℚ
      (productionPinsOf ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂)
        (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ))
      ψ φ₂ 1 := ⟨_, rfl⟩
  have hW₂apply : ∀ p : AdelicGL2 (𝓞 ℚ) ℚ, W₂ p = (-(1 / (4 * (Real.pi : ℂ))))
      * (archDerivAt hw₀ .H W p + Complex.I * (archDerivAt hw₀ .E W p + archDerivAt hw₀ .Fm W p)) := by
    intro p
    rw [hW₂, hφ₂, whittakerCoefficient_smul_apply, whittakerCoefficient_one_archRaiseAt_apply _ _ _ ψ _hψ hw₀
      _hiso.continuous (fun β g => apply_unipotentGL2_algebraMap_mul_of_isIsotypicCuspFormAt _hiso β g) _hconv hsm p,
      hW]

  have hpeel₂ : ∀ (h : AdelicGL2 (𝓞 ℚ) ℚ) (t : ℝ) (ht : 0 < t),
      W₂ (diagOne (archUnitHom w₀ (archRealUnit hw₀ t ht.ne')) * h)
        = ((Real.sqrt t : ℝ) : ℂ) ^ (u₁ + u₂ + 1) * W₂ (archRealGLAt hw₀ (splitTorusGL2 (Real.log t / 2)) * h) := by
    intro h t ht
    rw [hW₂, whittakerCoefficient_archRealGLAt_splitTorusGL2_half_log_of_isArchCompAt ℚ _ _ _ _ ψ
      (isLsXiFunction_of_isIsotypicCuspFormAt hiso₂) hw₀ hcen₀ 1 t ht h, ← mul_assoc, sqrt_cpow_mul_inv_sqrt_cpow _ ht,
      one_mul]
  have hpeelJ₂ : ∀ (h : AdelicGL2 (𝓞 ℚ) ℚ) (t : ℝ) (ht : 0 < t),
      W₂ (diagOne (archUnitHom w₀ (archRealUnit hw₀ (-t) (neg_ne_zero.mpr ht.ne'))) * h)
        = ((Real.sqrt t : ℝ) : ℂ) ^ (u₁ + u₂ + 1)
            * W₂ (archRealGLAt hw₀ (UpperHalfPlane.J * splitTorusGL2 (Real.log t / 2)) * h) := by
    intro h t ht
    rw [hW₂, whittakerCoefficient_archRealGLAt_J_mul_splitTorusGL2_half_log_of_isArchCompAt ℚ _ _ _ _ ψ
      (isLsXiFunction_of_isIsotypicCuspFormAt hiso₂) hw₀ hcen₀ 1 t ht h, ← mul_assoc, sqrt_cpow_mul_inv_sqrt_cpow _ ht,
      one_mul]
  have hW₂pos : ∀ (h : AdelicGL2 (𝓞 ℚ) ℚ), h ∈ finiteAdelicGL2Subgroup ℚ → ∀ (t : ℝ) (ht : 0 < t),
      W₂ (diagOne (archUnitHom w₀ (archRealUnit hw₀ t ht.ne')) * h)
        = ((Real.sqrt t : ℝ) : ℂ) ^ (u₁ + u₂ + 1) * (-(1 / (4 * (Real.pi : ℂ)))
            * (2 * (t : ℂ) * deriv (fun z : ℝ => W (archRealGLAt hw₀ (splitTorusGL2 (Real.log z / 2)) * h)) t
              - 4 * (Real.pi : ℂ) * (t : ℂ) * W (archRealGLAt hw₀ (splitTorusGL2 (Real.log t / 2)) * h))) := by
    intro h hh t ht
    rw [hpeel₂ h t ht, hW₂apply, hraise h hh t ht]
  have hW₂neg : ∀ (h : AdelicGL2 (𝓞 ℚ) ℚ), h ∈ finiteAdelicGL2Subgroup ℚ → ∀ (t : ℝ) (ht : 0 < t),
      W₂ (diagOne (archUnitHom w₀ (archRealUnit hw₀ (-t) (neg_ne_zero.mpr ht.ne'))) * h)
        = ((Real.sqrt t : ℝ) : ℂ) ^ (u₁ + u₂ + 1) * (-(1 / (4 * (Real.pi : ℂ))) * ((-1 : ℂ) ^ a.val
            * (2 * (t : ℂ) * deriv (fun z : ℝ => W (archRealGLAt hw₀ (splitTorusGL2 (Real.log z / 2)) * h)) t
              + 4 * (Real.pi : ℂ) * (t : ℂ) * W (archRealGLAt hw₀ (splitTorusGL2 (Real.log t / 2)) * h)))) := by
    intro h hh t ht
    rw [hpeelJ₂ h t ht, hW₂apply, hraiseJ h hh t ht]

  obtain ⟨Fref, hFref⟩ : ∃ Fref : ℂ → ℂ, ∀ z : ℂ,
      Fref z = if hz : z.re ≠ 0 then W (diagOne (archUnitHom w₀ (archRealUnit hw₀ z.re hz)) * t₀) else 0 :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨F₂, hF₂⟩ : ∃ F₂ : ℂ → ℂ, ∀ z : ℂ,
      F₂ z = if hz : z.re ≠ 0 then W₂ (diagOne (archUnitHom w₀ (archRealUnit hw₀ z.re hz)) * t₀) else 0 :=
    ⟨_, fun _ => rfl⟩
  have hFr : ∀ (r : ℝ) (hr : r ≠ 0), Fref (r : ℂ) = W (diagOne (archUnitHom w₀ (archRealUnit hw₀ r hr)) * t₀) := by
    intro r hr
    rw [hFref]
    simp only [Complex.ofReal_re]
    rw [dif_pos hr]
  have hF₂r : ∀ (r : ℝ) (hr : r ≠ 0), F₂ (r : ℂ) = W₂ (diagOne (archUnitHom w₀ (archRealUnit hw₀ r hr)) * t₀) := by
    intro r hr
    rw [hF₂]
    simp only [Complex.ofReal_re]
    rw [dif_pos hr]
  have hFnegr : ∀ (r : ℝ) (hr : -r ≠ 0),
      Fref (-(r : ℂ)) = W (diagOne (archUnitHom w₀ (archRealUnit hw₀ (-r) hr)) * t₀) := by
    intro r hr
    rw [hFref]
    simp only [Complex.neg_re, Complex.ofReal_re]
    rw [dif_pos hr]
  have hF₂negr : ∀ (r : ℝ) (hr : -r ≠ 0),
      F₂ (-(r : ℂ)) = W₂ (diagOne (archUnitHom w₀ (archRealUnit hw₀ (-r) hr)) * t₀) := by
    intro r hr
    rw [hF₂]
    simp only [Complex.neg_re, Complex.ofReal_re]
    rw [dif_pos hr]

  have hfp_ne : ∃ y : ℝ, 0 < y ∧ W (archRealGLAt hw₀ (splitTorusGL2 (Real.log y / 2)) * t₀) ≠ 0 := by
    refine ⟨y₀, hy₀, fun h0 => hrefy ?_⟩
    rw [hpeel t₀ y₀ hy₀, h0, mul_zero]
  have hgr := exists_forall_norm_splitTorus_le_mul_rpow c u d₁ d₂ T _hd _hcov ψ _hψ hw₀ hψr₀ _hiso _hne _hconv hsm _ hΩ
    _hwt hcen₀ W hW t₀ ht₀
  obtain ⟨ρ, hρ, hfam₀, hfam₂, hfam₂'⟩ := mellin_whittakerProfile_eq_archFactor_of_whittaker_ode_weightZero u₁ u₂ a
    Fref F₂ (fun y : ℝ => W (archRealGLAt hw₀ (splitTorusGL2 (Real.log y / 2)) * t₀)) (hode t₀ ht₀).1.1
    (hode t₀ ht₀).1.2.1
    (fun y hy => by
      have h := (hode t₀ ht₀).1.2.2 y hy
      push_cast at h
      linear_combination h)
    hgr hfp_ne
    (fun t ht => by rw [hFr t ht.ne', hpeel t₀ t ht])
    (fun t ht => by
      rw [hFnegr t (neg_ne_zero.mpr ht.ne'),
        apply_diagOne_archRealUnit_neg_mul_eq hw₀ hWJ ht₀ t ht.ne' (neg_ne_zero.mpr ht.ne'), hpeel t₀ t ht]
      ring)
    (fun t ht => by rw [hF₂r t ht.ne', hW₂pos t₀ ht₀ t ht])
    (fun t ht => by rw [hF₂negr t (neg_ne_zero.mpr ht.ne'), hW₂neg t₀ ht₀ t ht])

  have hne₂ : φ₂ ≠ 0 := by
    intro h0
    have hW₂0 : W₂ = 0 := by
      rw [hW₂, h0, whittakerCoefficient_zero_fn]
    have hF₂0 : ∀ z : ℂ, F₂ z = 0 := by
      intro z
      rw [hF₂]
      simp [hW₂0]
    have hs : max (-u₁.re) (-u₂.re) < (((max (-u₁.re) (-u₂.re) + 1 : ℝ) : ℂ)).re := by
      rw [Complex.ofReal_re]
      exact lt_add_one _
    have h2 := (hfam₂ ((max (-u₁.re) (-u₂.re) + 1 : ℝ) : ℂ) hs).2
    simp only [hF₂0, mul_zero, add_zero, zero_div] at h2
    have h0' : mellin (fun _ : ℝ => (0 : ℂ)) (((max (-u₁.re) (-u₂.re) + 1 : ℝ) : ℂ)) = 0 := by
      simp [mellin]
    rw [h0'] at h2
    exact mul_ne_zero (two_mul_add_add_sub_one_div_ne_zero u₁ u₂)
      (archFactor_twist_zero_principal_same_parity_ne_zero u₁ u₂ a a hs) h2.symm
  have hconv₂ : ∃ α : AdelicGL2 (𝓞 ℚ) ℚ → ℂ, IsFactorizableTestFn ℚ α ∧ rightConv ℚ φ₂ α = φ₂ := by
    obtain ⟨γ, hγ, -, hγrep⟩ := exists_isFactorizableTestFn_rightConv_eq_self_of_isIsotypicCuspFormAt c u d₁ d₂ T _hd
      _hcov Φ (fun w => archWeightCharAt (isReal_infinitePlace_rat w) ((fun _ => (2 : ℤ)) w)) hiso₂ hne₂ harch₂
    exact ⟨γ, hγ, hγrep⟩

  have hprop : ∀ h : AdelicGL2 (𝓞 ℚ) ℚ, h ∈ finiteAdelicGL2Subgroup ℚ → ∀ (r : ℝ) (hr : r ≠ 0),
      W (diagOne (archUnitHom w₀ (archRealUnit hw₀ r hr)) * h) = cst h * Fref (r : ℂ) := by
    intro h hh r hr
    rw [hFr r hr]
    rcases lt_or_gt_of_ne hr with hneg_r | hpos_r
    · have hr' : 0 < -r := neg_pos.mpr hneg_r
      rw [apply_diagOne_archRealUnit_mul_eq_mul_apply_neg hw₀ hWJ hh r hr hr'.ne',
        apply_diagOne_archRealUnit_mul_eq_mul_apply_neg hw₀ hWJ ht₀ r hr hr'.ne', hpeel h (-r) hr', hpeel t₀ (-r) hr',
        hfh h hh (-r) hr']
      ring
    · rw [hpeel h r hpos_r, hpeel t₀ r hpos_r, hfh h hh r hpos_r]
      ring
  have hprop₂ : ∀ h : AdelicGL2 (𝓞 ℚ) ℚ, h ∈ finiteAdelicGL2Subgroup ℚ → ∀ (r : ℝ) (hr : r ≠ 0),
      W₂ (diagOne (archUnitHom w₀ (archRealUnit hw₀ r hr)) * h) = cst h * F₂ (r : ℂ) := by
    intro h hh r hr
    rw [hF₂r r hr]
    rcases lt_or_gt_of_ne hr with hneg_r | hpos_r
    · have hr' : 0 < -r := neg_pos.mpr hneg_r
      rw [archRealUnit_congr hw₀ (neg_neg r).symm hr (neg_ne_zero.mpr hr'.ne'), hW₂neg h hh (-r) hr',
        hW₂neg t₀ ht₀ (-r) hr', deriv_eq_of_forall_pos_eq (hfh h hh) hr', deriv_fun_const_mul, hfh h hh (-r) hr']
      ring
    · rw [hW₂pos h hh r hpos_r, hW₂pos t₀ ht₀ r hpos_r, deriv_eq_of_forall_pos_eq (hfh h hh) hpos_r,
        deriv_fun_const_mul, hfh h hh r hpos_r]
      ring
  rw [hW] at hprop
  rw [hW₂] at hprop₂
  have hC₁ := whittakerCoefficient_one_diagOne_mul_eq_prod_mul_factorConstant c u d₁ d₂ T ψ φ₁ hw₀ Fref cst hprop ρ hρ
  have hC₂ := whittakerCoefficient_one_diagOne_mul_eq_prod_mul_factorConstant c u d₁ d₂ T ψ φ₂ hw₀ F₂ cst hprop₂ ρ hρ

  refine ⟨factorConstant cst ρ, fun par => ?_⟩
  have hpw : ∀ w : InfinitePlace ℚ, par w = par w₀ := fun w => by rw [Subsingleton.elim w w₀]
  rcases zmod_two_eq_or_eq_add_one (par w₀) a with hp | hp
  ·
    refine ⟨φ₁, fun _ z => ρ * Fref z, k₁, _hiso, _hne, _hconv, _hwt, ?_, ?_, hC₁, ?_, ?_, ?_, ?_⟩
    · intro w hw u₁' u₂' b₁ b₂ h
      rw [hR] at h
      cases h
      simp only [hk₀ w hw, hpw w, hp, signShift_add_signShift_self, Int.cast_zero]
    · intro w hw u₀' n' hn' h
      rw [hR] at h
      cases h
    · intro w hw u₁' u₂' b h _ t
      rw [hR] at h
      cases h
      dsimp only
      rcases eq_or_ne t 0 with rfl | ht
      · rw [hFref, hFref]
        simp
      · rw [hFnegr t (neg_ne_zero.mpr ht), hFr t ht,
          apply_diagOne_archRealUnit_neg_mul_eq hw₀ hWJ ht₀ t ht (neg_ne_zero.mpr ht)]
        ring
    · intro w hw u₀' n' hn' h
      rw [hR] at h
      cases h
    · intro w hw u₁' u₂' b h hpar
      rw [hR] at h
      cases h
      rw [hpw w, hp] at hpar
      exact absurd hpar (zmod_two_ne_add_one _)
    · intro w hw b hb
      rw [hR w hw, centralSign_principal_same_parity, add_zero, hpw w, hp, or_self] at hb
      subst hb
      refine ⟨_, fun s hs => ⟨(hfam₀ s hs).1, ?_⟩⟩
      rw [hR w hw]
      exact (hfam₀ s hs).2
  ·
    refine ⟨φ₂, fun _ z => ρ * F₂ z, fun _ => (2 : ℤ), hiso₂, hne₂, hconv₂, hwt₂, ?_, ?_, hC₂, ?_, ?_, ?_, ?_⟩
    · intro w hw u₁' u₂' b₁ b₂ h
      rw [hR] at h
      cases h
      simp only [hpw w, hp, signShift_add_signShift_add_one, Int.cast_ofNat]
    · intro w hw u₀' n' hn' h
      rw [hR] at h
      cases h
    · intro w hw u₁' u₂' b h hpar
      rw [hR] at h
      cases h
      rw [hpw w, hp] at hpar
      exact absurd hpar.symm (zmod_two_ne_add_one _)
    · intro w hw u₀' n' hn' h
      rw [hR] at h
      cases h
    · intro w hw u₁' u₂' b h _
      rw [hR] at h
      cases h
      refine ⟨_, fun s hs => ⟨(hfam₂ s hs).1, ?_⟩⟩
      rw [hR w hw]
      exact (hfam₂ s hs).2
    · intro w hw b hb
      rw [hR w hw, centralSign_principal_same_parity, add_zero, hpw w, hp, or_self] at hb
      subst hb
      refine ⟨_, fun s hs => ⟨(hfam₂' s hs).1, ?_⟩⟩
      rw [hR w hw]
      exact (hfam₂' s hs).2

end EvenPrincipalParameter

section CombinationOfCases

private theorem factorizationConclusion_of_archParam
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
    (ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ) (_hψ : IsGlobalAddChar ℚ ψ)
    (_hψr : ∀ (w : InfinitePlace ℚ), w.IsReal → ∀ x : InfiniteAdeleRing ℚ,
      (∀ w' : InfinitePlace ℚ, w' ≠ w → x w' = 0) →
        ψ (⟨x, 0⟩ : AdeleRing (𝓞 ℚ) ℚ)
          = Complex.exp (2 * Real.pi * Complex.I * extensionEmbedding w (x w)))
    (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (archR : ∀ w : InfinitePlace ℚ, w.IsReal → RealArchParam)
    (_hS : R.exceptionalSet ⊆ S)
    (_htype : ∀ (w : InfinitePlace ℚ) (hw : w.IsReal) (u₁ u₂ : ℂ) (a₁ a₂ : ZMod 2),
      archR w hw = RealArchParam.principal u₁ a₁ u₂ a₂ → |(u₁ - u₂).re| < 1)
    (_hcen : ∀ (w : InfinitePlace ℚ) (hw : w.IsReal),
      IsArchCompAt ℚ (R.centralChar.comp Subgroup.topEquiv.symm.toMonoidHom) w
        ((archR w hw).centralExponent + 1) ((archR w hw).centralSign.val : ℤ))
    (φ₁ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ) (k₁ : InfinitePlace ℚ → ℤ)
    (_hiso : IsIsotypicCuspFormAt ℚ
        (productionPinsOf ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂)
          (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ)
          (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ))
        R.centralChar Φ.level S Φ φ₁)
    (_hne : φ₁ ≠ 0)
    (_hconv : ∃ α : AdelicGL2 (𝓞 ℚ) ℚ → ℂ, IsFactorizableTestFn ℚ α ∧ rightConv ℚ φ₁ α = φ₁)
    (_hwt : ∀ (w : InfinitePlace ℚ) (hw : w.IsReal),
      HasArchCharacterAt₀ ℚ w (archWeightCharAt hw (k₁ w)) φ₁)
    (_hminp : ∀ (w : InfinitePlace ℚ) (hw : w.IsReal) (u₁ u₂ : ℂ) (a₁ a₂ : ZMod 2),
      archR w hw = RealArchParam.principal u₁ a₁ u₂ a₂ →
        (k₁ w = 0 ∨ k₁ w = 1) ∧ ((k₁ w : ZMod 2) = a₁ + a₂))
    (_hmind : ∀ (w : InfinitePlace ℚ) (hw : w.IsReal) (u₀ : ℂ) (n : ℕ) (hn : 1 ≤ n),
      archR w hw = RealArchParam.discrete u₀ n hn → k₁ w = (n : ℤ) + 1)
    (_hpair : ∀ (w : InfinitePlace ℚ) (hw : w.IsReal),
      IsArchSmoothAt hw φ₁ ∧ archCasimirAt hw φ₁ = (archR w hw).laplaceEigenvalue • φ₁)
    (_hJ : ∀ (w : InfinitePlace ℚ) (hw : w.IsReal) (u₁ u₂ : ℂ) (a₁ : ZMod 2),
      archR w hw = RealArchParam.principal u₁ a₁ u₂ a₁ →
        ∀ g : AdelicGL2 (𝓞 ℚ) ℚ, φ₁ (g * archRealGLAt hw UpperHalfPlane.J) = (-1 : ℂ) ^ a₁.val * φ₁ g)
    (_hlow : ∀ (w : InfinitePlace ℚ) (hw : w.IsReal) (u₀ : ℂ) (n : ℕ) (hn : 1 ≤ n),
      archR w hw = RealArchParam.discrete u₀ n hn →
        archDerivAt hw ArchDir.H φ₁
            - Complex.I • (archDerivAt hw ArchDir.E φ₁ + archDerivAt hw ArchDir.Fm φ₁) = 0)
    (_hlow1 : ∀ (w : InfinitePlace ℚ) (hw : w.IsReal) (u₀ : ℂ) (a₁ a₂ : ZMod 2),
      archR w hw = RealArchParam.principal u₀ a₁ u₀ a₂ → a₁ ≠ a₂ →
        archDerivAt hw ArchDir.H φ₁
            - Complex.I • (archDerivAt hw ArchDir.E φ₁ + archDerivAt hw ArchDir.Fm φ₁) = 0)
    (_heq : ∀ (w : InfinitePlace ℚ) (hw : w.IsReal) (u₁ u₂ : ℂ) (a₁ a₂ : ZMod 2),
      archR w hw = RealArchParam.principal u₁ a₁ u₂ a₂ → a₁ = a₂ ∨ u₁ = u₂) :
    FactorizationConclusion c u d₁ d₂ T Φ R ψ S archR := by
  obtain ⟨w₀⟩ := (inferInstance : Nonempty (InfinitePlace ℚ))
  have hw₀ : w₀.IsReal := isReal_infinitePlace_rat w₀
  have hall : ∀ P : RealArchParam, archR w₀ hw₀ = P → ∀ (w : InfinitePlace ℚ) (hw : w.IsReal), archR w hw = P := by
    intro P hP w hw
    obtain rfl : w = w₀ := Subsingleton.elim w w₀
    exact hP
  rcases hP : archR w₀ hw₀ with ⟨u₁, a₁, u₂, a₂⟩ | ⟨u₀, n, hn⟩
  · rcases _heq w₀ hw₀ u₁ u₂ a₁ a₂ hP with rfl | rfl
    · have hR := hall _ hP
      exact factorizationConclusion_of_evenPrincipal c u d₁ d₂ T _hd _hcov Φ R _hR ψ _hψ _hψr S archR _hS _htype
        _hcen φ₁ k₁ _hiso _hne _hconv _hwt _hminp _hmind _hpair _hJ _hlow _hlow1 _heq w₀ hw₀ u₁ u₂ a₁ hR
    · by_cases hpar : a₁ = a₂
      · subst hpar
        have hR := hall _ hP
        exact factorizationConclusion_of_evenPrincipal c u d₁ d₂ T _hd _hcov Φ R _hR ψ _hψ _hψr S archR _hS _htype
          _hcen φ₁ k₁ _hiso _hne _hconv _hwt _hminp _hmind _hpair _hJ _hlow _hlow1 _heq w₀ hw₀ u₁ u₁ a₁ hR
      · have hne : a₁ ≠ a₂ := hpar
        have hR := hall _ hP
        exact factorizationConclusion_of_oddPrincipal c u d₁ d₂ T _hd _hcov Φ R _hR ψ _hψ _hψr S archR _hS _htype
          _hcen φ₁ k₁ _hiso _hne _hconv _hwt _hminp _hmind _hpair _hJ _hlow _hlow1 _heq w₀ hw₀ u₁ hne hR
  · have hR := hall _ hP
    exact factorizationConclusion_of_discrete c u d₁ d₂ T _hd _hcov Φ R _hR ψ _hψ _hψr S archR _hS _htype _hcen φ₁
      k₁ _hiso _hne _hconv _hwt _hminp _hmind _hpair _hJ _hlow _hlow1 _heq w₀ hw₀ u₀ n hn hR

end CombinationOfCases

end MinimalWeightWhittaker
p2m_reactivate "P2MW.S_LanglandsTunnell_exists_whittaker_factorization_of_archCasimir_eigenvector_minimalWeight.MinimalWeightWhittaker"

open MinimalWeightWhittaker in

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
    (_hR : Continuous R.toFun)
    (ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ) (_hψ : IsGlobalAddChar ℚ ψ)
    (_hψr : ∀ (w : InfinitePlace ℚ), w.IsReal → ∀ x : InfiniteAdeleRing ℚ,
      (∀ w' : InfinitePlace ℚ, w' ≠ w → x w' = 0) →
        ψ (⟨x, 0⟩ : AdeleRing (𝓞 ℚ) ℚ)
          = Complex.exp (2 * Real.pi * Complex.I * extensionEmbedding w (x w)))
    (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (archR : ∀ w : InfinitePlace ℚ, w.IsReal → RealArchParam)
    (_hS : R.exceptionalSet ⊆ S)
    (_htype : ∀ (w : InfinitePlace ℚ) (hw : w.IsReal) (u₁ u₂ : ℂ) (a₁ a₂ : ZMod 2),
      archR w hw = RealArchParam.principal u₁ a₁ u₂ a₂ → |(u₁ - u₂).re| < 1)
    (_hcen : ∀ (w : InfinitePlace ℚ) (hw : w.IsReal),
      IsArchCompAt ℚ (R.centralChar.comp Subgroup.topEquiv.symm.toMonoidHom) w
        ((archR w hw).centralExponent + 1) ((archR w hw).centralSign.val : ℤ))
    (φ₁ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ) (k₁ : InfinitePlace ℚ → ℤ)
    (_hiso : IsIsotypicCuspFormAt ℚ
        (productionPinsOf ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂)
          (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ)
          (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ))
        R.centralChar Φ.level S Φ φ₁)
    (_hne : φ₁ ≠ 0)
    (_hconv : ∃ α : AdelicGL2 (𝓞 ℚ) ℚ → ℂ, IsFactorizableTestFn ℚ α ∧ rightConv ℚ φ₁ α = φ₁)
    (_hwt : ∀ (w : InfinitePlace ℚ) (hw : w.IsReal),
      HasArchCharacterAt₀ ℚ w (archWeightCharAt hw (k₁ w)) φ₁)
    (_hminp : ∀ (w : InfinitePlace ℚ) (hw : w.IsReal) (u₁ u₂ : ℂ) (a₁ a₂ : ZMod 2),
      archR w hw = RealArchParam.principal u₁ a₁ u₂ a₂ →
        (k₁ w = 0 ∨ k₁ w = 1) ∧ ((k₁ w : ZMod 2) = a₁ + a₂))
    (_hmind : ∀ (w : InfinitePlace ℚ) (hw : w.IsReal) (u₀ : ℂ) (n : ℕ) (hn : 1 ≤ n),
      archR w hw = RealArchParam.discrete u₀ n hn → k₁ w = (n : ℤ) + 1)
    (_hpair : ∀ (w : InfinitePlace ℚ) (hw : w.IsReal),
      IsArchSmoothAt hw φ₁ ∧ archCasimirAt hw φ₁ = (archR w hw).laplaceEigenvalue • φ₁)
    (_hJ : ∀ (w : InfinitePlace ℚ) (hw : w.IsReal) (u₁ u₂ : ℂ) (a₁ : ZMod 2),
      archR w hw = RealArchParam.principal u₁ a₁ u₂ a₁ →
        ∀ g : AdelicGL2 (𝓞 ℚ) ℚ, φ₁ (g * archRealGLAt hw UpperHalfPlane.J) = (-1 : ℂ) ^ a₁.val * φ₁ g)
    (_hlow : ∀ (w : InfinitePlace ℚ) (hw : w.IsReal) (u₀ : ℂ) (n : ℕ) (hn : 1 ≤ n),
      archR w hw = RealArchParam.discrete u₀ n hn →
        archDerivAt hw ArchDir.H φ₁
            - Complex.I • (archDerivAt hw ArchDir.E φ₁ + archDerivAt hw ArchDir.Fm φ₁) = 0)
    (_hlow1 : ∀ (w : InfinitePlace ℚ) (hw : w.IsReal) (u₀ : ℂ) (a₁ a₂ : ZMod 2),
      archR w hw = RealArchParam.principal u₀ a₁ u₀ a₂ → a₁ ≠ a₂ →
        archDerivAt hw ArchDir.H φ₁
            - Complex.I • (archDerivAt hw ArchDir.E φ₁ + archDerivAt hw ArchDir.Fm φ₁) = 0)
    (_heq : ∀ (w : InfinitePlace ℚ) (hw : w.IsReal) (u₁ u₂ : ℂ) (a₁ a₂ : ZMod 2),
      archR w hw = RealArchParam.principal u₁ a₁ u₂ a₂ → a₁ = a₂ ∨ u₁ = u₂) :
    ∃ C : FiniteAdeleRing (𝓞 ℚ) ℚ → AdelicGL2 (𝓞 ℚ) ℚ → ℂ,
    ∀ par : InfinitePlace ℚ → ZMod 2,
      ∃ (φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ) (Wr : InfinitePlace ℚ → ℂ → ℂ) (k : InfinitePlace ℚ → ℤ),
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
            (k w : ℂ) = signShift (a₁ + par w) + signShift (a₂ + par w)) ∧
        (∀ (w : InfinitePlace ℚ) (hw : w.IsReal) (u₀ : ℂ) (n : ℕ) (hn : 1 ≤ n),
          archR w hw = RealArchParam.discrete u₀ n hn → k w = (n : ℤ) + 1) ∧
        (∀ a : (AdeleRing (𝓞 ℚ) ℚ)ˣ, ∀ g : AdelicGL2 (𝓞 ℚ) ℚ, g ∈ finiteAdelicGL2Subgroup ℚ →
            whittakerCoefficient ℚ
                (productionPinsOf ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂)
                  (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ)
                  (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ))
                ψ φ 1 (diagOne a * g)
              = (∏ w : InfinitePlace ℚ, Wr w (extensionEmbedding w ((a : AdeleRing (𝓞 ℚ) ℚ).1 w)))
                  * C (a : AdeleRing (𝓞 ℚ) ℚ).2 g) ∧
        (∀ (w : InfinitePlace ℚ) (hw : w.IsReal) (u₁ u₂ : ℂ) (a₁ : ZMod 2),
          archR w hw = RealArchParam.principal u₁ a₁ u₂ a₁ → par w = a₁ →
            ∀ t : ℝ, Wr w (-t) = (-1 : ℂ) ^ a₁.val * Wr w t) ∧
        (∀ (w : InfinitePlace ℚ) (hw : w.IsReal) (u₀ : ℂ) (n : ℕ) (hn : 1 ≤ n),
          archR w hw = RealArchParam.discrete u₀ n hn → ∀ t : ℝ, t < 0 → Wr w t = 0) ∧
        (∀ (w : InfinitePlace ℚ) (hw : w.IsReal) (u₁ u₂ : ℂ) (a₁ : ZMod 2),
          archR w hw = RealArchParam.principal u₁ a₁ u₂ a₁ → par w = a₁ + 1 →
            ∃ s₀ : ℝ, ∀ s : ℂ, s₀ < s.re →
              MellinConvergent
                  (fun t : ℝ => (Wr w t + (-1 : ℂ) ^ a₁.val * Wr w (-t)) / (t : ℂ)) s ∧
                mellin (fun t : ℝ => (Wr w t + (-1 : ℂ) ^ a₁.val * Wr w (-t)) / (t : ℂ)) s
                  = (2 * s + u₁ + u₂ - 1) / (4 * (Real.pi : ℂ))
                      * ((archR w hw).twist 0 a₁).archFactor s) ∧
        (∀ (w : InfinitePlace ℚ) (hw : w.IsReal) (b : ZMod 2),
          (b = par w ∨ b = par w + (archR w hw).centralSign) →
            ∃ s₀ : ℝ, ∀ s : ℂ, s₀ < s.re →
              MellinConvergent
                  (fun t : ℝ => (Wr w t + (-1 : ℂ) ^ b.val * Wr w (-t)) / (t : ℂ)) s ∧
                mellin (fun t : ℝ => (Wr w t + (-1 : ℂ) ^ b.val * Wr w (-t)) / (t : ℂ)) s
                  = ((archR w hw).twist 0 b).archFactor s) := by
  exact factorizationConclusion_of_archParam c u d₁ d₂ T _hd _hcov Φ R _hR ψ _hψ _hψr S archR _hS _htype _hcen φ₁ k₁
    _hiso _hne _hconv _hwt _hminp _hmind _hpair _hJ _hlow _hlow1 _heq

end S_LanglandsTunnell_exists_whittaker_factorization_of_archCasimir_eigenvector_minimalWeight
end P2MW
export P2MW.S_LanglandsTunnell_exists_whittaker_factorization_of_archCasimir_eigenvector_minimalWeight (solution)
