-- Prove2me | solution 1 for LanglandsTunnell.whittakerCoefficient_diagOne_neg_eq_zero_of_isIsotypicCuspFormAt_of_lowering_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/eb7001bf-af5d-5672-880e-92a015f55796

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
import Theorems.Thm_NumberField_TateGlobal_ideleNorm_eq_prod_norm_infinitePlace_pow_mult_of_snd_eq_one
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
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_whittakerCoefficient_diagOne_neg_eq_zero_of_isIsotypicCuspFormAt_of_lowering_eq_zero
p2m_attr_erase "instance" "instCountableOfNumberField_definitions AutomorphicForm.compactSpace_maximalCompactAway AutomorphicForm.compactSpace_adelicMaximalCompact AutomorphicForm.isProbabilityMeasure_maximalCompactHaar AutomorphicForm.isHaarMeasure_maximalCompactHaar AutomorphicForm.compactSpace_maximalCompactAt AutomorphicForm.isProbabilityMeasure_maximalCompactAwayHaar AutomorphicForm.isHaarMeasure_maximalCompactAwayHaar AutomorphicForm.isProbabilityMeasure_maximalCompactAtHaar AutomorphicForm.isHaarMeasure_maximalCompactAtHaar instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions"
p2m_attr_erase "simp" "AutomorphicForm.CuspidalConstituent.rightRegular_apply ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply"

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

end CoefficientODE
end WeightTransferAndCasimirEquation
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
section GrowthOfSheetFunctions
section GrowthOfSheets

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
      | (have h__af := (Real.hasDerivAt_sin 0).neg; simp at h__af; exact h__af)

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

end
end ArchimedeanDerivations
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
end MinimalWeightWhittaker

open MinimalWeightWhittaker in
theorem solution
    (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 ℚ) ℚ)) (hd : d₁ < d₂)
    (hcov : CoversModCentre ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂))
    (ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ) (hψ : IsGlobalAddChar ℚ ψ) (w : InfinitePlace ℚ) (hw : w.IsReal)
    (hψr : ∀ x : InfiniteAdeleRing ℚ, (∀ w' : InfinitePlace ℚ, w' ≠ w → x w' = 0) →
      ψ (⟨x, 0⟩ : AdeleRing (𝓞 ℚ) ℚ) = Complex.exp (2 * Real.pi * Complex.I * extensionEmbedding w (x w)))
    (ξ : (productionPinsOf ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂)
      (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ)).Z →* ℂˣ)
    (N : Ideal (𝓞 ℚ)) (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (Φ : HeckeEigensystem ℚ ℂ)
    (φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ)
    (hiso : IsIsotypicCuspFormAt ℚ (productionPinsOf ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂)
      (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ)) ξ N S Φ φ)
    (hne : φ ≠ 0) (hconv : ∃ α : AdelicGL2 (𝓞 ℚ) ℚ → ℂ, IsFactorizableTestFn ℚ α ∧ rightConv ℚ φ α = φ)
    (hsm : IsArchSmoothAt hw φ) (ν : ℂ) (hΩ : archCasimirAt hw φ = (1 / 4 - ν ^ 2) • φ)
    (k : InfinitePlace ℚ → ℤ)
    (hwt : ∀ (w' : InfinitePlace ℚ) (hw' : w'.IsReal), HasArchCharacterAt₀ ℚ w' (archWeightCharAt hw' (k w')) φ)
    (uc : ℂ) (ac : ℤ) (hcen : IsArchCompAt ℚ (ξ.comp Subgroup.topEquiv.symm.toMonoidHom) w uc ac)
    (W : AdelicGL2 (𝓞 ℚ) ℚ → ℂ)
    (hW : W = whittakerCoefficient ℚ
      (productionPinsOf ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂)
        (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ))
      ψ φ 1)
    (hlowW : ∀ p : AdelicGL2 (𝓞 ℚ) ℚ,
      archDerivAt hw ArchDir.H W p - Complex.I * (archDerivAt hw ArchDir.E W p + archDerivAt hw ArchDir.Fm W p) = 0)
    (g : AdelicGL2 (𝓞 ℚ) ℚ) (hg : g ∈ finiteAdelicGL2Subgroup ℚ) (t : ℝ) (ht : t < 0)
    (r : (w.Completion)ˣ) (hr : (r : w.Completion) = (ringEquivRealOfIsReal hw).symm t) :
    W (diagOne (archUnitHom w r) * g) = 0 := by
  have hr' : r = archRealUnit hw t ht.ne := Units.ext hr
  subst hr'
  exact whittakerCoefficient_one_diagOne_archRealUnit_neg_eq_zero_of_lowering c u d₁ d₂ T hd hcov ψ hψ hw hψr hiso hne
    hconv hsm ν hΩ hwt hcen W hW hlowW g hg t ht

end S_LanglandsTunnell_whittakerCoefficient_diagOne_neg_eq_zero_of_isIsotypicCuspFormAt_of_lowering_eq_zero
end P2MW
export P2MW.S_LanglandsTunnell_whittakerCoefficient_diagOne_neg_eq_zero_of_isIsotypicCuspFormAt_of_lowering_eq_zero (solution)
