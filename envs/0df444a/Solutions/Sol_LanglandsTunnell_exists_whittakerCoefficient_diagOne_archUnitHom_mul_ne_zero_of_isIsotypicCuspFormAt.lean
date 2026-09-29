-- Prove2me | solution 1 for LanglandsTunnell.exists_whittakerCoefficient_diagOne_archUnitHom_mul_ne_zero_of_isIsotypicCuspFormAt
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/8576f335-b572-5b96-bd27-148360767d8f

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
import Theorems.Thm_AutomorphicForm_whittakerCoefficientIntegrable_and_summable_of_isKfSmooth_of_contDiff
import Theorems.Thm_AutomorphicForm_exists_whittakerCoefficient_one_ne_zero
import Theorems.Thm_AutomorphicForm_continuous_unipotentGL2
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_exists_whittakerCoefficient_diagOne_archUnitHom_mul_ne_zero_of_isIsotypicCuspFormAt
p2m_attr_erase "instance" "instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions"
p2m_attr_erase "simp" "ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply"

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
end Peeling
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
end MinimalWeightWhittaker

open MinimalWeightWhittaker in
theorem solution
    (D : Set (AdelicGL2 (𝓞 ℚ) ℚ)) (U : Ideal (𝓞 ℚ) → Subgroup (AdelicGL2 (𝓞 ℚ) ℚ))
    (gen : HeightOneSpectrum (𝓞 ℚ) → AdelicGL2 (𝓞 ℚ) ℚ)
    (ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ) (hψ : IsGlobalAddChar ℚ ψ) (w : InfinitePlace ℚ) (hw : w.IsReal)
    (ξ : (productionPinsOf ℚ D U gen (adelicBox ℚ)).Z →* ℂˣ) (N : Ideal (𝓞 ℚ)) (S : Finset (HeightOneSpectrum (𝓞 ℚ)))
    (Φ : HeckeEigensystem ℚ ℂ) (φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ)
    (hiso : IsIsotypicCuspFormAt ℚ (productionPinsOf ℚ D U gen (adelicBox ℚ)) ξ N S Φ φ)
    (hsm : IsArchSmoothAt hw φ) (hne : φ ≠ 0)
    (χ : rowIsometrySubgroup₀ w.Completion →* ℂˣ) (hwt : HasArchCharacterAt₀ ℚ w χ φ) :
    ∃ (y : ℝ) (t : AdelicGL2 (𝓞 ℚ) ℚ), y ≠ 0 ∧ t ∈ finiteAdelicGL2Subgroup ℚ ∧ ∀ r : (w.Completion)ˣ,
      (r : w.Completion) = (ringEquivRealOfIsReal hw).symm y →
        whittakerCoefficient ℚ (productionPinsOf ℚ D U gen (adelicBox ℚ)) ψ φ 1 (diagOne (archUnitHom w r) * t) ≠ 0 := by
  obtain ⟨g₀, hg₀⟩ := exists_whittakerCoefficient_one_ne_zero_of_isIsotypicCuspFormAt D U gen ψ hψ hw hiso hsm hne
  obtain ⟨r₀, hr₀, t₀, ht₀, href⟩ :=
    exists_whittakerCoefficient_one_diagOne_archRealUnit_mul_ne_zero D U gen ψ hψ hw hiso hwt hg₀
  refine ⟨r₀, t₀, hr₀, ht₀, fun r hr => ?_⟩
  have hr' : r = archRealUnit hw r₀ hr₀ := Units.ext hr
  subst hr'
  exact href

end S_LanglandsTunnell_exists_whittakerCoefficient_diagOne_archUnitHom_mul_ne_zero_of_isIsotypicCuspFormAt
end P2MW
export P2MW.S_LanglandsTunnell_exists_whittakerCoefficient_diagOne_archUnitHom_mul_ne_zero_of_isIsotypicCuspFormAt (solution)
