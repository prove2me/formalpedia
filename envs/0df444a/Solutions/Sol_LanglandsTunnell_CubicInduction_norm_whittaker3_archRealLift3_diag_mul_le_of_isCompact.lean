-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.norm_whittaker3_archRealLift3_diag_mul_le_of_isCompact
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/2c9c3325-e354-5d0e-8b21-5c883f313b35

import Definitions.Def_LanglandsTunnell_CubicInduction_ArchCentre3
import Definitions.Def_LanglandsTunnell_CubicInduction_AutomorphyDatum31
import Definitions.Def_NumberField_StandardGlobalAddCharRat
import Definitions.Def_LanglandsTunnell_CubicInduction_ArchSmoothSpace3
import Definitions.Def_LanglandsTunnell_CubicInduction_Growth
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_AutomorphicForm_SmoothingKernel
import Theorems.Thm_NumberField_AdeleRing_secondCountableTopology
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_CubicInduction_norm_whittaker3_archRealLift3_diag_mul_le_of_isCompact
p2m_attr_erase "instance" "instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions"
p2m_attr_erase "simp" "ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply"

set_option autoImplicit false

noncomputable section

open IsDedekindDomain NumberField AutomorphicForm AutomorphicForm.StandardKernel WhittakerBlock LanglandsTunnell.CubicInduction.WhittakerBlock

namespace LanglandsTunnell
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "WhittakerBlock.archDeriv AdelicGL upperUnipotent3 localMaximalCompact3 mem_localMaximalCompact3_iff componentAtN componentAt3 archComponent3 whittaker3 archPlaceComponent3 matrixSize matrixSize_nonneg matrixSupSize archGauge3 finGauge3 gauge3 one_le_gauge3 one_le_archGauge3 WhittakerBlock.archRealLift3_mul WhittakerBlock.archDeriv_eq_fderiv"
namespace ArchCalculus
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

private theorem realCoord_ofReal (r : ℝ) : realCoord (ofReal r) = r := by
  show (InfinitePlace.Completion.ringEquivRealOfIsReal Rat.isReal_infinitePlace)
      ((InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal Rat.infinitePlace)).symm r) = r
  exact RingEquiv.apply_symm_apply _ r

private def realEquiv : InfiniteAdeleRing ℚ ≃+* ℝ where
  toFun := realCoord
  invFun := ofReal
  left_inv := ofReal_realCoord
  right_inv := realCoord_ofReal
  map_mul' := map_mul realCoord
  map_add' := map_add realCoord

private def ofRealHom : ℝ →+* InfiniteAdeleRing ℚ := realEquiv.symm.toRingHom

@[scoped simp] private theorem ofRealHom_apply (r : ℝ) : ofRealHom r = ofReal r := rfl

@[scoped simp] private theorem ofRealHom_realCoord (x : InfiniteAdeleRing ℚ) : ofRealHom
    (realCoord x) = x := ofReal_realCoord x

private theorem map_realCoord_map_ofRealHom (M : Matrix (Fin 3) (Fin 3) (InfiniteAdeleRing ℚ)) :
    (M.map realCoord).map ofRealHom = M := by
  ext i j
  simp only [Matrix.map_apply, ofRealHom_apply, ofReal_realCoord]

private def invertibleSet : Set (Fin 3 → Fin 3 → ℝ) := {e | (Matrix.of e).det ≠ 0}

private theorem isOpen_invertibleSet : IsOpen invertibleSet :=
  isOpen_ne_fun (continuous_id.matrix_det) continuous_const

private theorem isArchSmooth3_iff (φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) :
    IsArchSmooth3 φ ↔ ∀ g, ContDiffOn ℝ (⊤ : ℕ∞) (fun e => φ (g * archRealLift3 e)) invertibleSet :=
  Iff.rfl

private def archMat (e : Fin 3 → Fin 3 → ℝ) : Matrix (Fin 3) (Fin 3) (InfiniteAdeleRing ℚ) :=
  (Matrix.of e).map ofRealHom

private theorem archRealMat3_eq (e : Fin 3 → Fin 3 → ℝ) :
    archRealMat3 e = archMatrixInclN (Fin 3) ℚ (archMat e) := rfl

private def archUnit (e : Fin 3 → Fin 3 → ℝ) (he : e ∈ invertibleSet) : GL (Fin 3) (InfiniteAdeleRing ℚ) :=
  Matrix.GeneralLinearGroup.map ofRealHom (Matrix.GeneralLinearGroup.mkOfDetNeZero (Matrix.of e) he)

private theorem coe_archUnit (e : Fin 3 → Fin 3 → ℝ) (he : e ∈ invertibleSet) :
    (archUnit e he : Matrix (Fin 3) (Fin 3) (InfiniteAdeleRing ℚ)) = archMat e := rfl

private theorem archRealLift3_eq (e : Fin 3 → Fin 3 → ℝ) (he : e ∈ invertibleSet) :
    archRealLift3 e = archInclN (Fin 3) ℚ (archUnit e he) := by
  have hu : IsUnit (archRealMat3 e) := ⟨archInclN (Fin 3) ℚ (archUnit e he), rfl⟩
  rw [archRealLift3, dif_pos hu]
  exact Units.ext hu.unit_spec

private theorem one_mem_invertibleSet : (fun a b : Fin 3 => if a = b then (1 : ℝ) else 0) ∈ invertibleSet := by
  have h : Matrix.of (fun a b : Fin 3 => if a = b then (1 : ℝ) else 0) = 1 := by
    ext a b
    simp [Matrix.one_apply]
  show (Matrix.of fun a b : Fin 3 => if a = b then (1 : ℝ) else 0).det ≠ 0
  rw [h, Matrix.det_one]
  exact one_ne_zero

private theorem archRealLift3_one : archRealLift3 (fun a b : Fin 3 => if a = b then (1 : ℝ) else 0) = 1 := by
  rw [archRealLift3_eq _ one_mem_invertibleSet, ← map_one (archInclN (Fin 3) ℚ)]
  congr 1
  apply Units.ext
  rw [coe_archUnit, Units.val_one, archMat]
  ext a b
  simp only [Matrix.map_apply, Matrix.of_apply, Matrix.one_apply, apply_ite ofRealHom, map_one, map_zero]

private theorem matrix_ext_of_arch_fin {M N : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)}
    (harch : M.map (AdelicLevel.adeleArch (𝓞 ℚ) ℚ) = N.map (AdelicLevel.adeleArch (𝓞 ℚ) ℚ))
    (hfin : M.map (AdelicLevel.adeleFin (𝓞 ℚ) ℚ) = N.map (AdelicLevel.adeleFin (𝓞 ℚ) ℚ)) : M = N := by
  ext i j
  refine Prod.ext ?_ ?_
  · have h := congrFun (congrFun harch i) j
    simp [Matrix.map_apply] at h
    exact h
  · have h := congrFun (congrFun hfin i) j
    simp [Matrix.map_apply] at h
    exact h

private theorem map_adeleArch_archMatrixInclN (X : Matrix (Fin 3) (Fin 3) (InfiniteAdeleRing ℚ)) :
    (archMatrixInclN (Fin 3) ℚ X).map (AdelicLevel.adeleArch (𝓞 ℚ) ℚ) = X := by
  ext i j
  simp [Matrix.map_apply, adeleArch_archMatrixInclN]

private theorem map_adeleFin_archMatrixInclN (X : Matrix (Fin 3) (Fin 3) (InfiniteAdeleRing ℚ)) :
    (archMatrixInclN (Fin 3) ℚ X).map (AdelicLevel.adeleFin (𝓞 ℚ) ℚ) = 1 := by
  ext i j
  simp [Matrix.map_apply, adeleFin_archMatrixInclN, Matrix.one_apply]

private def adArray (k : AdelicGL 3 (𝓞 ℚ) ℚ) (e : Fin 3 → Fin 3 → ℝ) : Fin 3 → Fin 3 → ℝ :=
  fun a b => (realMat (archComponent3 (𝓞 ℚ) ℚ k)⁻¹ * Matrix.of e * realMat (archComponent3 (𝓞 ℚ) ℚ k)) a b

private theorem of_adArray (k : AdelicGL 3 (𝓞 ℚ) ℚ) (e : Fin 3 → Fin 3 → ℝ) :
    Matrix.of (adArray k e) =
      realMat (archComponent3 (𝓞 ℚ) ℚ k)⁻¹ * Matrix.of e * realMat (archComponent3 (𝓞 ℚ) ℚ k) := rfl

private theorem det_realMat_ne_zero (h : GL (Fin 3) (InfiniteAdeleRing ℚ)) : (realMat h).det ≠ 0 := by
  have hu : IsUnit (realMat h) := ⟨realGL h, rfl⟩
  exact ((Matrix.isUnit_iff_isUnit_det _).1 hu).ne_zero

private theorem adArray_mem_invertibleSet (k : AdelicGL 3 (𝓞 ℚ) ℚ) {e : Fin 3 → Fin 3 → ℝ}
    (he : e ∈ invertibleSet) :
    adArray k e ∈ invertibleSet := by
  show (Matrix.of (adArray k e)).det ≠ 0
  rw [of_adArray, Matrix.det_mul, Matrix.det_mul]
  exact mul_ne_zero (mul_ne_zero (det_realMat_ne_zero _) he) (det_realMat_ne_zero _)

private theorem archMat_adArray (k : AdelicGL 3 (𝓞 ℚ) ℚ) (e : Fin 3 → Fin 3 → ℝ) :
    archMat (adArray k e) =
      ((archComponent3 (𝓞 ℚ) ℚ k)⁻¹ : GL (Fin 3) (InfiniteAdeleRing ℚ)).val * archMat e *
        (archComponent3 (𝓞 ℚ) ℚ k).val := by
  rw [archMat, of_adArray, Matrix.map_mul, Matrix.map_mul, realMat_eq, realMat_eq, map_realCoord_map_ofRealHom,
    map_realCoord_map_ofRealHom]
  rfl

private theorem map_adeleArch_val (k : AdelicGL 3 (𝓞 ℚ) ℚ) :
    (k : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)).map (AdelicLevel.adeleArch (𝓞 ℚ) ℚ) =
      (archComponent3 (𝓞 ℚ) ℚ k).val := rfl

private theorem map_adeleArch_val_inv (k : AdelicGL 3 (𝓞 ℚ) ℚ) :
    (k⁻¹ : AdelicGL 3 (𝓞 ℚ) ℚ).val.map (AdelicLevel.adeleArch (𝓞 ℚ) ℚ) =
      ((archComponent3 (𝓞 ℚ) ℚ k)⁻¹ : GL (Fin 3) (InfiniteAdeleRing ℚ)).val := by
  rw [← map_inv (archComponent3 (𝓞 ℚ) ℚ)]
  rfl

private theorem map_adeleFin_inv_mul (k : AdelicGL 3 (𝓞 ℚ) ℚ) :
    (k⁻¹ : AdelicGL 3 (𝓞 ℚ) ℚ).val.map (AdelicLevel.adeleFin (𝓞 ℚ) ℚ) *
        (k : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)).map (AdelicLevel.adeleFin (𝓞 ℚ) ℚ) = 1 := by
  rw [← Matrix.map_mul, Units.inv_mul, Matrix.map_one (AdelicLevel.adeleFin (𝓞 ℚ) ℚ) (map_zero _) (map_one _)]

private theorem inv_mul_archRealLift3_mul (k : AdelicGL 3 (𝓞 ℚ) ℚ) {e : Fin 3 → Fin 3 → ℝ}
    (he : e ∈ invertibleSet) :
    k⁻¹ * archRealLift3 e * k = archRealLift3 (adArray k e) := by
  rw [archRealLift3_eq _ he, archRealLift3_eq _ (adArray_mem_invertibleSet k he)]
  apply Units.ext
  rw [Units.val_mul, Units.val_mul]
  apply matrix_ext_of_arch_fin
  · rw [Matrix.map_mul, Matrix.map_mul]
    change _ * (archMatrixInclN (Fin 3) ℚ (archMat e)).map _ * _ =
      (archMatrixInclN (Fin 3) ℚ (archMat (adArray k e))).map _
    rw [map_adeleArch_archMatrixInclN, map_adeleArch_archMatrixInclN, archMat_adArray, map_adeleArch_val_inv,
      map_adeleArch_val]
  · rw [Matrix.map_mul, Matrix.map_mul]
    change _ * (archMatrixInclN (Fin 3) ℚ (archMat e)).map _ * _ =
      (archMatrixInclN (Fin 3) ℚ (archMat (adArray k e))).map _
    rw [map_adeleFin_archMatrixInclN, map_adeleFin_archMatrixInclN, Matrix.mul_one, map_adeleFin_inv_mul]

private theorem archRealLift3_mul_eq_mul_archRealLift3 (k : AdelicGL 3 (𝓞 ℚ) ℚ) {e : Fin 3 → Fin 3 → ℝ}
    (he : e ∈ invertibleSet) : archRealLift3 e * k = k * archRealLift3 (adArray k e) := by
  rw [← inv_mul_archRealLift3_mul k he, mul_assoc, ← mul_assoc k k⁻¹, mul_inv_cancel, one_mul]

private def adArrayL (k : AdelicGL 3 (𝓞 ℚ) ℚ) : (Fin 3 → Fin 3 → ℝ) →L[ℝ] (Fin 3 → Fin 3 → ℝ) :=
  LinearMap.toContinuousLinearMap
    { toFun := adArray k
      map_add' := fun e e' => by
        funext a b
        simp only [adArray, Pi.add_apply]
        rw [show Matrix.of (e + e') = Matrix.of e + Matrix.of e' from rfl, Matrix.mul_add, Matrix.add_mul,
          Matrix.add_apply]
      map_smul' := fun c e => by
        funext a b
        simp only [adArray, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
        rw [show Matrix.of (c • e) = c • Matrix.of e from rfl, Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_apply,
          smul_eq_mul] }

@[scoped simp] private theorem adArrayL_apply (k : AdelicGL 3 (𝓞 ℚ) ℚ)
    (e : Fin 3 → Fin 3 → ℝ) : adArrayL k e = adArray k e := rfl

private theorem isArchSmooth3_mul_right {u : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ} (hu : IsArchSmooth3 u)
    (k : AdelicGL 3 (𝓞 ℚ) ℚ) :
    IsArchSmooth3 (fun g => u (g * k)) := by
  intro g
  have hmaps : Set.MapsTo (adArrayL k) invertibleSet invertibleSet := fun e he => adArray_mem_invertibleSet k he
  refine ((hu (g * k)).comp ((adArrayL k).contDiff.contDiffOn) hmaps).congr ?_
  intro e he
  simp only [Function.comp, adArrayL_apply]
  rw [mul_assoc, archRealLift3_mul_eq_mul_archRealLift3 k he, ← mul_assoc]

private def oneArray : Fin 3 → Fin 3 → ℝ := fun a b => if a = b then (1 : ℝ) else 0

private def elemArray (i j : Fin 3) : Fin 3 → Fin 3 → ℝ := fun a b => if a = i ∧ b = j then (1 : ℝ) else 0

private theorem oneArray_mem_invertibleSet : oneArray ∈ invertibleSet := one_mem_invertibleSet

private theorem archRealLift3_oneArray : archRealLift3 oneArray = 1 := archRealLift3_one

private theorem archDeriv_apply_eq_fderiv_oneArray {u : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ} (hu : IsArchSmooth3 u)
    (i j : Fin 3)
    (g : AdelicGL 3 (𝓞 ℚ) ℚ) :
    archDeriv i j u g = fderiv ℝ (fun e => u (g * archRealLift3 e)) oneArray (elemArray i j) := by
  have h := archDeriv_eq_fderiv hu i j g (e := oneArray) oneArray_mem_invertibleSet
  rw [archRealLift3_oneArray, mul_one] at h
  rw [h]
  congr 1
  funext a b
  simp only [oneArray, elemArray]
  by_cases hb : b = j <;> by_cases ha : a = i <;> simp [ha, hb]

end LanglandsTunnell.CubicInduction.ArchCalculus
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_norm_whittaker3_archRealLift3_diag_mul_le_of_isCompact.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_norm_whittaker3_archRealLift3_diag_mul_le_of_isCompact.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_norm_whittaker3_archRealLift3_diag_mul_le_of_isCompact.LanglandsTunnell.CubicInduction.ArchCalculus"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_norm_whittaker3_archRealLift3_diag_mul_le_of_isCompact.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_norm_whittaker3_archRealLift3_diag_mul_le_of_isCompact.LanglandsTunnell.CubicInduction"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_norm_whittaker3_archRealLift3_diag_mul_le_of_isCompact.LanglandsTunnell"

set_option autoImplicit false

open IsDedekindDomain NumberField

noncomputable section

namespace LanglandsTunnell
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "WhittakerBlock.archDeriv AdelicGL upperUnipotent3 localMaximalCompact3 mem_localMaximalCompact3_iff componentAtN componentAt3 archComponent3 whittaker3 archPlaceComponent3 matrixSize matrixSize_nonneg matrixSupSize archGauge3 finGauge3 gauge3 one_le_gauge3 one_le_archGauge3 WhittakerBlock.archRealLift3_mul WhittakerBlock.archDeriv_eq_fderiv"
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

section SizeArch

variable {L : Type*} [NormedField L]

private theorem norm_entry_le_matrixSize (k : GL (Fin 3) L) (i j : Fin 3) :
    ‖(k : Matrix (Fin 3) (Fin 3) L) i j‖ ≤ matrixSize k := by
  have hrow : ‖(k : Matrix (Fin 3) (Fin 3) L) i j‖ + ‖((k⁻¹ : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L) i j‖ ≤
      ∑ j' : Fin 3,
        (‖(k : Matrix (Fin 3) (Fin 3) L) i j'‖ + ‖((k⁻¹ : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L) i j'‖) :=
    Finset.single_le_sum
      (f := fun j' => ‖(k : Matrix (Fin 3) (Fin 3) L) i j'‖ +
        ‖((k⁻¹ : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L) i j'‖)
      (fun _ _ => add_nonneg (norm_nonneg _) (norm_nonneg _)) (Finset.mem_univ j)
  have hall : (∑ j' : Fin 3,
      (‖(k : Matrix (Fin 3) (Fin 3) L) i j'‖ + ‖((k⁻¹ : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L) i j'‖)) ≤
      matrixSize k :=
    Finset.single_le_sum
      (f := fun i' => ∑ j' : Fin 3,
        (‖(k : Matrix (Fin 3) (Fin 3) L) i' j'‖ + ‖((k⁻¹ : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L) i' j'‖))
      (fun _ _ => Finset.sum_nonneg fun _ _ => add_nonneg (norm_nonneg _) (norm_nonneg _)) (Finset.mem_univ i)
  have hinv : 0 ≤ ‖((k⁻¹ : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L) i j‖ := norm_nonneg _
  linarith

private theorem norm_inv_entry_le_matrixSize (k : GL (Fin 3) L) (i j : Fin 3) :
    ‖((k⁻¹ : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L) i j‖ ≤ matrixSize k := by
  have hrow : ‖(k : Matrix (Fin 3) (Fin 3) L) i j‖ + ‖((k⁻¹ : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L) i j‖ ≤
      ∑ j' : Fin 3,
        (‖(k : Matrix (Fin 3) (Fin 3) L) i j'‖ + ‖((k⁻¹ : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L) i j'‖) :=
    Finset.single_le_sum
      (f := fun j' => ‖(k : Matrix (Fin 3) (Fin 3) L) i j'‖ +
        ‖((k⁻¹ : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L) i j'‖)
      (fun _ _ => add_nonneg (norm_nonneg _) (norm_nonneg _)) (Finset.mem_univ j)
  have hall : (∑ j' : Fin 3,
      (‖(k : Matrix (Fin 3) (Fin 3) L) i j'‖ + ‖((k⁻¹ : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L) i j'‖)) ≤
      matrixSize k :=
    Finset.single_le_sum
      (f := fun i' => ∑ j' : Fin 3,
        (‖(k : Matrix (Fin 3) (Fin 3) L) i' j'‖ + ‖((k⁻¹ : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L) i' j'‖))
      (fun _ _ => Finset.sum_nonneg fun _ _ => add_nonneg (norm_nonneg _) (norm_nonneg _)) (Finset.mem_univ i)
  have hent : 0 ≤ ‖(k : Matrix (Fin 3) (Fin 3) L) i j‖ := norm_nonneg _
  linarith

private theorem norm_mul_entry_le {A B : Matrix (Fin 3) (Fin 3) L} {a b : ℝ} (ha : 0 ≤ a)
    (hA : ∀ i j, ‖A i j‖ ≤ a) (hB : ∀ i j, ‖B i j‖ ≤ b) (i j : Fin 3) : ‖(A * B) i j‖ ≤ 3 * (a * b) := by
  rw [Matrix.mul_apply]
  calc ‖∑ m : Fin 3, A i m * B m j‖ ≤ ∑ m : Fin 3, ‖A i m * B m j‖ := norm_sum_le _ _
    _ ≤ ∑ _m : Fin 3, a * b := by
        refine Finset.sum_le_sum fun m _ => ?_
        rw [norm_mul]
        exact mul_le_mul (hA i m) (hB m j) (norm_nonneg _) ha
    _ = 3 * (a * b) := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_ofNat]

private theorem matrixSize_mul_le (k l : GL (Fin 3) L) :
    matrixSize (k * l) ≤ 54 * (matrixSize k * matrixSize l) := by
  have hk : 0 ≤ matrixSize k := matrixSize_nonneg k
  have hl : 0 ≤ matrixSize l := matrixSize_nonneg l
  have hprod : ((k * l : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L) =
      (k : Matrix (Fin 3) (Fin 3) L) * (l : Matrix (Fin 3) (Fin 3) L) := rfl
  have hprodinv : (((k * l)⁻¹ : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L) =
      ((l⁻¹ : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L) * ((k⁻¹ : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L) := rfl
  have hentry : ∀ i j : Fin 3,
      ‖((k * l : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L) i j‖ ≤ 3 * (matrixSize k * matrixSize l) := by
    intro i j
    rw [hprod]
    exact norm_mul_entry_le hk (norm_entry_le_matrixSize k) (norm_entry_le_matrixSize l) i j
  have hinventry : ∀ i j : Fin 3,
      ‖(((k * l)⁻¹ : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L) i j‖ ≤ 3 * (matrixSize l * matrixSize k) := by
    intro i j
    rw [hprodinv]
    exact norm_mul_entry_le hl (norm_inv_entry_le_matrixSize l) (norm_inv_entry_le_matrixSize k) i j
  have hterm : ∀ i j : Fin 3,
      ‖((k * l : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L) i j‖ +
        ‖(((k * l)⁻¹ : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L) i j‖ ≤ 6 * (matrixSize k * matrixSize l) := by
    intro i j
    have h1 := hentry i j
    have h2 := hinventry i j
    rw [mul_comm (matrixSize l) (matrixSize k)] at h2
    linarith
  calc matrixSize (k * l)
      = ∑ i : Fin 3, ∑ j : Fin 3,
          (‖((k * l : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L) i j‖ +
            ‖(((k * l)⁻¹ : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L) i j‖) := rfl
    _ ≤ ∑ _i : Fin 3, ∑ _j : Fin 3, 6 * (matrixSize k * matrixSize l) :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hterm i j
    _ = 54 * (matrixSize k * matrixSize l) := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_ofNat]
        ring

private theorem continuous_matrixSize : Continuous (matrixSize (L := L)) := by
  unfold matrixSize
  refine continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ => ?_
  exact ((Units.continuous_val.matrix_elem i j).norm).add ((Units.continuous_coe_inv.matrix_elem i j).norm)

end SizeArch
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_norm_whittaker3_archRealLift3_diag_mul_le_of_isCompact.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_norm_whittaker3_archRealLift3_diag_mul_le_of_isCompact.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_norm_whittaker3_archRealLift3_diag_mul_le_of_isCompact.LanglandsTunnell.CubicInduction.ArchCalculus"

section SizeFinite

variable {L : Type*} [NormedField L] [IsUltrametricDist L]

omit [IsUltrametricDist L] in
private theorem nnnorm_entry_le_matrixSupSize (k : GL (Fin 3) L) (i j : Fin 3) :
    ‖(k : Matrix (Fin 3) (Fin 3) L) i j‖₊ ≤ matrixSupSize k :=
  (le_max_left _ _).trans (Finset.le_sup (f := fun ij : Fin 3 × Fin 3 =>
    max ‖(k : Matrix (Fin 3) (Fin 3) L) ij.1 ij.2‖₊ ‖((k⁻¹ : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L) ij.1 ij.2‖₊)
    (Finset.mem_univ (i, j)))

omit [IsUltrametricDist L] in
private theorem nnnorm_inv_entry_le_matrixSupSize (k : GL (Fin 3) L) (i j : Fin 3) :
    ‖((k⁻¹ : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L) i j‖₊ ≤ matrixSupSize k :=
  (le_max_right _ _).trans (Finset.le_sup (f := fun ij : Fin 3 × Fin 3 =>
    max ‖(k : Matrix (Fin 3) (Fin 3) L) ij.1 ij.2‖₊ ‖((k⁻¹ : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L) ij.1 ij.2‖₊)
    (Finset.mem_univ (i, j)))

private theorem nnnorm_mul_entry_le {A B : Matrix (Fin 3) (Fin 3) L} {a b : NNReal}
    (hA : ∀ i j, ‖A i j‖₊ ≤ a) (hB : ∀ i j, ‖B i j‖₊ ≤ b) (i j : Fin 3) : ‖(A * B) i j‖₊ ≤ a * b := by
  rw [Matrix.mul_apply]
  refine IsUltrametricDist.nnnorm_sum_le_of_forall_le fun m _ => ?_
  calc ‖A i m * B m j‖₊ ≤ ‖A i m‖₊ * ‖B m j‖₊ := nnnorm_mul_le _ _
    _ ≤ a * b := mul_le_mul' (hA i m) (hB m j)

private theorem matrixSupSize_mul_le (g k : GL (Fin 3) L) :
    matrixSupSize (g * k) ≤ matrixSupSize g * matrixSupSize k := by
  change Finset.univ.sup (fun ij : Fin 3 × Fin 3 =>
    max ‖((g * k : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L) ij.1 ij.2‖₊
      ‖(((g * k)⁻¹ : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L) ij.1 ij.2‖₊) ≤ matrixSupSize g * matrixSupSize k
  refine Finset.sup_le fun ij _ => max_le ?_ ?_
  · have h : ((g * k : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L) =
        (g : Matrix (Fin 3) (Fin 3) L) * (k : Matrix (Fin 3) (Fin 3) L) := rfl
    rw [h]
    exact nnnorm_mul_entry_le (nnnorm_entry_le_matrixSupSize g) (nnnorm_entry_le_matrixSupSize k) ij.1 ij.2
  · have h : (((g * k)⁻¹ : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L) =
        ((k⁻¹ : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L) * ((g⁻¹ : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L) := rfl
    rw [h, mul_comm (matrixSupSize g)]
    exact nnnorm_mul_entry_le (nnnorm_inv_entry_le_matrixSupSize k) (nnnorm_inv_entry_le_matrixSupSize g) ij.1 ij.2

private theorem matrixSupSize_mul_le_of_forall_nnnorm_le_one (g k : GL (Fin 3) L)
    (hk : ∀ i j, ‖(k : Matrix (Fin 3) (Fin 3) L) i j‖₊ ≤ 1)
    (hk' : ∀ i j, ‖((k⁻¹ : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L) i j‖₊ ≤ 1) :
    matrixSupSize (g * k) ≤ matrixSupSize g := by
  change Finset.univ.sup (fun ij : Fin 3 × Fin 3 =>
    max ‖((g * k : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L) ij.1 ij.2‖₊
      ‖(((g * k)⁻¹ : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L) ij.1 ij.2‖₊) ≤ matrixSupSize g
  refine Finset.sup_le fun ij _ => max_le ?_ ?_
  · have h : ((g * k : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L) =
        (g : Matrix (Fin 3) (Fin 3) L) * (k : Matrix (Fin 3) (Fin 3) L) := rfl
    rw [h]
    simpa using nnnorm_mul_entry_le (nnnorm_entry_le_matrixSupSize g) hk ij.1 ij.2
  · have h : (((g * k)⁻¹ : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L) =
        ((k⁻¹ : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L) * ((g⁻¹ : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L) := rfl
    rw [h]
    simpa using nnnorm_mul_entry_le hk' (nnnorm_inv_entry_le_matrixSupSize g) ij.1 ij.2

private theorem matrixSupSize_one_mul_le_of_forall_nnnorm_le_one (k g : GL (Fin 3) L)
    (hk : ∀ i j, ‖(k : Matrix (Fin 3) (Fin 3) L) i j‖₊ ≤ 1)
    (hk' : ∀ i j, ‖((k⁻¹ : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L) i j‖₊ ≤ 1) :
    matrixSupSize (k * g) ≤ matrixSupSize g := by
  change Finset.univ.sup (fun ij : Fin 3 × Fin 3 =>
    max ‖((k * g : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L) ij.1 ij.2‖₊
      ‖(((k * g)⁻¹ : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L) ij.1 ij.2‖₊) ≤ matrixSupSize g
  refine Finset.sup_le fun ij _ => max_le ?_ ?_
  · have h : ((k * g : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L) =
        (k : Matrix (Fin 3) (Fin 3) L) * (g : Matrix (Fin 3) (Fin 3) L) := rfl
    rw [h]
    simpa using nnnorm_mul_entry_le hk (nnnorm_entry_le_matrixSupSize g) ij.1 ij.2
  · have h : (((k * g)⁻¹ : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L) =
        ((g⁻¹ : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L) * ((k⁻¹ : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L) := rfl
    rw [h]
    simpa using nnnorm_mul_entry_le (nnnorm_inv_entry_le_matrixSupSize g) hk' ij.1 ij.2

private theorem matrixSupSize_mul_of_forall_nnnorm_le_one (g k : GL (Fin 3) L)
    (hk : ∀ i j, ‖(k : Matrix (Fin 3) (Fin 3) L) i j‖₊ ≤ 1)
    (hk' : ∀ i j, ‖((k⁻¹ : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L) i j‖₊ ≤ 1) :
    matrixSupSize (g * k) = matrixSupSize g := by
  refine le_antisymm (matrixSupSize_mul_le_of_forall_nnnorm_le_one g k hk hk') ?_
  have h := matrixSupSize_mul_le_of_forall_nnnorm_le_one (g * k) k⁻¹ (by simpa using hk') (by simpa using hk)
  simpa using h

private theorem matrixSupSize_one_mul_of_forall_nnnorm_le_one (k g : GL (Fin 3) L)
    (hk : ∀ i j, ‖(k : Matrix (Fin 3) (Fin 3) L) i j‖₊ ≤ 1)
    (hk' : ∀ i j, ‖((k⁻¹ : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L) i j‖₊ ≤ 1) :
    matrixSupSize (k * g) = matrixSupSize g := by
  refine le_antisymm (matrixSupSize_one_mul_le_of_forall_nnnorm_le_one k g hk hk') ?_
  have h := matrixSupSize_one_mul_le_of_forall_nnnorm_le_one k⁻¹ (k * g) (by simpa using hk') (by simpa using hk)
  simpa using h

end SizeFinite
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_norm_whittaker3_archRealLift3_diag_mul_le_of_isCompact.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_norm_whittaker3_archRealLift3_diag_mul_le_of_isCompact.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_norm_whittaker3_archRealLift3_diag_mul_le_of_isCompact.LanglandsTunnell.CubicInduction.ArchCalculus"

section ArchGauge

private def archTranslateConst (h : AdelicGL 3 (𝓞 ℚ) ℚ) : ℝ :=
  1 + 54 * ∑ w : InfinitePlace ℚ, matrixSize (archPlaceComponent3 ℚ w h)

private theorem one_le_archTranslateConst (h : AdelicGL 3 (𝓞 ℚ) ℚ) : 1 ≤ archTranslateConst h := by
  unfold archTranslateConst
  have hsum : 0 ≤ ∑ w : InfinitePlace ℚ, matrixSize (archPlaceComponent3 ℚ w h) :=
    Finset.sum_nonneg fun w _ => matrixSize_nonneg _
  linarith

private theorem archGauge3_mul_le (g h : AdelicGL 3 (𝓞 ℚ) ℚ) :
    archGauge3 ℚ (g * h) ≤ archTranslateConst h * archGauge3 ℚ g := by
  set M : ℝ := ∑ w : InfinitePlace ℚ, matrixSize (archPlaceComponent3 ℚ w h) with hM
  have hM0 : 0 ≤ M := Finset.sum_nonneg fun w _ => matrixSize_nonneg _
  have hX0 : 0 ≤ ∑ w : InfinitePlace ℚ, matrixSize (archPlaceComponent3 ℚ w g) :=
    Finset.sum_nonneg fun w _ => matrixSize_nonneg _
  have hterm : ∀ w : InfinitePlace ℚ, matrixSize (archPlaceComponent3 ℚ w (g * h)) ≤
      54 * M * matrixSize (archPlaceComponent3 ℚ w g) := by
    intro w
    rw [map_mul]
    have h1 := matrixSize_mul_le (archPlaceComponent3 ℚ w g) (archPlaceComponent3 ℚ w h)
    have h2 : matrixSize (archPlaceComponent3 ℚ w h) ≤ M :=
      Finset.single_le_sum (f := fun w' => matrixSize (archPlaceComponent3 ℚ w' h))
        (fun _ _ => matrixSize_nonneg _) (Finset.mem_univ w)
    have h3 : 0 ≤ matrixSize (archPlaceComponent3 ℚ w g) := matrixSize_nonneg _
    nlinarith [mul_le_mul_of_nonneg_left h2 h3]
  have hsum : ∑ w : InfinitePlace ℚ, matrixSize (archPlaceComponent3 ℚ w (g * h)) ≤
      54 * M * ∑ w : InfinitePlace ℚ, matrixSize (archPlaceComponent3 ℚ w g) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun w _ => hterm w
  unfold archGauge3 archTranslateConst
  rw [← hM]
  nlinarith [hsum, hM0, hX0, mul_nonneg hM0 hX0]

private theorem continuous_glMap3 {A B : Type*} [CommRing A] [CommRing B] [TopologicalSpace A]
    [TopologicalSpace B] [IsTopologicalRing A] [IsTopologicalRing B] (f : A →+* B) (hf : Continuous f) :
    Continuous (Matrix.GeneralLinearGroup.map (n := Fin 3) f) :=
  Continuous.units_map _ ((continuous_id.matrix_map hf) : Continuous fun m : Matrix (Fin 3) (Fin 3) A => m.map f)

private theorem continuous_archPlaceComponent3 (w : InfinitePlace ℚ) :
    Continuous (archPlaceComponent3 ℚ w) :=
  (continuous_glMap3 _ (AdelicLevel.continuous_archEval ℚ w)).comp
    (continuous_glMap3 _ (AdelicLevel.continuous_adeleArch (𝓞 ℚ) ℚ))

private theorem continuous_componentAt3 (v : HeightOneSpectrum (𝓞 ℚ)) :
    Continuous (componentAt3 (𝓞 ℚ) ℚ v) :=
  continuous_glMap3 _ ((AdelicLevel.continuous_finAdeleEval (𝓞 ℚ) ℚ v).comp (AdelicLevel.continuous_adeleFin (𝓞 ℚ) ℚ))

private theorem continuous_archTranslateConst : Continuous archTranslateConst := by
  unfold archTranslateConst
  refine continuous_const.add (continuous_const.mul (continuous_finsetSum _ fun w _ => ?_))
  exact continuous_matrixSize.comp (continuous_archPlaceComponent3 w)

private theorem continuous_archGauge3 : Continuous (archGauge3 ℚ) := by
  unfold archGauge3
  refine continuous_const.add (continuous_finsetSum _ fun w _ => ?_)
  exact continuous_matrixSize.comp (continuous_archPlaceComponent3 w)

private theorem exists_forall_archTranslateConst_le_of_isCompact {K : Set (AdelicGL 3 (𝓞 ℚ) ℚ)}
    (hK : IsCompact K) : ∃ c : ℝ, ∀ k ∈ K, archTranslateConst k ≤ c := by
  obtain ⟨c, hc⟩ := (hK.image continuous_archTranslateConst).isBounded.bddAbove
  exact ⟨c, fun k hk => hc ⟨k, hk, rfl⟩⟩

private theorem exists_forall_archGauge3_le_of_isCompact {K : Set (AdelicGL 3 (𝓞 ℚ) ℚ)}
    (hK : IsCompact K) : ∃ c : ℝ, ∀ k ∈ K, archGauge3 ℚ k ≤ c := by
  obtain ⟨c, hc⟩ := (hK.image continuous_archGauge3).isBounded.bddAbove
  exact ⟨c, fun k hk => hc ⟨k, hk, rfl⟩⟩

end ArchGauge
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_norm_whittaker3_archRealLift3_diag_mul_le_of_isCompact.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_norm_whittaker3_archRealLift3_diag_mul_le_of_isCompact.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_norm_whittaker3_archRealLift3_diag_mul_le_of_isCompact.LanglandsTunnell.CubicInduction.ArchCalculus"

end LanglandsTunnell.CubicInduction
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_norm_whittaker3_archRealLift3_diag_mul_le_of_isCompact.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_norm_whittaker3_archRealLift3_diag_mul_le_of_isCompact.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_norm_whittaker3_archRealLift3_diag_mul_le_of_isCompact.LanglandsTunnell.CubicInduction.ArchCalculus"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_norm_whittaker3_archRealLift3_diag_mul_le_of_isCompact.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_norm_whittaker3_archRealLift3_diag_mul_le_of_isCompact.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_norm_whittaker3_archRealLift3_diag_mul_le_of_isCompact.LanglandsTunnell.CubicInduction.ArchCalculus"

namespace LanglandsTunnell
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "WhittakerBlock.archDeriv AdelicGL upperUnipotent3 localMaximalCompact3 mem_localMaximalCompact3_iff componentAtN componentAt3 archComponent3 whittaker3 archPlaceComponent3 matrixSize matrixSize_nonneg matrixSupSize archGauge3 finGauge3 gauge3 one_le_gauge3 one_le_archGauge3 WhittakerBlock.archRealLift3_mul WhittakerBlock.archDeriv_eq_fderiv"
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

open NumberField

section FiniteComponents

variable (v : HeightOneSpectrum (𝓞 ℚ))

private theorem componentAt3_apply (g : AdelicGL 3 (𝓞 ℚ) ℚ) (i j : Fin 3) :
    ((componentAt3 (𝓞 ℚ) ℚ v g : GL (Fin 3) (v.adicCompletion ℚ)) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j =
      ((g : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) i j).2 v :=
  rfl

private theorem componentAt3_inv_apply (g : AdelicGL 3 (𝓞 ℚ) ℚ) (i j : Fin 3) :
    (((componentAt3 (𝓞 ℚ) ℚ v g)⁻¹ : GL (Fin 3) (v.adicCompletion ℚ)) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ))
        i j =
      (((g⁻¹ : AdelicGL 3 (𝓞 ℚ) ℚ) : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) i j).2 v := by
  rw [← map_inv]
  rfl

private theorem nnnorm_entry_le_one_of_mem_localMaximalCompact3 {k : GL (Fin 3) (v.adicCompletion ℚ)}
    (hk : k ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v) (i j : Fin 3) :
    ‖(k : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j‖₊ ≤ 1 := by
  rw [← NNReal.coe_le_coe, coe_nnnorm, NNReal.coe_one]
  exact Valued.toNormedField.norm_le_one_iff.mpr (((mem_localMaximalCompact3_iff (𝓞 ℚ) ℚ v).mp hk).1 i j)

private theorem nnnorm_inv_entry_le_one_of_mem_localMaximalCompact3 {k : GL (Fin 3) (v.adicCompletion ℚ)}
    (hk : k ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v) (i j : Fin 3) :
    ‖((k⁻¹ : GL (Fin 3) (v.adicCompletion ℚ)) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j‖₊ ≤ 1 := by
  rw [← NNReal.coe_le_coe, coe_nnnorm, NNReal.coe_one]
  exact Valued.toNormedField.norm_le_one_iff.mpr (((mem_localMaximalCompact3_iff (𝓞 ℚ) ℚ v).mp hk).2 i j)

private theorem matrixSupSize_mul_of_mem
    (g : GL (Fin 3) (v.adicCompletion ℚ)) {k : GL (Fin 3) (v.adicCompletion ℚ)}
    (hk : k ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v) : matrixSupSize (g * k) = matrixSupSize g :=
  matrixSupSize_mul_of_forall_nnnorm_le_one g k (nnnorm_entry_le_one_of_mem_localMaximalCompact3 v hk)
    (nnnorm_inv_entry_le_one_of_mem_localMaximalCompact3 v hk)

private theorem matrixSupSize_mem_mul
    {k : GL (Fin 3) (v.adicCompletion ℚ)} (hk : k ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v)
    (g : GL (Fin 3) (v.adicCompletion ℚ)) : matrixSupSize (k * g) = matrixSupSize g :=
  matrixSupSize_one_mul_of_forall_nnnorm_le_one k g (nnnorm_entry_le_one_of_mem_localMaximalCompact3 v hk)
    (nnnorm_inv_entry_le_one_of_mem_localMaximalCompact3 v hk)

end FiniteComponents
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_norm_whittaker3_archRealLift3_diag_mul_le_of_isCompact.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_norm_whittaker3_archRealLift3_diag_mul_le_of_isCompact.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_norm_whittaker3_archRealLift3_diag_mul_le_of_isCompact.LanglandsTunnell.CubicInduction.ArchCalculus"

section FiniteGauge

private theorem finGauge3_mul_of_forall_mem {n : AdelicGL 3 (𝓞 ℚ) ℚ}
    (hn : ∀ v : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ v n ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v)
    (g : AdelicGL 3 (𝓞 ℚ) ℚ) : finGauge3 ℚ (n * g) = finGauge3 ℚ g := by
  unfold finGauge3
  refine finprod_congr fun v => ?_
  rw [map_mul, matrixSupSize_mem_mul v (hn v)]

private theorem finGauge3_mul_of_forall_mem' (g : AdelicGL 3 (𝓞 ℚ) ℚ) {u : AdelicGL 3 (𝓞 ℚ) ℚ}
    (hu : ∀ v : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ v u ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v) :
    finGauge3 ℚ (g * u) = finGauge3 ℚ g := by
  unfold finGauge3
  refine finprod_congr fun v => ?_
  rw [map_mul, matrixSupSize_mul_of_mem v _ (hu v)]

private theorem finGauge3_archInclN_mul (h : GL (Fin 3) (InfiniteAdeleRing ℚ)) (g : AdelicGL 3 (𝓞 ℚ) ℚ) :
    finGauge3 ℚ (AutomorphicForm.archInclN (Fin 3) ℚ h * g) = finGauge3 ℚ g :=
  finGauge3_mul_of_forall_mem (fun v => by
    show componentAtN (Fin 3) (𝓞 ℚ) ℚ v (AutomorphicForm.archInclN (Fin 3) ℚ h) ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v
    rw [AutomorphicForm.componentAtN_archInclN]
    exact one_mem _) g

private theorem finGauge3_nonneg (g : AdelicGL 3 (𝓞 ℚ) ℚ) : 0 ≤ finGauge3 ℚ g :=
  finprod_nonneg fun _ => NNReal.coe_nonneg _

private def integralSet : Set (AdelicGL 3 (𝓞 ℚ) ℚ) :=
  {k | (∀ i j, ((k : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) i j).2 ∈ AdelicBox.integralFiniteAdeles (𝓞 ℚ) ℚ) ∧
    ∀ i j, (((k⁻¹ : AdelicGL 3 (𝓞 ℚ) ℚ) : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) i j).2 ∈
      AdelicBox.integralFiniteAdeles (𝓞 ℚ) ℚ}

private theorem one_mem_integralSet : (1 : AdelicGL 3 (𝓞 ℚ) ℚ) ∈ integralSet := by
  have h1 : ∀ i j : Fin 3, (((1 : AdelicGL 3 (𝓞 ℚ) ℚ) : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) i j).2 ∈
      AdelicBox.integralFiniteAdeles (𝓞 ℚ) ℚ := by
    intro i j v
    by_cases hij : i = j
    · subst hij
      simp only [Units.val_one, Matrix.one_apply_eq]
      exact (1 : v.adicCompletionIntegers ℚ).2
    · simp only [Units.val_one, Matrix.one_apply_ne hij]
      exact (0 : v.adicCompletionIntegers ℚ).2
  exact ⟨h1, by simpa using h1⟩

private theorem isOpen_integralSet : IsOpen integralSet := by
  have hI := AdelicBox.isOpen_integralFiniteAdeles ℚ
  have hval : ∀ i j : Fin 3, IsOpen {k : AdelicGL 3 (𝓞 ℚ) ℚ |
      ((k : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) i j).2 ∈ AdelicBox.integralFiniteAdeles (𝓞 ℚ) ℚ} := fun i j =>
    hI.preimage (continuous_snd.comp (Units.continuous_val.matrix_elem i j))
  have hinv : ∀ i j : Fin 3, IsOpen {k : AdelicGL 3 (𝓞 ℚ) ℚ |
      (((k⁻¹ : AdelicGL 3 (𝓞 ℚ) ℚ) : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) i j).2 ∈
        AdelicBox.integralFiniteAdeles (𝓞 ℚ) ℚ} := fun i j =>
    hI.preimage (continuous_snd.comp (Units.continuous_coe_inv.matrix_elem i j))
  have heq : integralSet = (⋂ i, ⋂ j, {k : AdelicGL 3 (𝓞 ℚ) ℚ |
      ((k : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) i j).2 ∈ AdelicBox.integralFiniteAdeles (𝓞 ℚ) ℚ}) ∩
      ⋂ i, ⋂ j, {k : AdelicGL 3 (𝓞 ℚ) ℚ |
        (((k⁻¹ : AdelicGL 3 (𝓞 ℚ) ℚ) : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) i j).2 ∈
          AdelicBox.integralFiniteAdeles (𝓞 ℚ) ℚ} := by
    ext k
    simp only [integralSet, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter]
  rw [heq]
  exact (isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => hval i j).inter
    (isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => hinv i j)

private theorem componentAt3_mem_of_mem_integralSet {u : AdelicGL 3 (𝓞 ℚ) ℚ} (hu : u ∈ integralSet)
    (v : HeightOneSpectrum (𝓞 ℚ)) : componentAt3 (𝓞 ℚ) ℚ v u ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v := by
  rw [mem_localMaximalCompact3_iff]
  refine ⟨fun i j => ?_, fun i j => ?_⟩
  · rw [componentAt3_apply]
    exact (IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 ℚ) ℚ v).1 (hu.1 i j v)
  · rw [componentAt3_inv_apply]
    exact (IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 ℚ) ℚ v).1 (hu.2 i j v)

private theorem exists_forall_finGauge3_le_of_isCompact {K : Set (AdelicGL 3 (𝓞 ℚ) ℚ)} (hK : IsCompact K) :
    ∃ c : ℝ, ∀ k ∈ K, finGauge3 ℚ k ≤ c := by
  set c : AdelicGL 3 (𝓞 ℚ) ℚ → Set (AdelicGL 3 (𝓞 ℚ) ℚ) := fun k => (fun u => k * u) '' integralSet with hc
  have hopen : ∀ k ∈ K, IsOpen (c k) := fun k _ => isOpenMap_mul_left k _ isOpen_integralSet
  have hcover : K ⊆ ⋃ k ∈ K, c k := fun k hk =>
    Set.mem_iUnion₂.2 ⟨k, hk, ⟨1, one_mem_integralSet, mul_one k⟩⟩
  obtain ⟨t, htK, htfin, hKt⟩ := hK.elim_finite_subcover_image hopen hcover
  refine ⟨∑ k ∈ htfin.toFinset, finGauge3 ℚ k, fun k hk => ?_⟩
  obtain ⟨k₀, hk₀t, hkk₀⟩ := Set.mem_iUnion₂.1 (hKt hk)
  obtain ⟨u, hu, rfl⟩ := hkk₀
  rw [finGauge3_mul_of_forall_mem' k₀ (componentAt3_mem_of_mem_integralSet hu)]
  exact Finset.single_le_sum (f := fun k => finGauge3 ℚ k) (fun k _ => finGauge3_nonneg k)
    (htfin.mem_toFinset.2 hk₀t)

end FiniteGauge
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_norm_whittaker3_archRealLift3_diag_mul_le_of_isCompact.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_norm_whittaker3_archRealLift3_diag_mul_le_of_isCompact.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_norm_whittaker3_archRealLift3_diag_mul_le_of_isCompact.LanglandsTunnell.CubicInduction.ArchCalculus"

section TranslateBound

private theorem eventually_componentAt3_mem (k : AdelicGL 3 (𝓞 ℚ) ℚ) :
    ∀ᶠ v : HeightOneSpectrum (𝓞 ℚ) in Filter.cofinite, componentAt3 (𝓞 ℚ) ℚ v k ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v := by
  have hent : ∀ (x : FiniteAdeleRing (𝓞 ℚ) ℚ), ∀ᶠ v : HeightOneSpectrum (𝓞 ℚ) in Filter.cofinite,
      x v ∈ v.adicCompletionIntegers ℚ := fun x => x.2
  have h1 : ∀ᶠ v : HeightOneSpectrum (𝓞 ℚ) in Filter.cofinite, ∀ i j : Fin 3,
      ((k : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) i j).2 v ∈ v.adicCompletionIntegers ℚ :=
    Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j => hent _
  have h2 : ∀ᶠ v : HeightOneSpectrum (𝓞 ℚ) in Filter.cofinite, ∀ i j : Fin 3,
      (((k⁻¹ : AdelicGL 3 (𝓞 ℚ) ℚ) : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) i j).2 v ∈
        v.adicCompletionIntegers ℚ :=
    Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j => hent _
  filter_upwards [h1, h2] with v hv1 hv2
  rw [mem_localMaximalCompact3_iff]
  refine ⟨fun i j => ?_, fun i j => ?_⟩
  · rw [componentAt3_apply]
    exact (IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 ℚ) ℚ v).1 (hv1 i j)
  · rw [componentAt3_inv_apply]
    exact (IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 ℚ) ℚ v).1 (hv2 i j)

private theorem matrixSupSize_one {L : Type*} [NormedField L] : matrixSupSize (1 : GL (Fin 3) L) ≤ 1 := by
  change Finset.univ.sup (fun ij : Fin 3 × Fin 3 =>
    max ‖((1 : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L) ij.1 ij.2‖₊
      ‖((1⁻¹ : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L) ij.1 ij.2‖₊) ≤ 1
  refine Finset.sup_le fun ij _ => ?_
  simp only [inv_one, Units.val_one]
  refine max_le ?_ ?_ <;>
  · by_cases h : ij.1 = ij.2
    · simp [Matrix.one_apply, h]
    · simp [Matrix.one_apply_ne h]

private theorem matrixSupSize_eq_one_of_mem (v : HeightOneSpectrum (𝓞 ℚ)) {k : GL (Fin 3) (v.adicCompletion ℚ)}
    (hk : k ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v) : matrixSupSize k ≤ 1 := by
  have h := matrixSupSize_mem_mul v hk (1 : GL (Fin 3) (v.adicCompletion ℚ))
  rw [mul_one] at h
  rw [h]
  exact matrixSupSize_one

private theorem one_le_matrixSupSize {L : Type*} [NormedField L] [IsUltrametricDist L] (k : GL (Fin 3) L) :
    1 ≤ matrixSupSize k := by
  by_contra hlt
  push Not at hlt
  have hprod : ((k : Matrix (Fin 3) (Fin 3) L) * ((k⁻¹ : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L)) 0 0 = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_apply_eq]
  have hle : ‖((k : Matrix (Fin 3) (Fin 3) L) * ((k⁻¹ : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L)) 0 0‖₊ ≤
      matrixSupSize k * matrixSupSize k :=
    nnnorm_mul_entry_le (nnnorm_entry_le_matrixSupSize k) (nnnorm_inv_entry_le_matrixSupSize k) 0 0
  rw [hprod, nnnorm_one] at hle
  have hsq : matrixSupSize k * matrixSupSize k < 1 := by
    calc matrixSupSize k * matrixSupSize k ≤ 1 * matrixSupSize k := mul_le_mul_of_nonneg_right hlt.le zero_le
      _ = matrixSupSize k := one_mul _
      _ < 1 := hlt
  exact absurd (hle.trans_lt hsq) (lt_irrefl 1)

private theorem finGauge3_eq_prod (k : AdelicGL 3 (𝓞 ℚ) ℚ) {S : Finset (HeightOneSpectrum (𝓞 ℚ))}
    (hS : ∀ v ∉ S, componentAt3 (𝓞 ℚ) ℚ v k ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v) :
    finGauge3 ℚ k = ∏ v ∈ S, ((matrixSupSize (componentAt3 (𝓞 ℚ) ℚ v k) : NNReal) : ℝ) := by
  unfold finGauge3
  refine finprod_eq_prod_of_mulSupport_subset _ fun v hv => ?_
  by_contra hvS
  apply hv
  have h1 : matrixSupSize (componentAt3 (𝓞 ℚ) ℚ v k) = 1 :=
    le_antisymm (matrixSupSize_eq_one_of_mem v (hS v hvS)) (one_le_matrixSupSize _)
  simp [h1]

private theorem finGauge3_mul_le
    (g k : AdelicGL 3 (𝓞 ℚ) ℚ) : finGauge3 ℚ (g * k) ≤ finGauge3 ℚ g * finGauge3 ℚ k := by
  obtain ⟨Sg⟩ : Nonempty {S : Set (HeightOneSpectrum (𝓞 ℚ)) // S.Finite ∧
      ∀ v ∉ S, componentAt3 (𝓞 ℚ) ℚ v g ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v} :=
    ⟨⟨_, Filter.eventually_cofinite.1 (eventually_componentAt3_mem g), fun v hv => by
      by_contra h; exact hv h⟩⟩
  obtain ⟨Sk⟩ : Nonempty {S : Set (HeightOneSpectrum (𝓞 ℚ)) // S.Finite ∧
      ∀ v ∉ S, componentAt3 (𝓞 ℚ) ℚ v k ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v} :=
    ⟨⟨_, Filter.eventually_cofinite.1 (eventually_componentAt3_mem k), fun v hv => by
      by_contra h; exact hv h⟩⟩
  set T : Finset (HeightOneSpectrum (𝓞 ℚ)) := (Sg.2.1.union Sk.2.1).toFinset with hT
  have hmemT : ∀ v, v ∉ T → v ∉ Sg.1 ∧ v ∉ Sk.1 := fun v hv => by
    rw [hT, Set.Finite.mem_toFinset, Set.mem_union] at hv
    exact ⟨fun h => hv (Or.inl h), fun h => hv (Or.inr h)⟩
  have hg : finGauge3 ℚ g = ∏ v ∈ T, ((matrixSupSize (componentAt3 (𝓞 ℚ) ℚ v g) : NNReal) : ℝ) :=
    finGauge3_eq_prod g fun v hv => Sg.2.2 v (hmemT v hv).1
  have hk : finGauge3 ℚ k = ∏ v ∈ T, ((matrixSupSize (componentAt3 (𝓞 ℚ) ℚ v k) : NNReal) : ℝ) :=
    finGauge3_eq_prod k fun v hv => Sk.2.2 v (hmemT v hv).2
  have hgk : finGauge3 ℚ (g * k) = ∏ v ∈ T, ((matrixSupSize (componentAt3 (𝓞 ℚ) ℚ v (g * k)) : NNReal) : ℝ) :=
    finGauge3_eq_prod (g * k) fun v hv => by
      rw [map_mul]
      exact mul_mem (Sg.2.2 v (hmemT v hv).1) (Sk.2.2 v (hmemT v hv).2)
  rw [hg, hk, hgk, ← Finset.prod_mul_distrib]
  refine Finset.prod_le_prod (fun v _ => NNReal.coe_nonneg _) fun v _ => ?_
  rw [map_mul, ← NNReal.coe_mul, NNReal.coe_le_coe]
  exact matrixSupSize_mul_le _ _

private theorem one_le_finGauge3 (k : AdelicGL 3 (𝓞 ℚ) ℚ) : 1 ≤ finGauge3 ℚ k := by
  obtain ⟨S, hSfin, hS⟩ : ∃ S : Set (HeightOneSpectrum (𝓞 ℚ)), S.Finite ∧
      ∀ v ∉ S, componentAt3 (𝓞 ℚ) ℚ v k ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v :=
    ⟨_, Filter.eventually_cofinite.1 (eventually_componentAt3_mem k), fun v hv => by by_contra h; exact hv h⟩
  rw [finGauge3_eq_prod k (S := hSfin.toFinset) fun v hv => hS v (by simpa using hv)]
  refine Finset.one_le_prod fun v _ => ?_
  exact_mod_cast one_le_matrixSupSize (componentAt3 (𝓞 ℚ) ℚ v k)

private def translateConst (k : AdelicGL 3 (𝓞 ℚ) ℚ) : ℝ := archTranslateConst k * finGauge3 ℚ k

private theorem one_le_translateConst (k : AdelicGL 3 (𝓞 ℚ) ℚ) : 1 ≤ translateConst k :=
  one_le_mul_of_one_le_of_one_le (one_le_archTranslateConst k) (one_le_finGauge3 k)

private theorem gauge3_mul_le_translateConst (g k : AdelicGL 3 (𝓞 ℚ) ℚ) :
    gauge3 ℚ (g * k) ≤ translateConst k * gauge3 ℚ g := by
  have hA := archGauge3_mul_le g k
  have hF := finGauge3_mul_le g k
  have hA0 : 0 ≤ archGauge3 ℚ g := zero_le_one.trans (one_le_archGauge3 ℚ g)
  have hc0 : 0 ≤ archTranslateConst k := zero_le_one.trans (one_le_archTranslateConst k)
  have hFg0 : 0 ≤ finGauge3 ℚ g := finGauge3_nonneg g
  have hFk0 : 0 ≤ finGauge3 ℚ k := finGauge3_nonneg k
  have hFgk0 : 0 ≤ finGauge3 ℚ (g * k) := finGauge3_nonneg (g * k)
  have ht1 : 1 ≤ translateConst k := one_le_translateConst k
  have ht0 : 0 ≤ translateConst k := zero_le_one.trans ht1
  have hmain : archGauge3 ℚ (g * k) * finGauge3 ℚ (g * k) ≤ translateConst k * (archGauge3 ℚ g * finGauge3 ℚ g) := by
    calc archGauge3 ℚ (g * k) * finGauge3 ℚ (g * k)
        ≤ (archTranslateConst k * archGauge3 ℚ g) * (finGauge3 ℚ g * finGauge3 ℚ k) :=
          mul_le_mul hA hF hFgk0 (mul_nonneg hc0 hA0)
      _ = translateConst k * (archGauge3 ℚ g * finGauge3 ℚ g) := by unfold translateConst; ring
  unfold gauge3
  refine max_le ?_ ?_
  · calc (1 : ℝ) ≤ translateConst k * 1 := by rw [mul_one]; exact ht1
      _ ≤ translateConst k * max 1 (archGauge3 ℚ g * finGauge3 ℚ g) :=
          mul_le_mul_of_nonneg_left (le_max_left _ _) ht0
  · calc archGauge3 ℚ (g * k) * finGauge3 ℚ (g * k) ≤ translateConst k * (archGauge3 ℚ g * finGauge3 ℚ g) := hmain
      _ ≤ translateConst k * max 1 (archGauge3 ℚ g * finGauge3 ℚ g) :=
          mul_le_mul_of_nonneg_left (le_max_right _ _) ht0

private theorem exists_forall_translateConst_le_of_isCompact
    {K : Set (AdelicGL 3 (𝓞 ℚ) ℚ)} (hK : IsCompact K) :
    ∃ c : ℝ, ∀ k ∈ K, translateConst k ≤ c := by
  obtain ⟨a, ha⟩ := exists_forall_archTranslateConst_le_of_isCompact hK
  obtain ⟨b, hb⟩ := exists_forall_finGauge3_le_of_isCompact hK
  refine ⟨a * b, fun k hk => ?_⟩
  unfold translateConst
  have h1 : 0 ≤ finGauge3 ℚ k := finGauge3_nonneg k
  have h2 : 0 ≤ archTranslateConst k := zero_le_one.trans (one_le_archTranslateConst k)
  have h3 : 0 ≤ a := h2.trans (ha k hk)
  calc archTranslateConst k * finGauge3 ℚ k ≤ a * finGauge3 ℚ k := mul_le_mul_of_nonneg_right (ha k hk) h1
    _ ≤ a * b := mul_le_mul_of_nonneg_left (hb k hk) h3

end TranslateBound
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_norm_whittaker3_archRealLift3_diag_mul_le_of_isCompact.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_norm_whittaker3_archRealLift3_diag_mul_le_of_isCompact.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_norm_whittaker3_archRealLift3_diag_mul_le_of_isCompact.LanglandsTunnell.CubicInduction.ArchCalculus"

end LanglandsTunnell.CubicInduction
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_norm_whittaker3_archRealLift3_diag_mul_le_of_isCompact.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_norm_whittaker3_archRealLift3_diag_mul_le_of_isCompact.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_norm_whittaker3_archRealLift3_diag_mul_le_of_isCompact.LanglandsTunnell.CubicInduction.ArchCalculus"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_norm_whittaker3_archRealLift3_diag_mul_le_of_isCompact.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_norm_whittaker3_archRealLift3_diag_mul_le_of_isCompact.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_norm_whittaker3_archRealLift3_diag_mul_le_of_isCompact.LanglandsTunnell.CubicInduction.ArchCalculus"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_norm_whittaker3_archRealLift3_diag_mul_le_of_isCompact.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_norm_whittaker3_archRealLift3_diag_mul_le_of_isCompact.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_norm_whittaker3_archRealLift3_diag_mul_le_of_isCompact.LanglandsTunnell.CubicInduction.ArchCalculus"

namespace LanglandsTunnell
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "WhittakerBlock.archDeriv AdelicGL upperUnipotent3 localMaximalCompact3 mem_localMaximalCompact3_iff componentAtN componentAt3 archComponent3 whittaker3 archPlaceComponent3 matrixSize matrixSize_nonneg matrixSupSize archGauge3 finGauge3 gauge3 one_le_gauge3 one_le_archGauge3 WhittakerBlock.archRealLift3_mul WhittakerBlock.archDeriv_eq_fderiv"
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

open ArchCalculus MeasureTheory
p2m_open "LanglandsTunnell.CubicInduction.WhittakerBlock"
open scoped ProbabilityTheory

section Diagonal

private def diagArray (d : Fin 3 → ℝ) : Fin 3 → Fin 3 → ℝ := fun i j => if i = j then d i else 0

private theorem of_diagArray (d : Fin 3 → ℝ) : Matrix.of (diagArray d) = Matrix.diagonal d := by
  ext i j
  simp [diagArray, Matrix.diagonal_apply]

private theorem diagArray_mem_invertibleSet {d : Fin 3 → ℝ} (hd : ∀ i, d i ≠ 0) : diagArray d ∈ invertibleSet := by
  show (Matrix.of (diagArray d)).det ≠ 0
  rw [of_diagArray, Matrix.det_diagonal]
  exact Finset.prod_ne_zero_iff.2 fun i _ => hd i

private theorem diagArray_one : diagArray 1 = oneArray := by
  funext a b
  simp [diagArray, oneArray]

private theorem archRealLift3_diagArray_mul {d d' : Fin 3 → ℝ} (hd : ∀ i, d i ≠ 0) (hd' : ∀ i, d' i ≠ 0) :
    archRealLift3 (diagArray d) * archRealLift3 (diagArray d') = archRealLift3 (diagArray (d * d')) := by
  rw [WhittakerBlock.archRealLift3_mul (diagArray_mem_invertibleSet hd) (diagArray_mem_invertibleSet hd')]
  congr 1
  funext a b
  rw [of_diagArray, of_diagArray, Matrix.diagonal_mul_diagonal]
  simp [diagArray, Matrix.diagonal_apply]

private theorem archRealLift3_diagArray_inv {d : Fin 3 → ℝ} (hd : ∀ i, d i ≠ 0) :
    (archRealLift3 (diagArray d))⁻¹ = archRealLift3 (diagArray d⁻¹) := by
  have hinv : ∀ i, d⁻¹ i ≠ 0 := fun i => by simpa using hd i
  rw [inv_eq_iff_mul_eq_one, archRealLift3_diagArray_mul hd hinv]
  have h1 : d * d⁻¹ = 1 := funext fun i => mul_inv_cancel₀ (hd i)
  rw [h1, diagArray_one]
  exact archRealLift3_one

private theorem coe_archRealLift3 {e : Fin 3 → Fin 3 → ℝ} (he : e ∈ invertibleSet) :
    ((archRealLift3 e : AdelicGL 3 (𝓞 ℚ) ℚ) : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) = archRealMat3 e := by
  rw [archRealLift3_eq e he]
  rfl

private theorem ofRealHom_apply' (r : ℝ) : ofRealHom r = AutomorphicForm.StandardKernel.ofReal r := rfl

private theorem continuous_archRealMat3_comp {X : Type*} [TopologicalSpace X] {E : X → Fin 3 → Fin 3 → ℝ}
    (hE : ∀ i j, Continuous fun x => E x i j) : Continuous fun x => archRealMat3 (E x) := by
  refine continuous_matrix fun i j => ?_
  have h : (fun x => archRealMat3 (E x) i j) =
      fun x => ((ofRealHom (E x i j), ((1 : Matrix (Fin 3) (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ)) i j)) :
        InfiniteAdeleRing ℚ × FiniteAdeleRing (𝓞 ℚ) ℚ) := rfl
  rw [h]
  refine Continuous.prodMk ?_ continuous_const
  simp only [ofRealHom_apply']
  exact AutomorphicForm.StandardKernel.continuous_ofReal.comp (hE i j)

private theorem continuousOn_archRealLift3_torus {y₂ : ℝ} (hy₂ : 0 < y₂) :
    ContinuousOn (fun t : ℝ => archRealLift3 (diagArray ![t * y₂, y₂, 1])) (Set.Ioi 0) := by
  rw [continuousOn_iff_continuous_restrict]
  have hne : ∀ t : Set.Ioi (0 : ℝ), ∀ i, (![(t : ℝ) * y₂, y₂, 1] : Fin 3 → ℝ) i ≠ 0 := by
    intro t i
    have ht : (0 : ℝ) < t := t.2
    fin_cases i <;> simp [ht.ne', hy₂.ne']
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · have h : (Units.val ∘ fun t : Set.Ioi (0 : ℝ) => archRealLift3 (diagArray ![(t : ℝ) * y₂, y₂, 1])) =
        fun t : Set.Ioi (0 : ℝ) => archRealMat3 (diagArray ![(t : ℝ) * y₂, y₂, 1]) := by
      funext t
      exact coe_archRealLift3 (diagArray_mem_invertibleSet (hne t))
    refine (congrArg Continuous h).mpr ?_
    refine continuous_archRealMat3_comp fun i j => ?_
    simp only [diagArray]
    fin_cases i <;> fin_cases j <;> simp <;> fun_prop
  · have h : (fun t : Set.Ioi (0 : ℝ) => ((archRealLift3 (diagArray ![(t : ℝ) * y₂, y₂, 1]))⁻¹ :
        AdelicGL 3 (𝓞 ℚ) ℚ).val) =
        fun t : Set.Ioi (0 : ℝ) => archRealMat3 (diagArray (![(t : ℝ) * y₂, y₂, 1])⁻¹) := by
      funext t
      rw [archRealLift3_diagArray_inv (hne t)]
      exact coe_archRealLift3 (diagArray_mem_invertibleSet fun i => by simpa using hne t i)
    refine (congrArg Continuous h).mpr ?_
    refine continuous_archRealMat3_comp fun i j => ?_
    simp only [diagArray]
    have hy : y₂ ≠ 0 := hy₂.ne'
    fin_cases i <;> fin_cases j <;> simp <;>
      first
      | fun_prop
      | exact (continuous_subtype_val.mul continuous_const).inv₀ fun t => mul_ne_zero (ne_of_gt t.2) hy
      | exact continuous_const.mul (continuous_subtype_val.inv₀ fun t => (show (0 : ℝ) < t from t.2).ne')

end Diagonal
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_norm_whittaker3_archRealLift3_diag_mul_le_of_isCompact.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_norm_whittaker3_archRealLift3_diag_mul_le_of_isCompact.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_norm_whittaker3_archRealLift3_diag_mul_le_of_isCompact.LanglandsTunnell.CubicInduction.ArchCalculus"

section BoxMeasure

@[reducible]
private def adeleMeasurableSpace
    : MeasurableSpace (AdeleRing (𝓞 ℚ) ℚ) := NumberField.AdelicHaar.adeleBorel (𝓞 ℚ) ℚ

attribute [local instance] adeleMeasurableSpace

@[reducible]
private def adeleBorelSpace
    : BorelSpace (AdeleRing (𝓞 ℚ) ℚ) := NumberField.AdelicHaar.borelSpace_adeleBorel (𝓞 ℚ) ℚ

attribute [local instance] adeleBorelSpace

@[reducible]
private def adeleSecondCountable : SecondCountableTopology (AdeleRing (𝓞 ℚ) ℚ) :=
  NumberField.AdeleRing.secondCountableTopology ℚ

attribute [local instance] adeleSecondCountable

private def boxMeasure : Measure (AdeleRing (𝓞 ℚ) ℚ) :=
  (NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ)[|AdelicBox.adelicBox ℚ]

private scoped instance instFiling1 : IsProbabilityMeasure boxMeasure := AdelicBox.isProbabilityMeasure_cond_adelicBox ℚ

private theorem productionPins_ν
    : (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ)).ν = boxMeasure :=
  rfl

private theorem whittaker3_production_eq (Φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (g : AdelicGL 3 (𝓞 ℚ) ℚ) :
    whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
        NumberField.StandardAddChar.psiQ Φ g =
      ∫ x, ∫ y, ∫ z, Φ (upperUnipotent3 x y z * g) * NumberField.StandardAddChar.psiQ (-(x + y))
        ∂boxMeasure ∂boxMeasure ∂boxMeasure :=
  rfl

private theorem exists_isCompact_ae_mem_boxMeasure :
    ∃ C : Set (AdeleRing (𝓞 ℚ) ℚ), IsCompact C ∧ ∀ᵐ x ∂boxMeasure, x ∈ C := by
  obtain ⟨C, hC, hBC⟩ := AdelicBox.exists_isCompact_adelicBox_subset ℚ
  refine ⟨C, hC, ?_⟩
  have h := ProbabilityTheory.ae_cond_mem (μ := NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ)
    (AdelicBox.measurableSet_adelicBox ℚ)
  exact h.mono fun x hx => hBC hx

private def boxMeasure₃ : Measure (AdeleRing (𝓞 ℚ) ℚ × (AdeleRing (𝓞 ℚ) ℚ × AdeleRing (𝓞 ℚ) ℚ)) :=
  boxMeasure.prod (boxMeasure.prod boxMeasure)

private scoped instance instFiling2 : IsProbabilityMeasure boxMeasure₃ := by
  unfold boxMeasure₃
  infer_instance

private theorem exists_isCompact_ae_mem_boxMeasure₃ :
    ∃ C₃ : Set (AdeleRing (𝓞 ℚ) ℚ × (AdeleRing (𝓞 ℚ) ℚ × AdeleRing (𝓞 ℚ) ℚ)), IsCompact C₃ ∧
      ∀ᵐ p ∂boxMeasure₃, p ∈ C₃ := by
  obtain ⟨C, hC, hae⟩ := exists_isCompact_ae_mem_boxMeasure
  refine ⟨C ×ˢ (C ×ˢ C), hC.prod (hC.prod hC), ?_⟩
  have hCm : MeasurableSet C := hC.isClosed.measurableSet
  have h2 : ∀ᵐ q ∂boxMeasure.prod boxMeasure, q ∈ C ×ˢ C :=
    (Measure.ae_prod_mem_iff_ae_ae_mem (hCm.prod hCm)).2 (hae.mono fun x hx => hae.mono fun y hy => ⟨hx, hy⟩)
  exact (Measure.ae_prod_mem_iff_ae_ae_mem (hCm.prod (hCm.prod hCm))).2
    (hae.mono fun x hx => h2.mono fun q hq => ⟨hx, hq⟩)

private theorem integrable_of_continuous_boxMeasure {f : AdeleRing (𝓞 ℚ) ℚ → ℂ} (hf : Continuous f) :
    Integrable f boxMeasure := by
  obtain ⟨C, hC, hae⟩ := exists_isCompact_ae_mem_boxMeasure
  obtain ⟨M, hM⟩ := hC.exists_bound_of_continuousOn hf.continuousOn
  exact (integrable_const M).mono' hf.aestronglyMeasurable (hae.mono fun x hx => hM x hx)

private theorem integrable_of_continuous_boxMeasure₃
    {f : AdeleRing (𝓞 ℚ) ℚ × (AdeleRing (𝓞 ℚ) ℚ × AdeleRing (𝓞 ℚ) ℚ) → ℂ} (hf : Continuous f) :
    Integrable f boxMeasure₃ := by
  obtain ⟨C₃, hC₃, hae⟩ := exists_isCompact_ae_mem_boxMeasure₃
  obtain ⟨M, hM⟩ := hC₃.exists_bound_of_continuousOn hf.continuousOn
  exact (integrable_const M).mono' hf.aestronglyMeasurable (hae.mono fun p hp => hM p hp)

private theorem integrable_of_continuous_boxMeasure₂
    {f : AdeleRing (𝓞 ℚ) ℚ × AdeleRing (𝓞 ℚ) ℚ → ℂ} (hf : Continuous f) :
    Integrable f (boxMeasure.prod boxMeasure) := by
  obtain ⟨C, hC, hae⟩ := exists_isCompact_ae_mem_boxMeasure
  have hCm : MeasurableSet C := hC.isClosed.measurableSet
  have h2 : ∀ᵐ q ∂boxMeasure.prod boxMeasure, q ∈ C ×ˢ C :=
    (Measure.ae_prod_mem_iff_ae_ae_mem (hCm.prod hCm)).2 (hae.mono fun x hx => hae.mono fun y hy => ⟨hx, hy⟩)
  obtain ⟨M, hM⟩ := (hC.prod hC).exists_bound_of_continuousOn hf.continuousOn
  exact (integrable_const M).mono' hf.aestronglyMeasurable (h2.mono fun q hq => hM q hq)

private theorem integral_boxMeasure₃_eq {f : AdeleRing (𝓞 ℚ) ℚ × (AdeleRing (𝓞 ℚ) ℚ × AdeleRing (𝓞 ℚ) ℚ) → ℂ}
    (hf : Continuous f) :
    ∫ p, f p ∂boxMeasure₃ = ∫ x, ∫ y, ∫ z, f (x, (y, z)) ∂boxMeasure ∂boxMeasure ∂boxMeasure := by
  unfold boxMeasure₃
  rw [integral_prod _ (integrable_of_continuous_boxMeasure₃ hf)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  exact integral_prod _
    (integrable_of_continuous_boxMeasure₂ (hf.comp (Continuous.prodMk continuous_const continuous_id)))

private theorem continuous_upperUnipotent3 :
    Continuous fun p : AdeleRing (𝓞 ℚ) ℚ × (AdeleRing (𝓞 ℚ) ℚ × AdeleRing (𝓞 ℚ) ℚ) =>
      (upperUnipotent3 p.1 p.2.1 p.2.2 : AdelicGL 3 (𝓞 ℚ) ℚ) := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · refine continuous_matrix fun i j => ?_
    change Continuous fun p : AdeleRing (𝓞 ℚ) ℚ × (AdeleRing (𝓞 ℚ) ℚ × AdeleRing (𝓞 ℚ) ℚ) =>
      (!![1, p.1, p.2.2; 0, 1, p.2.1; 0, 0, 1] : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) i j
    fin_cases i <;> fin_cases j <;> simp <;> fun_prop
  · refine continuous_matrix fun i j => ?_
    change Continuous fun p : AdeleRing (𝓞 ℚ) ℚ × (AdeleRing (𝓞 ℚ) ℚ × AdeleRing (𝓞 ℚ) ℚ) =>
      (!![1, -p.1, p.1 * p.2.1 - p.2.2; 0, 1, -p.2.1; 0, 0, 1] : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) i j
    fin_cases i <;> fin_cases j <;> simp <;> fun_prop

private theorem whittaker3_production_eq_integral_boxMeasure₃ {Φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ} (hΦ : Continuous Φ)
    (g : AdelicGL 3 (𝓞 ℚ) ℚ) :
    whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
        NumberField.StandardAddChar.psiQ Φ g =
      ∫ p, Φ (upperUnipotent3 p.1 p.2.1 p.2.2 * g) * NumberField.StandardAddChar.psiQ (-(p.1 + p.2.1))
        ∂boxMeasure₃ := by
  rw [whittaker3_production_eq, integral_boxMeasure₃_eq]
  exact (hΦ.comp (continuous_upperUnipotent3.mul continuous_const)).mul
    (NumberField.StandardAddChar.continuous_psiQ.comp (continuous_fst.add (continuous_fst.comp continuous_snd)).neg)

end BoxMeasure
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_norm_whittaker3_archRealLift3_diag_mul_le_of_isCompact.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_norm_whittaker3_archRealLift3_diag_mul_le_of_isCompact.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_norm_whittaker3_archRealLift3_diag_mul_le_of_isCompact.LanglandsTunnell.CubicInduction.ArchCalculus"

end LanglandsTunnell.CubicInduction
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_norm_whittaker3_archRealLift3_diag_mul_le_of_isCompact.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_norm_whittaker3_archRealLift3_diag_mul_le_of_isCompact.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_norm_whittaker3_archRealLift3_diag_mul_le_of_isCompact.LanglandsTunnell.CubicInduction.ArchCalculus"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_norm_whittaker3_archRealLift3_diag_mul_le_of_isCompact.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_norm_whittaker3_archRealLift3_diag_mul_le_of_isCompact.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_norm_whittaker3_archRealLift3_diag_mul_le_of_isCompact.LanglandsTunnell.CubicInduction.ArchCalculus"

namespace LanglandsTunnell
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "WhittakerBlock.archDeriv AdelicGL upperUnipotent3 localMaximalCompact3 mem_localMaximalCompact3_iff componentAtN componentAt3 archComponent3 whittaker3 archPlaceComponent3 matrixSize matrixSize_nonneg matrixSupSize archGauge3 finGauge3 gauge3 one_le_gauge3 one_le_archGauge3 WhittakerBlock.archRealLift3_mul WhittakerBlock.archDeriv_eq_fderiv"
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

open ArchCalculus MeasureTheory
p2m_open "LanglandsTunnell.CubicInduction.WhittakerBlock"
open scoped ProbabilityTheory

section Exchange

@[reducible]
private def instFiling3 : MeasurableSpace (AdeleRing (𝓞 ℚ) ℚ) := NumberField.AdelicHaar.adeleBorel (𝓞 ℚ) ℚ

attribute [local instance] instFiling3

@[reducible]
private def instFiling4 : BorelSpace (AdeleRing (𝓞 ℚ) ℚ) := NumberField.AdelicHaar.borelSpace_adeleBorel (𝓞 ℚ) ℚ

attribute [local instance] instFiling4

@[reducible]
private def instFiling5 : SecondCountableTopology (AdeleRing (𝓞 ℚ) ℚ) :=
  NumberField.AdeleRing.secondCountableTopology ℚ

attribute [local instance] instFiling5

private theorem continuousOn_archRealLift3_diagArray {d : ℝ → Fin 3 → ℝ} {S : Set ℝ}
    (hd : ∀ i, ContinuousOn (fun t => d t i) S)
    (hne : ∀ t ∈ S, ∀ i, d t i ≠ 0) : ContinuousOn (fun t => archRealLift3 (diagArray (d t))) S := by
  rw [continuousOn_iff_continuous_restrict]
  have hd' : ∀ i, Continuous fun t : S => d t i := fun i => continuousOn_iff_continuous_restrict.1 (hd i)
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · have h : (Units.val ∘ fun t : S => archRealLift3 (diagArray (d t))) =
        fun t : S => archRealMat3 (diagArray (d t)) := by
      funext t
      exact coe_archRealLift3 (diagArray_mem_invertibleSet (hne t t.2))
    refine (congrArg Continuous h).mpr ?_
    refine continuous_archRealMat3_comp fun i j => ?_
    simp only [diagArray]
    split_ifs
    · exact hd' i
    · exact continuous_const
  · have h : (fun t : S => ((archRealLift3 (diagArray (d t)))⁻¹ : AdelicGL 3 (𝓞 ℚ) ℚ).val) =
        fun t : S => archRealMat3 (diagArray (d t)⁻¹) := by
      funext t
      rw [archRealLift3_diagArray_inv (hne t t.2)]
      exact coe_archRealLift3 (diagArray_mem_invertibleSet fun i => by simpa using hne t t.2 i)
    refine (congrArg Continuous h).mpr ?_
    refine continuous_archRealMat3_comp fun i j => ?_
    simp only [diagArray, Pi.inv_apply]
    split_ifs
    · exact (hd' i).inv₀ fun t => hne t t.2 i
    · exact continuous_const

private theorem continuousOn_torus₁ {y₂ : ℝ} (hy₂ : 0 < y₂) :
    ContinuousOn (fun t : ℝ => archRealLift3 (diagArray ![t * y₂, y₂, 1])) (Set.Ioi 0) :=
  continuousOn_archRealLift3_diagArray (d := fun t => ![t * y₂, y₂, 1])
    (fun i => by fin_cases i <;> simp <;> fun_prop)
    (fun t ht i => by have : (0 : ℝ) < t := ht; fin_cases i <;> simp [this.ne', hy₂.ne'])

private theorem continuousOn_torus₂ {y₁ : ℝ} (hy₁ : 0 < y₁) :
    ContinuousOn (fun t : ℝ => archRealLift3 (diagArray ![y₁ * t, t, 1])) (Set.Ioi 0) :=
  continuousOn_archRealLift3_diagArray (d := fun t => ![y₁ * t, t, 1])
    (fun i => by fin_cases i <;> simp <;> fun_prop)
    (fun t ht i => by have : (0 : ℝ) < t := ht; fin_cases i <;> simp [hy₁.ne', this.ne'])

private theorem hasDerivAt_comp_archRealLift3
    {u : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ} (hsa : IsArchSmooth3 u) (n : AdelicGL 3 (𝓞 ℚ) ℚ)
    {e : ℝ → Fin 3 → Fin 3 → ℝ} {e' : Fin 3 → Fin 3 → ℝ} {t₀ : ℝ} (he : HasDerivAt e e' t₀)
    (hinv : e t₀ ∈ invertibleSet) :
    HasDerivAt (fun t => u (n * archRealLift3 (e t)))
      (fderiv ℝ (fun e'' => u (n * archRealLift3 e'')) (e t₀) e') t₀ := by
  have hsmooth := (isArchSmooth3_iff u).1 hsa n
  have hdiff : DifferentiableAt ℝ (fun e'' => u (n * archRealLift3 e'')) (e t₀) :=
    ((hsmooth _ hinv).contDiffAt (isOpen_invertibleSet.mem_nhds hinv)).differentiableAt (by simp)
  exact hdiff.hasFDerivAt.comp_hasDerivAt t₀ he

private theorem hasDerivAt_path₁ (y₂ t₀ : ℝ) :
    HasDerivAt (fun t : ℝ => diagArray ![t * y₂, y₂, 1]) (diagArray ![y₂, 0, 0]) t₀ := by
  rw [hasDerivAt_pi]
  intro a
  rw [hasDerivAt_pi]
  intro b
  simp only [diagArray]
  fin_cases a <;> fin_cases b <;> simp <;>
    first
    | simpa using (hasDerivAt_id t₀).mul_const y₂
    | exact hasDerivAt_const t₀ _

private theorem hasDerivAt_path₂ (y₁ t₀ : ℝ) :
    HasDerivAt (fun t : ℝ => diagArray ![y₁ * t, t, 1]) (diagArray ![y₁, 1, 0]) t₀ := by
  rw [hasDerivAt_pi]
  intro a
  rw [hasDerivAt_pi]
  intro b
  simp only [diagArray]
  fin_cases a <;> fin_cases b <;> simp <;>
    first
    | simpa using (hasDerivAt_id t₀).const_mul y₁
    | exact hasDerivAt_id t₀
    | exact hasDerivAt_id'
    | exact hasDerivAt_const t₀ _

private theorem path₁_mem {y₂ : ℝ} (hy₂ : 0 < y₂) {t : ℝ} (ht : 0 < t) : diagArray ![t * y₂, y₂, 1] ∈ invertibleSet :=
  diagArray_mem_invertibleSet fun i => by fin_cases i <;> simp [ht.ne', hy₂.ne']

private theorem path₂_mem {y₁ : ℝ} (hy₁ : 0 < y₁) {t : ℝ} (ht : 0 < t) : diagArray ![y₁ * t, t, 1] ∈ invertibleSet :=
  diagArray_mem_invertibleSet fun i => by fin_cases i <;> simp [hy₁.ne', ht.ne']

private theorem smul_path₁_deriv (y₂ t : ℝ) :
    (fun a b : Fin 3 => if b = (0 : Fin 3) then diagArray ![t * y₂, y₂, 1] a 0 else 0) =
      t • diagArray ![y₂, 0, 0] := by
  funext a b
  simp only [diagArray, Pi.smul_apply, smul_eq_mul]
  fin_cases a <;> fin_cases b <;> simp

private theorem smul_path₂_deriv (y₁ t : ℝ) :
    (fun a b : Fin 3 => if b = (0 : Fin 3) then diagArray ![y₁ * t, t, 1] a 0 else 0) +
        (fun a b : Fin 3 => if b = (1 : Fin 3) then diagArray ![y₁ * t, t, 1] a 1 else 0) =
      t • diagArray ![y₁, 1, 0] := by
  funext a b
  simp only [diagArray, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  fin_cases a <;> fin_cases b <;> simp
  ring

private theorem hasDerivAt_wall₁ {u : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ} (hsa : IsArchSmooth3 u) (n : AdelicGL 3 (𝓞 ℚ) ℚ) {y₂ : ℝ}
    (hy₂ : 0 < y₂) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s : ℝ => u (n * archRealLift3 (diagArray ![s * y₂, y₂, 1])))
      (archDeriv 0 0 u (n * archRealLift3 (diagArray ![t * y₂, y₂, 1])) / (t : ℂ)) t := by
  have h := hasDerivAt_comp_archRealLift3 hsa n (hasDerivAt_path₁ y₂ t) (path₁_mem hy₂ ht)
  convert h using 1
  rw [WhittakerBlock.archDeriv_eq_fderiv hsa 0 0 n (path₁_mem hy₂ ht), smul_path₁_deriv, ContinuousLinearMap.map_smul]
  have htc : (t : ℂ) ≠ 0 := by exact_mod_cast ht.ne'
  rw [Complex.real_smul, mul_div_cancel_left₀ _ htc]

private theorem hasDerivAt_wall₂ {u : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ} (hsa : IsArchSmooth3 u) (n : AdelicGL 3 (𝓞 ℚ) ℚ) {y₁ : ℝ}
    (hy₁ : 0 < y₁) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s : ℝ => u (n * archRealLift3 (diagArray ![y₁ * s, s, 1])))
      ((fun g => archDeriv 0 0 u g + archDeriv 1 1 u g) (n * archRealLift3 (diagArray ![y₁ * t, t, 1])) /
        (t : ℂ)) t := by
  have h := hasDerivAt_comp_archRealLift3 hsa n (hasDerivAt_path₂ y₁ t) (path₂_mem hy₁ ht)
  convert h using 1
  simp only []
  rw [WhittakerBlock.archDeriv_eq_fderiv hsa 0 0 n (path₂_mem hy₁ ht),
    WhittakerBlock.archDeriv_eq_fderiv hsa 1 1 n (path₂_mem hy₁ ht), ← ContinuousLinearMap.map_add, smul_path₂_deriv,
    ContinuousLinearMap.map_smul]
  have htc : (t : ℂ) ≠ 0 := by exact_mod_cast ht.ne'
  rw [Complex.real_smul, mul_div_cancel_left₀ _ htc]

private def integrand (Φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (g : AdelicGL 3 (𝓞 ℚ) ℚ)
    (p : AdeleRing (𝓞 ℚ) ℚ × (AdeleRing (𝓞 ℚ) ℚ × AdeleRing (𝓞 ℚ) ℚ)) : ℂ :=
  Φ (upperUnipotent3 p.1 p.2.1 p.2.2 * g) * NumberField.StandardAddChar.psiQ (-(p.1 + p.2.1))

private theorem whittaker3_production_eq_integral_integrand {Φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ} (hΦ : Continuous Φ)
    (g : AdelicGL 3 (𝓞 ℚ) ℚ) :
    whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
        NumberField.StandardAddChar.psiQ Φ g = ∫ p, integrand Φ g p ∂boxMeasure₃ :=
  whittaker3_production_eq_integral_boxMeasure₃ hΦ g

private theorem continuous_integrand {Φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ} (hΦ : Continuous Φ) (g : AdelicGL 3 (𝓞 ℚ) ℚ) :
    Continuous (integrand Φ g) :=
  (hΦ.comp (continuous_upperUnipotent3.mul continuous_const)).mul
    (NumberField.StandardAddChar.continuous_psiQ.comp (continuous_fst.add (continuous_fst.comp continuous_snd)).neg)

private theorem whittaker3_production_add {Φ₁ Φ₂ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ} (h₁ : Continuous Φ₁) (h₂ : Continuous Φ₂)
    (g : AdelicGL 3 (𝓞 ℚ) ℚ) :
    whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
        NumberField.StandardAddChar.psiQ (Φ₁ + Φ₂) g =
      whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
          NumberField.StandardAddChar.psiQ Φ₁ g +
        whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
          NumberField.StandardAddChar.psiQ Φ₂ g := by
  rw [whittaker3_production_eq_integral_integrand (h₁.add h₂), whittaker3_production_eq_integral_integrand h₁,
    whittaker3_production_eq_integral_integrand h₂,
    ← integral_add (integrable_of_continuous_boxMeasure₃ (continuous_integrand h₁ g))
      (integrable_of_continuous_boxMeasure₃ (continuous_integrand h₂ g))]
  refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
  simp only [integrand, Pi.add_apply]
  ring

private theorem continuousOn_integrand_path
    {Φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ} (hΦ : Continuous Φ) {G : ℝ → AdelicGL 3 (𝓞 ℚ) ℚ}
    (hG : ContinuousOn G (Set.Ioi 0)) :
    ContinuousOn (fun q : ℝ × (AdeleRing (𝓞 ℚ) ℚ × (AdeleRing (𝓞 ℚ) ℚ × AdeleRing (𝓞 ℚ) ℚ)) => integrand Φ (G q.1) q.2)
      (Set.Ioi 0 ×ˢ Set.univ) := by
  have h1 : ContinuousOn (fun q : ℝ × (AdeleRing (𝓞 ℚ) ℚ × (AdeleRing (𝓞 ℚ) ℚ × AdeleRing (𝓞 ℚ) ℚ)) =>
      upperUnipotent3 q.2.1 q.2.2.1 q.2.2.2 * G q.1) (Set.Ioi 0 ×ˢ Set.univ) :=
    (continuous_upperUnipotent3.comp continuous_snd).continuousOn.mul
      (hG.comp continuous_fst.continuousOn fun q hq => hq.1)
  have h2 : Continuous fun q : ℝ × (AdeleRing (𝓞 ℚ) ℚ × (AdeleRing (𝓞 ℚ) ℚ × AdeleRing (𝓞 ℚ) ℚ)) =>
      NumberField.StandardAddChar.psiQ (-(q.2.1 + q.2.2.1)) :=
    NumberField.StandardAddChar.continuous_psiQ.comp
      ((continuous_fst.comp continuous_snd).add (continuous_fst.comp (continuous_snd.comp continuous_snd))).neg
  exact (hΦ.comp_continuousOn h1).mul h2.continuousOn

private theorem hasDerivAt_whittaker3_of_pointwise
    {u Φ' : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ} (hu : Continuous u) (hΦ' : Continuous Φ')
    {G : ℝ → AdelicGL 3 (𝓞 ℚ) ℚ} (hG : ContinuousOn G (Set.Ioi 0))
    (hpt : ∀ n : AdelicGL 3 (𝓞 ℚ) ℚ, ∀ t : ℝ, 0 < t → HasDerivAt (fun s => u (n * G s)) (Φ' (n * G t) / (t : ℂ)) t)
    {t₀ : ℝ} (ht₀ : 0 < t₀) :
    HasDerivAt (fun t => whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
        NumberField.StandardAddChar.psiQ u (G t))
      (whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
        NumberField.StandardAddChar.psiQ Φ' (G t₀) / (t₀ : ℂ)) t₀ := by
  obtain ⟨C₃, hC₃, hae⟩ := exists_isCompact_ae_mem_boxMeasure₃
  have hs_nhds : Set.Icc (t₀ / 2) (2 * t₀) ∈ nhds t₀ := Icc_mem_nhds (by linarith) (by linarith)
  have hs_pos : ∀ t ∈ Set.Icc (t₀ / 2) (2 * t₀), 0 < t := fun t ht => by have := ht.1; linarith
  obtain ⟨B, hB⟩ := (isCompact_Icc.prod hC₃).exists_bound_of_continuousOn
    ((continuousOn_integrand_path hΦ' hG).mono fun q hq => ⟨hs_pos q.1 hq.1, trivial⟩)
  set F : ℝ → AdeleRing (𝓞 ℚ) ℚ × (AdeleRing (𝓞 ℚ) ℚ × AdeleRing (𝓞 ℚ) ℚ) → ℂ := fun t p => integrand u (G t) p with hF
  set F' : ℝ → AdeleRing (𝓞 ℚ) ℚ × (AdeleRing (𝓞 ℚ) ℚ × AdeleRing (𝓞 ℚ) ℚ) → ℂ :=
    fun t p => integrand Φ' (G t) p / (t : ℂ) with hF'
  have hF_meas : ∀ᶠ t in nhds t₀, AEStronglyMeasurable (F t) boxMeasure₃ :=
    Filter.Eventually.of_forall fun t => (continuous_integrand hu (G t)).aestronglyMeasurable
  have hF_int : Integrable (F t₀) boxMeasure₃ := integrable_of_continuous_boxMeasure₃ (continuous_integrand hu (G t₀))
  have hF'_meas : AEStronglyMeasurable (F' t₀) boxMeasure₃ :=
    ((continuous_integrand hΦ' (G t₀)).div_const _).aestronglyMeasurable
  have h_bound : ∀ᵐ p ∂boxMeasure₃, ∀ t ∈ Set.Icc (t₀ / 2) (2 * t₀), ‖F' t p‖ ≤ |B| / (t₀ / 2) := by
    refine hae.mono fun p hp t ht => ?_
    have htpos : 0 < t := hs_pos t ht
    have hBt : ‖integrand Φ' (G t) p‖ ≤ |B| := (hB (t, p) ⟨ht, hp⟩).trans (le_abs_self B)
    simp only [hF', norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos htpos]
    calc ‖integrand Φ' (G t) p‖ / t ≤ |B| / t := div_le_div_of_nonneg_right hBt htpos.le
      _ ≤ |B| / (t₀ / 2) := div_le_div_of_nonneg_left (abs_nonneg B) (half_pos ht₀) ht.1
  have h_diff : ∀ᵐ p ∂boxMeasure₃, ∀ t ∈ Set.Icc (t₀ / 2) (2 * t₀), HasDerivAt (F · p) (F' t p) t := by
    refine Filter.Eventually.of_forall fun p t ht => ?_
    have h := (hpt (upperUnipotent3 p.1 p.2.1 p.2.2) t (hs_pos t ht)).mul_const
      (NumberField.StandardAddChar.psiQ (-(p.1 + p.2.1)))
    convert h using 1
    · rfl
    · rfl
    simp only [hF', integrand]
    ring
  obtain ⟨-, hderiv⟩ := hasDerivAt_integral_of_dominated_loc_of_deriv_le hs_nhds hF_meas hF_int hF'_meas h_bound
    (integrable_const _) h_diff
  have hfun : (fun t => whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
      NumberField.StandardAddChar.psiQ u (G t)) = fun t => ∫ p, F t p ∂boxMeasure₃ := by
    funext t
    exact whittaker3_production_eq_integral_integrand hu (G t)
  have hval : whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
      NumberField.StandardAddChar.psiQ Φ' (G t₀) / (t₀ : ℂ) = ∫ p, F' t₀ p ∂boxMeasure₃ := by
    rw [whittaker3_production_eq_integral_integrand hΦ' (G t₀), ← integral_div]
  rw [hfun, hval]
  exact hderiv

end Exchange
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_norm_whittaker3_archRealLift3_diag_mul_le_of_isCompact.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_norm_whittaker3_archRealLift3_diag_mul_le_of_isCompact.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_norm_whittaker3_archRealLift3_diag_mul_le_of_isCompact.LanglandsTunnell.CubicInduction.ArchCalculus"

private theorem hasDerivAt_whittaker3_archRealLift3_diag_archDeriv_proof
    (u : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)
    (hcw : ∀ w : List (Fin 3 × Fin 3), Continuous (List.foldr (fun ij φ => WhittakerBlock.archDeriv ij.1 ij.2 φ) u w))
    (hsa : WhittakerBlock.IsArchSmooth3 u)
    (y₁ y₂ : ℝ) (hy₁ : 0 < y₁) (hy₂ : 0 < y₂) :
    HasDerivAt (fun t : ℝ => whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
        NumberField.StandardAddChar.psiQ u
        (WhittakerBlock.archRealLift3 (fun i j => if i = j then ![t * y₂, y₂, 1] i else 0)))
      (whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
        NumberField.StandardAddChar.psiQ (WhittakerBlock.archDeriv 0 0 u)
        (WhittakerBlock.archRealLift3 (fun i j => if i = j then ![y₁ * y₂, y₂, 1] i else 0)) / (y₁ : ℂ)) y₁ ∧
    HasDerivAt (fun t : ℝ => whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
        NumberField.StandardAddChar.psiQ u
        (WhittakerBlock.archRealLift3 (fun i j => if i = j then ![y₁ * t, t, 1] i else 0)))
      ((whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
        NumberField.StandardAddChar.psiQ (WhittakerBlock.archDeriv 0 0 u)
        (WhittakerBlock.archRealLift3 (fun i j => if i = j then ![y₁ * y₂, y₂, 1] i else 0)) +
       whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
        NumberField.StandardAddChar.psiQ (WhittakerBlock.archDeriv 1 1 u)
        (WhittakerBlock.archRealLift3 (fun i j => if i = j then ![y₁ * y₂, y₂, 1] i else 0))) / (y₂ : ℂ)) y₂ := by
  have hu : Continuous u := hcw []
  have h00 : Continuous (WhittakerBlock.archDeriv 0 0 u) := hcw [(0, 0)]
  have h11 : Continuous (WhittakerBlock.archDeriv 1 1 u) := hcw [(1, 1)]
  constructor
  · exact hasDerivAt_whittaker3_of_pointwise hu h00 (continuousOn_torus₁ hy₂)
      (fun n t ht => hasDerivAt_wall₁ hsa n hy₂ ht) hy₁
  · have h := hasDerivAt_whittaker3_of_pointwise hu (h00.add h11) (continuousOn_torus₂ hy₁)
      (fun n t ht => hasDerivAt_wall₂ hsa n hy₁ ht) hy₂
    rw [whittaker3_production_add h00 h11] at h
    exact h

end LanglandsTunnell.CubicInduction
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_norm_whittaker3_archRealLift3_diag_mul_le_of_isCompact.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_norm_whittaker3_archRealLift3_diag_mul_le_of_isCompact.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_norm_whittaker3_archRealLift3_diag_mul_le_of_isCompact.LanglandsTunnell.CubicInduction.ArchCalculus"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_norm_whittaker3_archRealLift3_diag_mul_le_of_isCompact.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_norm_whittaker3_archRealLift3_diag_mul_le_of_isCompact.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_norm_whittaker3_archRealLift3_diag_mul_le_of_isCompact.LanglandsTunnell.CubicInduction.ArchCalculus"

namespace LanglandsTunnell
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "WhittakerBlock.archDeriv AdelicGL upperUnipotent3 localMaximalCompact3 mem_localMaximalCompact3_iff componentAtN componentAt3 archComponent3 whittaker3 archPlaceComponent3 matrixSize matrixSize_nonneg matrixSupSize archGauge3 finGauge3 gauge3 one_le_gauge3 one_le_archGauge3 WhittakerBlock.archRealLift3_mul WhittakerBlock.archDeriv_eq_fderiv"
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

open ArchCalculus MeasureTheory
p2m_open "LanglandsTunnell.CubicInduction.WhittakerBlock"

section APriori

@[reducible]
private def instFiling6 : MeasurableSpace (AdeleRing (𝓞 ℚ) ℚ) := NumberField.AdelicHaar.adeleBorel (𝓞 ℚ) ℚ

attribute [local instance] instFiling6

@[reducible]
private def instFiling7 : BorelSpace (AdeleRing (𝓞 ℚ) ℚ) := NumberField.AdelicHaar.borelSpace_adeleBorel (𝓞 ℚ) ℚ

attribute [local instance] instFiling7

@[reducible]
private def instFiling8 : SecondCountableTopology (AdeleRing (𝓞 ℚ) ℚ) :=
  NumberField.AdeleRing.secondCountableTopology ℚ

attribute [local instance] instFiling8

private theorem exists_forall_gauge3_le_of_isCompact {K : Set (AdelicGL 3 (𝓞 ℚ) ℚ)} (hK : IsCompact K) :
    ∃ c : ℝ, 1 ≤ c ∧ ∀ g ∈ K, gauge3 ℚ g ≤ c := by
  obtain ⟨a, ha⟩ := hK.exists_bound_of_continuousOn continuous_archGauge3.continuousOn
  obtain ⟨b, hb⟩ := exists_forall_finGauge3_le_of_isCompact hK
  refine ⟨max 1 (|a| * |b|), le_max_left _ _, fun g hg => ?_⟩
  unfold gauge3
  refine max_le (le_max_left _ _) (le_trans ?_ (le_max_right _ _))
  have h1 : archGauge3 ℚ g ≤ |a| := by
    have := ha g hg
    rw [Real.norm_eq_abs, abs_of_nonneg (zero_le_one.trans (one_le_archGauge3 ℚ g))] at this
    exact this.trans (le_abs_self a)
  have h2 : finGauge3 ℚ g ≤ |b| := (hb g hg).trans (le_abs_self b)
  exact mul_le_mul h1 h2 (finGauge3_nonneg g) (abs_nonneg a)

private theorem finGauge3_one : finGauge3 ℚ (1 : AdelicGL 3 (𝓞 ℚ) ℚ) = 1 := by
  unfold finGauge3
  refine finprod_eq_one_of_forall_eq_one fun v => ?_
  rw [map_one]
  have h : matrixSupSize (1 : GL (Fin 3) (v.adicCompletion ℚ)) = 1 :=
    le_antisymm matrixSupSize_one (one_le_matrixSupSize _)
  simp [h]

private theorem finGauge3_archRealLift3 {e : Fin 3 → Fin 3 → ℝ} (he : e ∈ invertibleSet) :
    finGauge3 ℚ (archRealLift3 e) = 1 := by
  rw [archRealLift3_eq e he, ← mul_one (archInclN (Fin 3) ℚ (archUnit e he)), finGauge3_archInclN_mul, finGauge3_one]

private theorem norm_archPlaceComponent3_archRealLift3_apply (w : InfinitePlace ℚ) {e : Fin 3 → Fin 3 → ℝ}
    (he : e ∈ invertibleSet)
    (i j : Fin 3) :
    ‖((archPlaceComponent3 ℚ w (archRealLift3 e) : GL (Fin 3) w.Completion) :
        Matrix (Fin 3) (Fin 3) w.Completion) i j‖ =
      |e i j| := by
  have h1 : ((archPlaceComponent3 ℚ w (archRealLift3 e) : GL (Fin 3) w.Completion) :
      Matrix (Fin 3) (Fin 3) w.Completion) i j =
        AdelicLevel.archEval ℚ w (AdelicLevel.adeleArch (𝓞 ℚ) ℚ
          (((archRealLift3 e : AdelicGL 3 (𝓞 ℚ) ℚ) : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) i j)) := rfl
  rw [h1, coe_archRealLift3 he]
  have h2 : AdelicLevel.adeleArch (𝓞 ℚ) ℚ (archRealMat3 e i j) = ofRealHom (e i j) := rfl
  rw [h2, ofRealHom_apply']
  change ‖(InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal w)).symm (e i j)‖ = |e i j|
  have hiso := InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal (IsTotallyReal.isReal w)
  have h3 := hiso.norm_map_of_map_zero (map_zero _)
    ((InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal w)).symm (e i j))
  rw [← Real.norm_eq_abs, ← h3]
  congr 1
  exact (InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal w)).apply_symm_apply (e i j)

private theorem one_le_torusParam (y₁ y₂ : ℝ) : 1 ≤ max y₁ 1 * max y₂ 1 * max y₁⁻¹ 1 * max y₂⁻¹ 1 := by
  have h1 : (1 : ℝ) ≤ max y₁ 1 := le_max_right _ _
  have h2 : (1 : ℝ) ≤ max y₂ 1 := le_max_right _ _
  have h3 : (1 : ℝ) ≤ max y₁⁻¹ 1 := le_max_right _ _
  have h4 : (1 : ℝ) ≤ max y₂⁻¹ 1 := le_max_right _ _
  calc (1 : ℝ) = 1 * 1 * 1 * 1 := by norm_num
    _ ≤ max y₁ 1 * max y₂ 1 * max y₁⁻¹ 1 * max y₂⁻¹ 1 :=
        mul_le_mul (mul_le_mul (mul_le_mul h1 h2 zero_le_one (by linarith)) h3 zero_le_one (by positivity)) h4
          zero_le_one (by positivity)

private theorem abs_torus_entry_le {y₁ y₂ : ℝ} (hy₁ : 0 < y₁) (hy₂ : 0 < y₂) (i j : Fin 3) :
    |diagArray ![y₁ * y₂, y₂, 1] i j| ≤ max y₁ 1 * max y₂ 1 * max y₁⁻¹ 1 * max y₂⁻¹ 1 ∧
      |diagArray (![y₁ * y₂, y₂, 1])⁻¹ i j| ≤ max y₁ 1 * max y₂ 1 * max y₁⁻¹ 1 * max y₂⁻¹ 1 := by
  have hP := one_le_torusParam y₁ y₂
  have h1 : y₁ ≤ max y₁ 1 := le_max_left _ _
  have h2 : y₂ ≤ max y₂ 1 := le_max_left _ _
  have h3 : y₁⁻¹ ≤ max y₁⁻¹ 1 := le_max_left _ _
  have h4 : y₂⁻¹ ≤ max y₂⁻¹ 1 := le_max_left _ _
  have m1 : (1 : ℝ) ≤ max y₁ 1 := le_max_right _ _
  have m2 : (1 : ℝ) ≤ max y₂ 1 := le_max_right _ _
  have m3 : (1 : ℝ) ≤ max y₁⁻¹ 1 := le_max_right _ _
  have m4 : (1 : ℝ) ≤ max y₂⁻¹ 1 := le_max_right _ _
  have hy₁i : 0 < y₁⁻¹ := inv_pos.2 hy₁
  have hy₂i : 0 < y₂⁻¹ := inv_pos.2 hy₂

  have e1 : y₁ * y₂ ≤ max y₁ 1 * max y₂ 1 * max y₁⁻¹ 1 * max y₂⁻¹ 1 := by
    calc y₁ * y₂ ≤ max y₁ 1 * max y₂ 1 := mul_le_mul h1 h2 hy₂.le (by linarith)
      _ = max y₁ 1 * max y₂ 1 * 1 * 1 := by ring
      _ ≤ max y₁ 1 * max y₂ 1 * max y₁⁻¹ 1 * max y₂⁻¹ 1 :=
          mul_le_mul (mul_le_mul_of_nonneg_left m3 (by positivity)) m4 zero_le_one (by positivity)
  have e2 : y₂ ≤ max y₁ 1 * max y₂ 1 * max y₁⁻¹ 1 * max y₂⁻¹ 1 := by
    calc y₂ = 1 * y₂ * 1 * 1 := by ring
      _ ≤ max y₁ 1 * max y₂ 1 * max y₁⁻¹ 1 * max y₂⁻¹ 1 :=
          mul_le_mul (mul_le_mul (mul_le_mul m1 h2 hy₂.le (by linarith)) m3 zero_le_one (by positivity)) m4
            zero_le_one (by positivity)
  have e3 : y₁⁻¹ * y₂⁻¹ ≤ max y₁ 1 * max y₂ 1 * max y₁⁻¹ 1 * max y₂⁻¹ 1 := by
    calc y₁⁻¹ * y₂⁻¹ = 1 * 1 * y₁⁻¹ * y₂⁻¹ := by ring
      _ ≤ max y₁ 1 * max y₂ 1 * max y₁⁻¹ 1 * max y₂⁻¹ 1 :=
          mul_le_mul (mul_le_mul (mul_le_mul m1 m2 zero_le_one (by linarith)) h3 hy₁i.le (by positivity)) h4 hy₂i.le
            (by positivity)
  have e4 : y₂⁻¹ ≤ max y₁ 1 * max y₂ 1 * max y₁⁻¹ 1 * max y₂⁻¹ 1 := by
    calc y₂⁻¹ = 1 * 1 * 1 * y₂⁻¹ := by ring
      _ ≤ max y₁ 1 * max y₂ 1 * max y₁⁻¹ 1 * max y₂⁻¹ 1 :=
          mul_le_mul (mul_le_mul (mul_le_mul m1 m2 zero_le_one (by linarith)) m3 zero_le_one (by positivity)) h4
            hy₂i.le (by positivity)
  have hinv : (y₁ * y₂)⁻¹ = y₁⁻¹ * y₂⁻¹ := mul_inv y₁ y₂
  simp only [diagArray, Pi.inv_apply]
  fin_cases i <;> fin_cases j <;> simp [abs_of_pos, hy₁, hy₂, mul_pos hy₁ hy₂, hy₁i, hy₂i, hinv, mul_pos hy₁i hy₂i] <;>
    first
    | exact hP
    | exact e1
    | exact e2
    | exact e3
    | exact e4
    | exact zero_le_one.trans hP
    | exact ⟨e1, e3⟩
    | exact ⟨e2, e4⟩

private theorem translateConst_torus_le {y₁ y₂ : ℝ} (hy₁ : 0 < y₁) (hy₂ : 0 < y₂) :
    translateConst (archRealLift3 (diagArray ![y₁ * y₂, y₂, 1])) ≤
      (1 + 54 * (Fintype.card (InfinitePlace ℚ) : ℝ) * 18) * (max y₁ 1 * max y₂ 1 * max y₁⁻¹ 1 * max y₂⁻¹ 1) := by
  set P : ℝ := max y₁ 1 * max y₂ 1 * max y₁⁻¹ 1 * max y₂⁻¹ 1 with hPdef
  have hP : 1 ≤ P := one_le_torusParam y₁ y₂
  have hd : ∀ i, (![y₁ * y₂, y₂, 1] : Fin 3 → ℝ) i ≠ 0 := fun i => by fin_cases i <;> simp [hy₁.ne', hy₂.ne']
  have hmem : diagArray ![y₁ * y₂, y₂, 1] ∈ invertibleSet := diagArray_mem_invertibleSet hd
  have hmem' : diagArray (![y₁ * y₂, y₂, 1])⁻¹ ∈ invertibleSet :=
    diagArray_mem_invertibleSet fun i => by simpa using hd i

  have hsize : ∀ w : InfinitePlace ℚ,
      matrixSize (archPlaceComponent3 ℚ w (archRealLift3 (diagArray ![y₁ * y₂, y₂, 1]))) ≤
      18 * P := by
    intro w
    unfold matrixSize
    have hentry : ∀ i j : Fin 3,
        ‖((archPlaceComponent3 ℚ w (archRealLift3 (diagArray ![y₁ * y₂, y₂, 1])) : GL (Fin 3) w.Completion) :
            Matrix (Fin 3) (Fin 3) w.Completion) i j‖ +
          ‖(((archPlaceComponent3 ℚ w (archRealLift3 (diagArray ![y₁ * y₂, y₂, 1])))⁻¹ : GL (Fin 3) w.Completion) :
            Matrix (Fin 3) (Fin 3) w.Completion) i j‖ ≤ P + P := by
      intro i j
      obtain ⟨hA, hB⟩ := abs_torus_entry_le hy₁ hy₂ i j
      rw [← map_inv, archRealLift3_diagArray_inv hd, norm_archPlaceComponent3_archRealLift3_apply w hmem,
        norm_archPlaceComponent3_archRealLift3_apply w hmem']
      exact add_le_add hA hB
    calc ∑ i : Fin 3, ∑ j : Fin 3,
          (‖((archPlaceComponent3 ℚ w (archRealLift3 (diagArray ![y₁ * y₂, y₂, 1])) : GL (Fin 3) w.Completion) :
              Matrix (Fin 3) (Fin 3) w.Completion) i j‖ +
            ‖(((archPlaceComponent3 ℚ w (archRealLift3 (diagArray ![y₁ * y₂, y₂, 1])))⁻¹ : GL (Fin 3) w.Completion) :
              Matrix (Fin 3) (Fin 3) w.Completion) i j‖)
        ≤ ∑ i : Fin 3, ∑ j : Fin 3, (P + P) :=
          Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hentry i j
      _ = 18 * P := by simp; ring
  unfold translateConst
  rw [finGauge3_archRealLift3 hmem, mul_one]
  unfold archTranslateConst
  have hsum : ∑ w : InfinitePlace ℚ,
      matrixSize (archPlaceComponent3 ℚ w (archRealLift3 (diagArray ![y₁ * y₂, y₂, 1]))) ≤
      ∑ _w : InfinitePlace ℚ, 18 * P := Finset.sum_le_sum fun w _ => hsize w
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hsum
  have hcard : (0 : ℝ) ≤ (Fintype.card (InfinitePlace ℚ) : ℝ) := Nat.cast_nonneg _
  calc 1 + 54 * ∑ w : InfinitePlace ℚ,
        matrixSize (archPlaceComponent3 ℚ w (archRealLift3 (diagArray ![y₁ * y₂, y₂, 1])))
      ≤ 1 + 54 * ((Fintype.card (InfinitePlace ℚ) : ℝ) * (18 * P)) := by linarith
    _ = 1 + 54 * (Fintype.card (InfinitePlace ℚ) : ℝ) * 18 * P := by ring
    _ ≤ (1 + 54 * (Fintype.card (InfinitePlace ℚ) : ℝ) * 18) * P := by nlinarith [hP, hcard]

end APriori
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_norm_whittaker3_archRealLift3_diag_mul_le_of_isCompact.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_norm_whittaker3_archRealLift3_diag_mul_le_of_isCompact.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_norm_whittaker3_archRealLift3_diag_mul_le_of_isCompact.LanglandsTunnell.CubicInduction.ArchCalculus"

end LanglandsTunnell.CubicInduction
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_norm_whittaker3_archRealLift3_diag_mul_le_of_isCompact.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_norm_whittaker3_archRealLift3_diag_mul_le_of_isCompact.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_norm_whittaker3_archRealLift3_diag_mul_le_of_isCompact.LanglandsTunnell.CubicInduction.ArchCalculus"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_norm_whittaker3_archRealLift3_diag_mul_le_of_isCompact.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_norm_whittaker3_archRealLift3_diag_mul_le_of_isCompact.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_norm_whittaker3_archRealLift3_diag_mul_le_of_isCompact.LanglandsTunnell.CubicInduction.ArchCalculus"

set_option autoImplicit false in
attribute [local instance] LanglandsTunnell.CubicInduction.instFiling6 in
attribute [local instance] LanglandsTunnell.CubicInduction.instFiling7 in
attribute [local instance] LanglandsTunnell.CubicInduction.instFiling8 in
open _root_.LanglandsTunnell.CubicInduction _root_.P2MW.S_LanglandsTunnell_CubicInduction_norm_whittaker3_archRealLift3_diag_mul_le_of_isCompact.LanglandsTunnell.CubicInduction in
open IsDedekindDomain NumberField AutomorphicForm AutomorphicForm.StandardKernel WhittakerBlock in
open IsDedekindDomain NumberField in
open ArchCalculus MeasureTheory in
open WhittakerBlock LanglandsTunnell.CubicInduction.WhittakerBlock in
theorem solution
    (N : ℕ) (u : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)
    (hcw : ∀ w : List (Fin 3 × Fin 3), Continuous (List.foldr (fun ij φ => WhittakerBlock.archDeriv ij.1 ij.2 φ) u w))
    (hgr : ∀ w : List (Fin 3 × Fin 3), ∃ C : ℝ, ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ,
      ‖List.foldr (fun ij φ => WhittakerBlock.archDeriv ij.1 ij.2 φ) u w g‖ ≤ C * gauge3 ℚ g ^ N) :
    ∀ K : Set (AdelicGL 3 (𝓞 ℚ) ℚ), IsCompact K → ∃ C : ℝ, ∀ k ∈ K, ∀ y₁ y₂ : ℝ, 0 < y₁ → 0 < y₂ →
      ‖whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
          NumberField.StandardAddChar.psiQ u
          (WhittakerBlock.archRealLift3 (fun i j => if i = j then ![y₁ * y₂, y₂, 1] i else 0) * k)‖ ≤
        C * (max y₁ 1 * max y₂ 1 * max y₁⁻¹ 1 * max y₂⁻¹ 1) ^ N := by
  intro K hK
  have hu : Continuous u := hcw []
  obtain ⟨Cu, hCu⟩ := hgr []
  have hCu' : ∀ g, ‖u g‖ ≤ Cu * gauge3 ℚ g ^ N := hCu
  obtain ⟨C₃, hC₃, hae⟩ := exists_isCompact_ae_mem_boxMeasure₃

  obtain ⟨cn, hcn1, hcn⟩ := exists_forall_gauge3_le_of_isCompact (hC₃.image continuous_upperUnipotent3)
  obtain ⟨tK, htK⟩ := exists_forall_translateConst_le_of_isCompact hK
  have htK1 : 1 ≤ |tK| + 1 := by linarith [abs_nonneg tK]

  obtain ⟨Bψ, hBψ⟩ := hC₃.exists_bound_of_continuousOn (NumberField.StandardAddChar.continuous_psiQ.comp
    (continuous_fst.add (continuous_fst.comp continuous_snd)).neg).continuousOn
  set c₀ : ℝ := 1 + 54 * (Fintype.card (InfinitePlace ℚ) : ℝ) * 18 with hc₀
  have hc₀1 : 1 ≤ c₀ := by
    have : (0 : ℝ) ≤ (Fintype.card (InfinitePlace ℚ) : ℝ) := Nat.cast_nonneg _
    rw [hc₀]; nlinarith
  refine ⟨|Cu| * ((|tK| + 1) * c₀ * cn) ^ N * |Bψ|, fun k hk y₁ y₂ hy₁ hy₂ => ?_⟩
  set P : ℝ := max y₁ 1 * max y₂ 1 * max y₁⁻¹ 1 * max y₂⁻¹ 1 with hPdef
  have hP : 1 ≤ P := one_le_torusParam y₁ y₂
  set T : AdelicGL 3 (𝓞 ℚ) ℚ := archRealLift3 (diagArray ![y₁ * y₂, y₂, 1]) with hT
  have hTtc : translateConst T ≤ c₀ * P := translateConst_torus_le hy₁ hy₂

  have hpt : ∀ p ∈ C₃, ‖integrand u (T * k) p‖ ≤ |Cu| * ((|tK| + 1) * c₀ * cn) ^ N * |Bψ| * P ^ N := by
    intro p hp
    set n : AdelicGL 3 (𝓞 ℚ) ℚ := upperUnipotent3 p.1 p.2.1 p.2.2 with hn
    have hgn : gauge3 ℚ n ≤ cn := hcn n ⟨p, hp, rfl⟩
    have hgauge : gauge3 ℚ (n * (T * k)) ≤ (|tK| + 1) * c₀ * cn * P := by
      have hk1 : translateConst k ≤ |tK| + 1 := (htK k hk).trans (by linarith [le_abs_self tK])
      have hg0 : 0 ≤ gauge3 ℚ (n * T) := zero_le_one.trans (one_le_gauge3 ℚ _)
      have hn0 : 0 ≤ gauge3 ℚ n := zero_le_one.trans (one_le_gauge3 ℚ _)
      have hTtc0 : 0 ≤ translateConst T := zero_le_one.trans (one_le_translateConst T)
      calc gauge3 ℚ (n * (T * k)) = gauge3 ℚ (n * T * k) := by rw [mul_assoc]
        _ ≤ translateConst k * gauge3 ℚ (n * T) := gauge3_mul_le_translateConst (n * T) k
        _ ≤ translateConst k * (translateConst T * gauge3 ℚ n) :=
            mul_le_mul_of_nonneg_left (gauge3_mul_le_translateConst n T) (zero_le_one.trans (one_le_translateConst k))
        _ ≤ (|tK| + 1) * ((c₀ * P) * cn) := by
            refine mul_le_mul hk1 (mul_le_mul hTtc hgn hn0 (by positivity)) (mul_nonneg hTtc0 hn0) (by positivity)
        _ = (|tK| + 1) * c₀ * cn * P := by ring
    have hpow : gauge3 ℚ (n * (T * k)) ^ N ≤ ((|tK| + 1) * c₀ * cn) ^ N * P ^ N := by
      rw [← mul_pow]
      exact pow_le_pow_left₀ (zero_le_one.trans (one_le_gauge3 ℚ _)) hgauge N
    have hun : ‖u (n * (T * k))‖ ≤ |Cu| * (((|tK| + 1) * c₀ * cn) ^ N * P ^ N) :=
      (hCu' _).trans (mul_le_mul (le_abs_self Cu) hpow
        (pow_nonneg (zero_le_one.trans (one_le_gauge3 ℚ _)) N) (abs_nonneg Cu))
    have hψ : ‖NumberField.StandardAddChar.psiQ (-(p.1 + p.2.1))‖ ≤ |Bψ| := (hBψ p hp).trans (le_abs_self Bψ)
    calc ‖integrand u (T * k) p‖
        = ‖u (n * (T * k))‖ * ‖NumberField.StandardAddChar.psiQ (-(p.1 + p.2.1))‖ := norm_mul _ _
      _ ≤ |Cu| * (((|tK| + 1) * c₀ * cn) ^ N * P ^ N) * |Bψ| := mul_le_mul hun hψ (norm_nonneg _) (by positivity)
      _ = |Cu| * ((|tK| + 1) * c₀ * cn) ^ N * |Bψ| * P ^ N := by ring
  have hint : ‖∫ p, integrand u (T * k) p ∂boxMeasure₃‖ ≤ |Cu| * ((|tK| + 1) * c₀ * cn) ^ N * |Bψ| * P ^ N := by
    have h := norm_integral_le_of_norm_le_const (μ := boxMeasure₃) (hae.mono fun p hp => hpt p hp)
    simpa using h
  have hW : whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
      NumberField.StandardAddChar.psiQ u
      (WhittakerBlock.archRealLift3 (fun i j => if i = j then ![y₁ * y₂, y₂, 1] i else 0) * k) =
        ∫ p, integrand u (T * k) p ∂boxMeasure₃ :=
    whittaker3_production_eq_integral_integrand hu (T * k)
  rw [hW]
  exact hint

end
end S_LanglandsTunnell_CubicInduction_norm_whittaker3_archRealLift3_diag_mul_le_of_isCompact
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_norm_whittaker3_archRealLift3_diag_mul_le_of_isCompact (solution)
