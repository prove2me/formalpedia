-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.mirabolicSeries_eq_dual_of_radicalCoefficient_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/f132f215-85b2-575c-b211-54f48a8b70ab

import Definitions.Def_LanglandsTunnell_CubicInduction_AutomorphyDatum31
import Theorems.Thm_NumberField_AdelicFourier_norm_apply_eq_one_of_isGlobalAddChar
import Theorems.Thm_ContinuousMap_ae_eq_zero_of_forall_mem_starSubalgebra_integral_mul_eq_zero
import Theorems.Thm_NumberField_AdelicFourier_mem_range_algebraMap_of_forall_apply_mul_eq_one
import Theorems.Thm_RatAdele_denseRange_algebraMap_add_adeleSingleAt
import Theorems.Thm_LanglandsTunnell_TateLocal_forall_eq_one_and_exists_ne_one_of_addCharLevel
import Theorems.Thm_LanglandsTunnell_CubicInduction_isCuspidalAlongP21_mirabolicSeries
import Definitions.Def_NumberField_IdeleProductMeasure
import Definitions.Def_LanglandsTunnell_CubicInduction_Structure
import Definitions.Def_AutomorphicForm_WhittakerCoefficient
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

p2m_attr_erase "ext" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.ext"
p2m_attr_erase "ext" "NumberField.InfinitePlace.Completion.ext"
namespace P2MW.S_LanglandsTunnell_CubicInduction_mirabolicSeries_eq_dual_of_radicalCoefficient_eq
p2m_attr_erase "instance" "RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions"
p2m_attr_erase "simp" "ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply"

set_option Elab.async false
set_option autoImplicit false

open IsDedekindDomain NumberField NumberField.AdelicHaar AutomorphicForm Matrix MeasureTheory in
open scoped NNReal ENNReal Pointwise ProbabilityTheory in
local notation "μbox" => ProbabilityTheory.cond (NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ) (AdelicBox.adelicBox ℚ)
open IsDedekindDomain NumberField NumberField.AdelicHaar AutomorphicForm Matrix MeasureTheory in
open scoped NNReal ENNReal Pointwise ProbabilityTheory in
local notation "𝔸" => AdeleRing (𝓞 ℚ) ℚ

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "Converse.IsAdmissibleTwist TateLocal.addCharLevel TateLocal.localBorel TateLocal.borelSpace_localBorel TateLocal.integersPositiveCompacts TateLocal.coe_integersPositiveCompacts TateLocal.selfDualHaarAt TateLocal.higherUnitsAt TateLocal.forall_eq_one_and_exists_ne_one_of_addCharLevel"
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "matrixFin_ext matrixAdele_ext localMatN mapMatrix_localMatN_self mapMatrix_localMatN_of_ne finMatN mapMatrix_arch_finMatN mapMatrix_fin_finMatN localToAdelic3 converseCongruenceSet3 HasVanishingUnipotentIntegralAlong IsCongruenceEquivariantAlong lowerUnipotent21 longWeyl3 longWeyl3_coe dualWhittakerFn3 dualWhittakerFn3_apply weylPrime3 weylPrime3_coe weylPrime3_mul_self transposeInv3_weylPrime3 weylPrime3_mul_transposeInv3_radicalP21_mul_weylPrime3 IsGL3PsiWhittakerFn transposeInv3 IsCuspidalAlongP21 psiLoc mirabolicTranslate AdelicGL globalPointsGL centralScalarGL upperUnipotent3 upperUnipotent3_coe upperUnipotent3_zero radicalP21 radicalP21_zero radicalP21_coe radicalP21_add embedMat2 iotaGL coe_iotaGL iota MirabolicIndex mirabolicRep mirabolicRep_spec mirabolic_mk_unipotent_mul localMaximalCompact3 componentAtN archComponentN componentAt3 archComponent3 LocalGL3 cosetSum IsCosetEigenfunction IsRightInvariant diagUnitGL2 diagHom diagHom_apply isCuspidalAlongP21_mirabolicSeries"
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"
section
open IsDedekindDomain NumberField NumberField.AdelicHaar AutomorphicForm Matrix MeasureTheory
open scoped NNReal ENNReal Pointwise ProbabilityTheory
attribute [local instance] NumberField.Idele.ideleBorel NumberField.AdelicHaar.adeleBorel

section TransposeDual

variable {A : Type*} [CommRing A]

private theorem transposeInv3_mul_aux1 (g h : GL (Fin 3) A) :
    transposeInv3 (g * h) = transposeInv3 g * transposeInv3 h := by
  refine Units.ext ?_
  change ((((g * h)⁻¹ : GL (Fin 3) A)) : Matrix (Fin 3) (Fin 3) A)ᵀ = _
  rw [_root_.mul_inv_rev, Units.val_mul, Matrix.transpose_mul]
  rfl

private theorem transposeInv3_one_aux1 : transposeInv3 (1 : GL (Fin 3) A) = 1 := by
  refine Units.ext ?_
  change ((((1 : GL (Fin 3) A))⁻¹ : GL (Fin 3) A) : Matrix (Fin 3) (Fin 3) A)ᵀ = 1
  rw [inv_one, Units.val_one, Matrix.transpose_one]

private theorem transposeInv3_transposeInv3_aux1 (g : GL (Fin 3) A) : transposeInv3 (transposeInv3 g) = g := by
  refine Units.ext ?_
  change ((((transposeInv3 g)⁻¹ : GL (Fin 3) A)) : Matrix (Fin 3) (Fin 3) A)ᵀ = _
  have h : ((((transposeInv3 g)⁻¹ : GL (Fin 3) A)) : Matrix (Fin 3) (Fin 3) A) =
      ((g : GL (Fin 3) A) : Matrix (Fin 3) (Fin 3) A)ᵀ := rfl
  rw [h, Matrix.transpose_transpose]

private theorem transposeInv3_longWeyl3_aux1 : transposeInv3 (longWeyl3 : GL (Fin 3) A) = longWeyl3 := by
  refine Units.ext ?_
  change ((((longWeyl3 : GL (Fin 3) A))⁻¹ : GL (Fin 3) A) : Matrix (Fin 3) (Fin 3) A)ᵀ = _
  have h : ((((longWeyl3 : GL (Fin 3) A))⁻¹ : GL (Fin 3) A) : Matrix (Fin 3) (Fin 3) A) =
      !![0, 0, 1; 0, 1, 0; 1, 0, 0] := rfl
  rw [h, longWeyl3_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.transpose_apply]

private theorem longWeyl3_mul_self_aux1 : (longWeyl3 : GL (Fin 3) A) * longWeyl3 = 1 := by
  refine Units.ext ?_
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_three]

private theorem longWeyl3_mul_transposeInv3_upperUnipotent3_mul_longWeyl3_aux1 (x y z : A) :
    (longWeyl3 * transposeInv3 (upperUnipotent3 x y z) * longWeyl3 : GL (Fin 3) A) =
      upperUnipotent3 (-y) (-x) (x * y - z) := by
  refine Units.ext ?_
  have hinv : (((upperUnipotent3 x y z : GL (Fin 3) A)⁻¹ : GL (Fin 3) A) : Matrix (Fin 3) (Fin 3) A) =
      !![1, -x, x * y - z; 0, 1, -y; 0, 0, 1] := rfl
  have htr : ((transposeInv3 (upperUnipotent3 x y z) : GL (Fin 3) A) : Matrix (Fin 3) (Fin 3) A) =
      !![1, 0, 0; -x, 1, 0; x * y - z, -y, 1] := by
    change (((upperUnipotent3 x y z : GL (Fin 3) A)⁻¹ : GL (Fin 3) A) : Matrix (Fin 3) (Fin 3) A)ᵀ = _
    rw [hinv]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.transpose_apply]
  rw [Units.val_mul, Units.val_mul, htr, longWeyl3_coe, upperUnipotent3_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]

private theorem longWeyl3_mul_transposeInv3_upperUnipotent3_aux1 (x y z : A) :
    (longWeyl3 * transposeInv3 (upperUnipotent3 x y z) : GL (Fin 3) A) =
      upperUnipotent3 (-y) (-x) (x * y - z) * longWeyl3 := by
  rw [← longWeyl3_mul_transposeInv3_upperUnipotent3_mul_longWeyl3_aux1, mul_assoc, longWeyl3_mul_self_aux1, mul_one]

private theorem isGL3PsiWhittakerFn_dualWhittakerFn3_aux1 {R : Type*} [CommRing R] (ψ : AddChar A R)
    {W : GL (Fin 3) A → R} (hW : IsGL3PsiWhittakerFn ψ W) :
    IsGL3PsiWhittakerFn ψ⁻¹ (dualWhittakerFn3 W) := by
  intro x y z g
  rw [dualWhittakerFn3_apply, dualWhittakerFn3_apply, transposeInv3_mul_aux1, ← mul_assoc,
    AddChar.inv_apply, longWeyl3_mul_transposeInv3_upperUnipotent3_aux1, mul_assoc,
    hW (-y) (-x) (x * y - z) (longWeyl3 * transposeInv3 g), show -y + -x = -(x + y) by ring]

private theorem dualWhittakerFn3_dualWhittakerFn3_aux1 {R : Type*} (W : GL (Fin 3) A → R) :
    dualWhittakerFn3 (dualWhittakerFn3 W) = W := by
  funext g
  rw [dualWhittakerFn3_apply, dualWhittakerFn3_apply, transposeInv3_mul_aux1, transposeInv3_longWeyl3_aux1,
    transposeInv3_transposeInv3_aux1, ← mul_assoc, longWeyl3_mul_self_aux1, one_mul]

private theorem dualWhittakerFn3_apply_mul_weylPrime3_mul_transposeInv3_aux1 {R : Type*} (W : GL (Fin 3) A → R)
    (h g : GL (Fin 3) A) :
    dualWhittakerFn3 W (h * (weylPrime3 * transposeInv3 g)) =
      W (longWeyl3 * transposeInv3 h * weylPrime3 * g) := by
  rw [dualWhittakerFn3_apply, transposeInv3_mul_aux1, transposeInv3_mul_aux1, transposeInv3_weylPrime3,
    transposeInv3_transposeInv3_aux1, ← mul_assoc, ← mul_assoc]

end TransposeDual

section Transport

variable {A : Type*} [CommRing A]

private theorem iotaGL_mul_upperUnipotent3_zero_aux1 (h : GL (Fin 2) A) (y z : A) :
    iotaGL h * upperUnipotent3 0 y z =
      upperUnipotent3 0 ((h : Matrix (Fin 2) (Fin 2) A) 1 0 * z + (h : Matrix (Fin 2) (Fin 2) A) 1 1 * y)
        ((h : Matrix (Fin 2) (Fin 2) A) 0 0 * z + (h : Matrix (Fin 2) (Fin 2) A) 0 1 * y) * iotaGL h := by
  refine Units.ext ?_
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Units.val_mul, coe_iotaGL, embedMat2, Matrix.mul_apply, Fin.sum_univ_three]

private theorem iotaGL_mul_upperUnipotent3 (h : GL (Fin 2) A) (t : A) :
    iotaGL h * upperUnipotent3 0 t 0 =
      upperUnipotent3 0 ((h : Matrix (Fin 2) (Fin 2) A) 1 1 * t) ((h : Matrix (Fin 2) (Fin 2) A) 0 1 * t) *
        iotaGL h := by
  simpa using iotaGL_mul_upperUnipotent3_zero_aux1 h t 0

private theorem whittaker_iotaGL_mul_upperUnipotent3_mul {R : Type*} [CommRing R] (ψ' : AddChar A R)
    {W' : GL (Fin 3) A → R} (hW' : IsGL3PsiWhittakerFn ψ' W') (h : GL (Fin 2) A) (t : A) (X : GL (Fin 3) A) :
    W' (iotaGL h * (upperUnipotent3 0 t 0 * X)) =
      ψ' ((h : Matrix (Fin 2) (Fin 2) A) 1 1 * t) * W' (iotaGL h * X) := by
  rw [← mul_assoc, iotaGL_mul_upperUnipotent3, mul_assoc, hW', zero_add]

private theorem lowerUnipotent21_mul_upperUnipotent3_comm (z t : A) :
    lowerUnipotent21 z * upperUnipotent3 0 t 0 = upperUnipotent3 0 t 0 * lowerUnipotent21 z := by
  refine Units.ext ?_
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_three]

private theorem weylPrime3_mul_transposeInv3_radicalP21_mul_weylPrime3_eq_aux1 (v : Fin 2 → A) :
    (weylPrime3 * transposeInv3 (radicalP21 v) * weylPrime3 : GL (Fin 3) A) =
      lowerUnipotent21 (-(v 0)) * upperUnipotent3 0 (-(v 1)) 0 := by
  refine Units.ext ?_
  rw [weylPrime3_mul_transposeInv3_radicalP21_mul_weylPrime3]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_three]

private theorem transposeInv3_iotaGL_diagUnitGL2 (a : Aˣ) :
    transposeInv3 (iotaGL (diagUnitGL2 a)) = iotaGL (diagUnitGL2 a⁻¹) := by
  refine Units.ext ?_
  change ((((iotaGL (diagUnitGL2 a))⁻¹ : GL (Fin 3) A)) : Matrix (Fin 3) (Fin 3) A)ᵀ = _
  rw [← map_inv iotaGL, ← diagHom_apply, ← map_inv diagHom, diagHom_apply]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [coe_iotaGL, embedMat2]

private theorem weylPrime3_mul_iotaGL_diagUnitGL2_mul_weylPrime3 (b : Aˣ) :
    (weylPrime3 * iotaGL (diagUnitGL2 b) * weylPrime3 : GL (Fin 3) A) = iotaGL (diagUnitGL2 b) := by
  refine Units.ext ?_
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Units.val_mul, coe_iotaGL, embedMat2, Matrix.mul_apply, Fin.sum_univ_three]

private theorem weylPrime3_mul_transposeInv3_radicalP21_mul_diag_mul (z y : A) (a : Aˣ) (g : GL (Fin 3) A) :
    weylPrime3 * transposeInv3 (radicalP21 ![z, y] * (iotaGL (diagUnitGL2 a) * g)) =
      lowerUnipotent21 (-z) * upperUnipotent3 0 (-y) 0 *
        (iotaGL (diagUnitGL2 a⁻¹) * (weylPrime3 * transposeInv3 g)) := by
  have h5 := weylPrime3_mul_transposeInv3_radicalP21_mul_weylPrime3_eq_aux1 (A := A) ![z, y]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h5
  have hww : ∀ X : GL (Fin 3) A, weylPrime3 * (weylPrime3 * X) = X := fun X => by
    rw [← mul_assoc, weylPrime3_mul_self, one_mul]
  rw [transposeInv3_mul_aux1, transposeInv3_mul_aux1, transposeInv3_iotaGL_diagUnitGL2, ← h5]
  conv_rhs => rw [← weylPrime3_mul_iotaGL_diagUnitGL2_mul_weylPrime3 a⁻¹]
  simp only [mul_assoc, hww]

end Transport

section Terms

private theorem dual_term_radical_eq (ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ) {W : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ}
    (hW : IsGL3PsiWhittakerFn ψ W) (g : AdelicGL 3 (𝓞 ℚ) ℚ) (a : (AdeleRing (𝓞 ℚ) ℚ)ˣ) (i : MirabolicIndex ℚ)
    (z y : AdeleRing (𝓞 ℚ) ℚ) :
    dualWhittakerFn3 W (mirabolicTranslate i *
        (weylPrime3 * transposeInv3 (radicalP21 ![z, y] * (iotaGL (diagUnitGL2 a) * g)))) =
      ψ (((globalPoints (𝓞 ℚ) ℚ (mirabolicRep ℚ i) : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) :
            Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) 1 1 * y) *
        dualWhittakerFn3 W (mirabolicTranslate i *
          (lowerUnipotent21 (-z) * (iotaGL (diagUnitGL2 a⁻¹) * (weylPrime3 * transposeInv3 g)))) := by
  have hdual := isGL3PsiWhittakerFn_dualWhittakerFn3_aux1 ψ hW
  rw [weylPrime3_mul_transposeInv3_radicalP21_mul_diag_mul, lowerUnipotent21_mul_upperUnipotent3_comm, mul_assoc]
  show dualWhittakerFn3 W (iotaGL (globalPoints (𝓞 ℚ) ℚ (mirabolicRep ℚ i)) * _) =
    _ * dualWhittakerFn3 W (iotaGL (globalPoints (𝓞 ℚ) ℚ (mirabolicRep ℚ i)) * _)
  rw [whittaker_iotaGL_mul_upperUnipotent3_mul ψ⁻¹ hdual, AddChar.inv_apply, mul_neg, neg_neg]

end Terms

section YStep

private theorem setIntegral_adelicBox_comp_add_right_aux1 {f : AdeleRing (𝓞 ℚ) ℚ → ℂ}
    (hf : ∀ (α : ℚ) (y : AdeleRing (𝓞 ℚ) ℚ), f (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) α + y) = f y)
    (s : AdeleRing (𝓞 ℚ) ℚ) :
    ∫ y in AdelicBox.adelicBox ℚ, f (y + s) ∂(NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ) =
      ∫ y in AdelicBox.adelicBox ℚ, f y ∂(NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ) := by
  haveI := NumberField.AdelicHaar.borelSpace_adeleBorel (𝓞 ℚ) ℚ
  haveI := NumberField.AdelicHaar.isAddHaarMeasure_adelicAddHaar (𝓞 ℚ) ℚ
  set μ : Measure (AdeleRing (𝓞 ℚ) ℚ) := NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ with hμ

  have hf' : ∀ (γ : AdeleRing.principalSubgroup (𝓞 ℚ) ℚ) (y : AdeleRing (𝓞 ℚ) ℚ), f (γ +ᵥ y) = f y := by
    intro γ y
    obtain ⟨α, hα⟩ := RingHom.mem_range.mp γ.2
    show f ((γ : AdeleRing (𝓞 ℚ) ℚ) + y) = f y
    rw [← hα]
    exact hf α y
  have hbox := AdelicBox.isAddFundamentalDomain_adelicBox ℚ μ

  haveI : Countable (AdeleRing.principalSubgroup (𝓞 ℚ) ℚ) := by
    refine Function.Surjective.countable (f := fun α : ℚ =>
      (⟨algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) α, ⟨α, rfl⟩⟩ : AdeleRing.principalSubgroup (𝓞 ℚ) ℚ)) ?_
    rintro ⟨x, hx⟩
    obtain ⟨α, rfl⟩ := RingHom.mem_range.mp hx
    exact ⟨α, rfl⟩

  have hbox' : IsAddFundamentalDomain (AdeleRing.principalSubgroup (𝓞 ℚ) ℚ) (s +ᵥ AdelicBox.adelicBox ℚ) μ :=
    hbox.vadd_of_comm s

  have hpre : (fun y : AdeleRing (𝓞 ℚ) ℚ => y + s) ⁻¹' (s +ᵥ AdelicBox.adelicBox ℚ) = AdelicBox.adelicBox ℚ := by
    ext y
    simp only [Set.mem_preimage, Set.mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add]
    rw [show -s + (y + s) = y by abel]
  have hshift := (measurePreserving_add_right μ s).setIntegral_preimage_emb
    (MeasurableEquiv.addRight s).measurableEmbedding f (s +ᵥ AdelicBox.adelicBox ℚ)
  rw [hpre] at hshift
  rw [hshift]
  exact hbox'.setIntegral_eq hbox hf'

private theorem addChar_mul_algebraMap_add_aux1 {ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ}
    (hψ : IsPrincipalInvariantAddChar ℚ ψ) (β α : ℚ) (y : AdeleRing (𝓞 ℚ) ℚ) :
    ψ (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) β * (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) α + y)) =
      ψ (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) β * y) := by
  rw [mul_add, AddChar.map_add_eq_mul, ← map_mul (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ)), hψ (β * α), one_mul]

private theorem setIntegral_adelicBox_addChar_mul_eq_zero_aux1 {ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ}
    (hψ : IsGlobalAddChar ℚ ψ)
    {β : ℚ} (hβ : β ≠ 0) :
    ∫ y in AdelicBox.adelicBox ℚ, ψ (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) β * y)
      ∂(NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ) = 0 := by
  obtain ⟨t, ht⟩ : ∃ t : AdeleRing (𝓞 ℚ) ℚ, ψ t ≠ 1 := by
    by_contra h
    refine hψ.nontrivial (AddChar.ext ψ 1 fun t => ?_)
    rw [AddChar.one_apply]
    by_contra ht
    exact h ⟨t, ht⟩
  set I : ℂ := ∫ y in AdelicBox.adelicBox ℚ, ψ (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) β * y)
    ∂(NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ) with hI
  have hβt : algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) β * (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) β⁻¹ * t) = t := by
    rw [← mul_assoc, ← map_mul, mul_inv_cancel₀ hβ, map_one, one_mul]
  have hshift := setIntegral_adelicBox_comp_add_right_aux1
    (f := fun y => ψ (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) β * y))
    (addChar_mul_algebraMap_add_aux1 hψ.principalInvariant β) (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) β⁻¹ * t)
  have hmul : (∫ y in AdelicBox.adelicBox ℚ,
      ψ (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) β * (y + algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) β⁻¹ * t))
        ∂(NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ)) = ψ t * I := by
    rw [hI, ← integral_const_mul]
    congr 1
    funext y
    rw [mul_add, AddChar.map_add_eq_mul, hβt, mul_comm]
  have h : ψ t * I = I := by
    rw [← hmul]
    exact hshift
  have h' : (ψ t - 1) * I = 0 := by rw [sub_mul, one_mul, h, sub_self]
  exact (mul_eq_zero.mp h').resolve_left (sub_ne_zero.mpr ht)

private theorem integral_box_phase_eq_zero {ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ} (hψ : IsGlobalAddChar ℚ ψ)
    {β : ℚ} (hβ : β ≠ 0) :
    ∫ y, ψ (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) β * y) ∂μbox = 0 := by
  rw [ProbabilityTheory.cond, integral_smul_measure, setIntegral_adelicBox_addChar_mul_eq_zero_aux1 hψ hβ, smul_zero]

private theorem globalPoints_apply_one_one (h : GL (Fin 2) ℚ) :
    ((globalPoints (𝓞 ℚ) ℚ h : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) 1 1 =
      algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) ((h : Matrix (Fin 2) (Fin 2) ℚ) 1 1) :=
  Matrix.GeneralLinearGroup.map_apply _ _ _ _

private theorem integral_box_phase_mul {ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ} (hψ : IsGlobalAddChar ℚ ψ) (δ : ℚ) :
    ∫ y, ψ (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) δ * y) * ψ (-y) ∂μbox = if δ = 1 then 1 else 0 := by
  haveI := AdelicBox.isProbabilityMeasure_cond_adelicBox ℚ
  have hcomb : ∀ y : AdeleRing (𝓞 ℚ) ℚ,
      ψ (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) δ * y) * ψ (-y) = ψ (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) (δ - 1) * y) := by
    intro y
    rw [← AddChar.map_add_eq_mul, map_sub, map_one]
    ring_nf
  simp_rw [hcomb]
  split_ifs with hδ
  · subst hδ
    simp
  · exact integral_box_phase_eq_zero hψ (sub_ne_zero.mpr hδ)

private theorem integral_box_tsum_phase {ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ} (hψ : IsGlobalAddChar ℚ ψ)
    (d : MirabolicIndex ℚ → AdeleRing (𝓞 ℚ) ℚ) (T : MirabolicIndex ℚ → ℂ) (hT : Summable T) :
    ∫ y, (∑' i, ψ (d i * y) * T i) * ψ (-y) ∂μbox = ∑' i, (∫ y, ψ (d i * y) * ψ (-y) ∂μbox) * T i := by
  haveI := AdelicBox.isProbabilityMeasure_cond_adelicBox ℚ
  haveI := borelSpace_adeleBorel (𝓞 ℚ) ℚ
  have hψc : Continuous ψ := hψ.continuous
  have hcont : ∀ i, Continuous fun y : AdeleRing (𝓞 ℚ) ℚ => ψ (d i * y) * T i * ψ (-y) := fun i =>
    ((hψc.comp (continuous_const.mul continuous_id)).mul continuous_const).mul (hψc.comp continuous_neg)
  have hnn : ∀ (i : MirabolicIndex ℚ) (y : AdeleRing (𝓞 ℚ) ℚ), ‖ψ (d i * y) * T i * ψ (-y)‖ₑ = ‖T i‖ₑ := by
    intro i y
    have h1 : ∀ x, ‖ψ x‖ₑ = 1 := fun x => by
      have hx : ‖ψ x‖ = 1 := by
        simpa using NumberField.AdelicFourier.norm_apply_eq_one_of_isGlobalAddChar ℚ hψ x
      rw [← ofReal_norm, hx, ENNReal.ofReal_one]
    rw [enorm_mul, enorm_mul, h1, h1, one_mul, mul_one]
  have hsumn : Summable fun i => ‖T i‖₊ :=
    NNReal.summable_coe.mp (by simpa only [coe_nnnorm] using (summable_norm_iff (f := T)).mpr hT)
  have hfun : (fun y : AdeleRing (𝓞 ℚ) ℚ => (∑' i, ψ (d i * y) * T i) * ψ (-y)) =
      fun y => ∑' i, ψ (d i * y) * T i * ψ (-y) := by
    funext y
    exact tsum_mul_right.symm
  rw [hfun, integral_tsum (fun i => (hcont i).aestronglyMeasurable)]
  · refine tsum_congr fun i => ?_
    simp_rw [mul_right_comm _ (T i)]
    exact integral_mul_const _ _
  · simp_rw [hnn, lintegral_const, measure_univ, mul_one, enorm_eq_nnnorm]
    exact ENNReal.tsum_coe_ne_top_iff_summable.mpr hsumn

private theorem integral_box_dualSeries_radical {ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ} (hψ : IsGlobalAddChar ℚ ψ)
    {W : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ} (hW : IsGL3PsiWhittakerFn ψ W)
    (hsum' : ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ,
      Summable fun i : MirabolicIndex ℚ => dualWhittakerFn3 W (mirabolicTranslate i * g))
    (g : AdelicGL 3 (𝓞 ℚ) ℚ) (a : (AdeleRing (𝓞 ℚ) ℚ)ˣ) (z : AdeleRing (𝓞 ℚ) ℚ) :
    ∫ y, (∑' i : MirabolicIndex ℚ, dualWhittakerFn3 W (mirabolicTranslate i *
          (weylPrime3 * transposeInv3 (radicalP21 ![z, y] * (iotaGL (diagUnitGL2 a) * g))))) * ψ (-y) ∂μbox =
      ∑' i : MirabolicIndex ℚ,
        if ((mirabolicRep ℚ i : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) 1 1 = 1 then
          dualWhittakerFn3 W (mirabolicTranslate i *
            (lowerUnipotent21 (-z) * (iotaGL (diagUnitGL2 a⁻¹) * (weylPrime3 * transposeInv3 g))))
        else 0 := by
  simp_rw [dual_term_radical_eq ψ hW g a _ z, globalPoints_apply_one_one]
  rw [integral_box_tsum_phase hψ
    (fun i => algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) (((mirabolicRep ℚ i : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) 1 1))
    (fun i => dualWhittakerFn3 W (mirabolicTranslate i *
      (lowerUnipotent21 (-z) * (iotaGL (diagUnitGL2 a⁻¹) * (weylPrime3 * transposeInv3 g))))) (hsum' _)]
  refine tsum_congr fun i => ?_
  rw [integral_box_phase_mul hψ]
  split_ifs <;> simp

end YStep

section ConstantTerm

variable {A : Type*} [CommRing A]

private theorem iotaGL_mul_lowerUnipotent21_of_apply_one_one_eq_zero (h : GL (Fin 2) A) (t s : A)
    (h11 : (h : Matrix (Fin 2) (Fin 2) A) 1 1 = 0)
    (hs : (h : Matrix (Fin 2) (Fin 2) A) 0 1 * t = s * (h : Matrix (Fin 2) (Fin 2) A) 1 0) :
    iotaGL h * lowerUnipotent21 t = upperUnipotent3 s 0 0 * iotaGL h := by
  refine Units.ext ?_
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Units.val_mul, coe_iotaGL, embedMat2, Matrix.mul_apply, Fin.sum_univ_three, h11, hs, mul_comm]

private theorem whittaker_upperUnipotent3_left_mul {R : Type*} [CommRing R] (ψ' : AddChar A R)
    {W' : GL (Fin 3) A → R} (hW' : IsGL3PsiWhittakerFn ψ' W') (s : A) (X : GL (Fin 3) A) :
    W' (upperUnipotent3 s 0 0 * X) = ψ' s * W' X := by
  rw [hW', add_zero]

end ConstantTerm

section ConstantTermRat

private theorem integral_box_phase_eq_ite {ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ} (hψ : IsGlobalAddChar ℚ ψ) (δ : ℚ) :
    ∫ y, ψ (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) δ * y) ∂μbox = if δ = 0 then 1 else 0 := by
  haveI := AdelicBox.isProbabilityMeasure_cond_adelicBox ℚ
  split_ifs with h
  · subst h
    simp
  · exact integral_box_phase_eq_zero hψ h

private theorem integral_box_tsum_phase_rat {ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ} (hψ : IsGlobalAddChar ℚ ψ)
    (δ : MirabolicIndex ℚ → ℚ) (T : MirabolicIndex ℚ → ℂ) (hT : Summable T) :
    ∫ y, (∑' i, ψ (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) (δ i) * y) * T i) ∂μbox = ∑' i, if δ i = 0 then T i else 0 := by
  have hshift : ∀ y : AdeleRing (𝓞 ℚ) ℚ,
      (∑' i, ψ (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) (δ i) * y) * T i) =
        (∑' i, ψ (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) (δ i + 1) * y) * T i) * ψ (-y) := by
    intro y
    rw [← tsum_mul_right]
    refine tsum_congr fun i => ?_
    have h1 : ψ y * ψ (-y) = 1 := by
      rw [← AddChar.map_add_eq_mul, add_neg_cancel, AddChar.map_zero_eq_one]
    rw [map_add, map_one, add_mul, one_mul, AddChar.map_add_eq_mul]
    linear_combination (-(ψ (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) (δ i) * y) * T i)) * h1
  simp_rw [hshift]
  rw [integral_box_tsum_phase hψ (fun i => algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) (δ i + 1)) T hT]
  refine tsum_congr fun i => ?_
  rw [integral_box_phase_mul hψ]
  by_cases h : δ i = 0
  · simp [h]
  · simp [h]

private theorem integral_box_dualSeries_radical_unweighted {ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ}
    (hψ : IsGlobalAddChar ℚ ψ)
    {W : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ} (hW : IsGL3PsiWhittakerFn ψ W)
    (hsum' : ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ,
      Summable fun i : MirabolicIndex ℚ => dualWhittakerFn3 W (mirabolicTranslate i * g))
    (g : AdelicGL 3 (𝓞 ℚ) ℚ) (a : (AdeleRing (𝓞 ℚ) ℚ)ˣ) (z : AdeleRing (𝓞 ℚ) ℚ) :
    ∫ y, (∑' i : MirabolicIndex ℚ, dualWhittakerFn3 W (mirabolicTranslate i *
          (weylPrime3 * transposeInv3 (radicalP21 ![z, y] * (iotaGL (diagUnitGL2 a) * g))))) ∂μbox =
      ∑' i : MirabolicIndex ℚ,
        if ((mirabolicRep ℚ i : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) 1 1 = 0 then
          dualWhittakerFn3 W (mirabolicTranslate i *
            (lowerUnipotent21 (-z) * (iotaGL (diagUnitGL2 a⁻¹) * (weylPrime3 * transposeInv3 g))))
        else 0 := by
  simp_rw [dual_term_radical_eq ψ hW g a _ z, globalPoints_apply_one_one]
  exact integral_box_tsum_phase_rat hψ (fun i => ((mirabolicRep ℚ i : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) 1 1)
    (fun i => dualWhittakerFn3 W (mirabolicTranslate i *
      (lowerUnipotent21 (-z) * (iotaGL (diagUnitGL2 a⁻¹) * (weylPrime3 * transposeInv3 g))))) (hsum' _)

private noncomputable def phaseCoeff (i : MirabolicIndex ℚ) : ℚ :=
  ((mirabolicRep ℚ i : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) 0 1 /
    ((mirabolicRep ℚ i : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) 1 0

private theorem det_ne_zero_rep (i : MirabolicIndex ℚ) :
    ((mirabolicRep ℚ i : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ).det ≠ 0 :=
  ((Matrix.isUnit_iff_isUnit_det _).mp (mirabolicRep ℚ i).isUnit).ne_zero

private theorem apply_one_zero_ne_zero_of_apply_one_one_eq_zero (i : MirabolicIndex ℚ)
    (h11 : ((mirabolicRep ℚ i : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) 1 1 = 0) :
    ((mirabolicRep ℚ i : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) 1 0 ≠ 0 := by
  intro h10
  apply det_ne_zero_rep i
  rw [Matrix.det_fin_two, h11, h10]
  ring

private theorem phaseCoeff_ne_zero_of_apply_one_one_eq_zero (i : MirabolicIndex ℚ)
    (h11 : ((mirabolicRep ℚ i : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) 1 1 = 0) : phaseCoeff i ≠ 0 := by
  have h01 : ((mirabolicRep ℚ i : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) 0 1 ≠ 0 := by
    intro h01
    apply det_ne_zero_rep i
    rw [Matrix.det_fin_two, h11, h01]
    ring
  exact div_ne_zero h01 (apply_one_zero_ne_zero_of_apply_one_one_eq_zero i h11)

private theorem dual_term_lower_eq {ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ} {W : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ}
    (hW : IsGL3PsiWhittakerFn ψ W) (i : MirabolicIndex ℚ)
    (h11 : ((mirabolicRep ℚ i : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) 1 1 = 0) (z : AdeleRing (𝓞 ℚ) ℚ)
    (Y : AdelicGL 3 (𝓞 ℚ) ℚ) :
    dualWhittakerFn3 W (mirabolicTranslate i * (lowerUnipotent21 (-z) * Y)) =
      ψ (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) (phaseCoeff i) * z) * dualWhittakerFn3 W (mirabolicTranslate i * Y) := by
  have hdual := isGL3PsiWhittakerFn_dualWhittakerFn3_aux1 ψ hW
  set H : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ) := globalPoints (𝓞 ℚ) ℚ (mirabolicRep ℚ i) with hH
  have hH11 : (H : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) 1 1 = 0 := by
    rw [hH, globalPoints_apply_one_one, h11, map_zero]
  have hent : ∀ k l : Fin 2, (H : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) k l =
      algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) (((mirabolicRep ℚ i : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) k l) :=
    fun k l =>
    Matrix.GeneralLinearGroup.map_apply _ _ _ _
  have h10 := apply_one_zero_ne_zero_of_apply_one_one_eq_zero i h11
  have hc : algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) (phaseCoeff i) * (H : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) 1 0 =
      (H : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) 0 1 := by
    rw [hent 1 0, hent 0 1, ← map_mul, phaseCoeff, div_mul_cancel₀ _ h10]
  have hs : (H : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) 0 1 * (-z) =
      (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) (phaseCoeff i) * (-z)) *
        (H : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) 1 0 := by
    rw [← hc]
    ring
  show dualWhittakerFn3 W (iotaGL H * (lowerUnipotent21 (-z) * Y)) = _ * dualWhittakerFn3 W (iotaGL H * Y)
  rw [← mul_assoc, iotaGL_mul_lowerUnipotent21_of_apply_one_one_eq_zero H (-z) _ hH11 hs, mul_assoc,
    whittaker_upperUnipotent3_left_mul ψ⁻¹ hdual, AddChar.inv_apply, mul_neg, neg_neg]

end ConstantTermRat

section Head

private theorem box_integral_dualSeries_radical_eq_zero
    (ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ) (hψ : IsGlobalAddChar ℚ ψ)
    (W : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hW : IsGL3PsiWhittakerFn ψ W)
    (hsum' : ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ,
      Summable fun i : MirabolicIndex ℚ => dualWhittakerFn3 W (mirabolicTranslate i * g))
    (g : AdelicGL 3 (𝓞 ℚ) ℚ) (a : (AdeleRing (𝓞 ℚ) ℚ)ˣ) :
    ∫ z : AdeleRing (𝓞 ℚ) ℚ, ∫ y : AdeleRing (𝓞 ℚ) ℚ,
        (∑' i : MirabolicIndex ℚ, dualWhittakerFn3 W (mirabolicTranslate i *
          (weylPrime3 * transposeInv3 (radicalP21 ![z, y] * (iotaGL (diagUnitGL2 a) * g)))))
      ∂μbox ∂μbox = 0 := by
  set Y : AdelicGL 3 (𝓞 ℚ) ℚ := iotaGL (diagUnitGL2 a⁻¹) * (weylPrime3 * transposeInv3 g) with hY
  set T : MirabolicIndex ℚ → ℂ := fun i =>
    if ((mirabolicRep ℚ i : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) 1 1 = 0 then
      dualWhittakerFn3 W (mirabolicTranslate i * Y) else 0 with hT
  have hinner : ∀ z : AdeleRing (𝓞 ℚ) ℚ,
      (∫ y : AdeleRing (𝓞 ℚ) ℚ, (∑' i : MirabolicIndex ℚ, dualWhittakerFn3 W (mirabolicTranslate i *
          (weylPrime3 * transposeInv3 (radicalP21 ![z, y] * (iotaGL (diagUnitGL2 a) * g))))) ∂μbox) =
        ∑' i : MirabolicIndex ℚ, ψ (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) (phaseCoeff i) * z) * T i := by
    intro z
    rw [integral_box_dualSeries_radical_unweighted hψ hW hsum' g a z]
    refine tsum_congr fun i => ?_
    simp only [hT]
    split_ifs with h
    · exact dual_term_lower_eq hW i h z Y
    · simp
  simp_rw [hinner]
  have hTs : Summable T := by
    refine Summable.of_norm_bounded (summable_norm_iff.mpr (hsum' Y)) fun i => ?_
    simp only [hT]
    split_ifs <;> simp
  rw [integral_box_tsum_phase_rat hψ phaseCoeff T hTs]
  refine (tsum_congr fun i => ?_).trans tsum_zero
  simp only [hT]
  split_ifs with hc h11
  · exact absurd hc (phaseCoeff_ne_zero_of_apply_one_one_eq_zero i h11)
  · rfl
  · rfl

end Head

section Transport

open LanglandsTunnell.Converse

section Matrices

variable {K : Type*} [Field K]

private def dualModeMat (α b : Kˣ) : GL (Fin 2) K where
  val := !![0, (α : K) * b; (b : K), 0]
  inv := !![0, (b : K)⁻¹; ((α : K) * b)⁻¹, 0]
  val_inv := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
    field_simp
  inv_val := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
    field_simp

@[scoped simp] private theorem dualModeMat_coe (α b : Kˣ) :
    ((dualModeMat α b : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = !![0, (α : K) * b; (b : K), 0] :=
  rfl

private def primalModeMat (b α : Kˣ) : GL (Fin 2) K where
  val := !![0, (b : K); (α : K), 0]
  inv := !![0, (α : K)⁻¹; (b : K)⁻¹, 0]
  val_inv := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  inv_val := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

@[scoped simp] private theorem primalModeMat_coe (b α : Kˣ) :
    ((primalModeMat b α : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = !![0, (b : K); (α : K), 0] :=
  rfl

private def scalar3 (c : Kˣ) : GL (Fin 3) K := Matrix.GeneralLinearGroup.scalar (Fin 3) c

private theorem scalar3_coe (c : Kˣ) :
    ((scalar3 c : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = Matrix.scalar (Fin 3) (c : K) :=
  rfl

private theorem longWeyl3_mul_transposeInv3_iotaGL_dualModeMat_mul_weylPrime3 (α b : Kˣ) :
    longWeyl3 * transposeInv3 (iotaGL (dualModeMat α b)) * weylPrime3 =
      scalar3 (α * b)⁻¹ * iotaGL (primalModeMat (α * b) α) := by
  refine Units.ext ?_
  have hτ : ((transposeInv3 (iotaGL (dualModeMat α b)) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      (embedMat2 (!![0, (b : K)⁻¹; ((α : K) * b)⁻¹, 0] : Matrix (Fin 2) (Fin 2) K))ᵀ :=
    rfl
  rw [Units.val_mul, Units.val_mul, Units.val_mul, hτ, longWeyl3_coe, weylPrime3_coe, scalar3_coe, coe_iotaGL,
    primalModeMat_coe]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [embedMat2, Matrix.mul_apply, Fin.sum_univ_three, Matrix.vecHead, Matrix.vecTail, Matrix.scalar_apply,
      Matrix.diagonal_apply] <;> field_simp

end Matrices

section TransposeDual

variable {A : Type*} [CommRing A]

private theorem dualWhittakerFn3_mul_weylPrime3_mul_transposeInv3 {R : Type*} (W : GL (Fin 3) A → R)
    (h g : GL (Fin 3) A) :
    dualWhittakerFn3 W (h * (weylPrime3 * transposeInv3 g)) = W (longWeyl3 * transposeInv3 h * weylPrime3 * g) := by
  rw [dualWhittakerFn3_apply, transposeInv3_mul_aux1, transposeInv3_mul_aux1, transposeInv3_weylPrime3,
    transposeInv3_transposeInv3_aux1, mul_assoc (longWeyl3 * transposeInv3 h), mul_assoc]

end TransposeDual

section RationalPoints

private theorem globalPointsGL_transposeInv3_aux1 (h : GL (Fin 3) ℚ) :
    globalPointsGL 3 (𝓞 ℚ) ℚ (transposeInv3 h) = transposeInv3 (globalPointsGL 3 (𝓞 ℚ) ℚ h) := by
  refine Units.ext ?_
  have h1 : ((globalPointsGL 3 (𝓞 ℚ) ℚ h)⁻¹ : GL (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) = globalPointsGL 3 (𝓞 ℚ) ℚ h⁻¹ :=
    (map_inv (globalPointsGL 3 (𝓞 ℚ) ℚ) h).symm
  change ((((h⁻¹ : GL (Fin 3) ℚ) : Matrix (Fin 3) (Fin 3) ℚ))ᵀ).map (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ)) =
    ((((globalPointsGL 3 (𝓞 ℚ) ℚ h)⁻¹ : GL (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)))ᵀ
  rw [h1]
  ext i j
  rfl

private theorem globalPointsGL_longWeyl3 : globalPointsGL 3 (𝓞 ℚ) ℚ longWeyl3 = longWeyl3 := by
  refine Units.ext ?_
  ext i j
  fin_cases i <;> fin_cases j <;> simp [globalPointsGL]

private theorem globalPointsGL_weylPrime3_aux1 : globalPointsGL 3 (𝓞 ℚ) ℚ weylPrime3 = weylPrime3 := by
  refine Units.ext ?_
  ext i j
  fin_cases i <;> fin_cases j <;> simp [globalPointsGL]

private theorem globalPointsGL_iotaGL_aux1 (h : GL (Fin 2) ℚ) :
    globalPointsGL 3 (𝓞 ℚ) ℚ (iotaGL h) = iotaGL (globalPoints (𝓞 ℚ) ℚ h) := by
  refine Units.ext ?_
  ext i j
  fin_cases i <;> fin_cases j <;> simp [globalPointsGL, globalPoints, embedMat2]

private theorem globalPointsGL_scalar3 (c : ℚˣ) :
    globalPointsGL 3 (𝓞 ℚ) ℚ (scalar3 c) =
      centralScalarGL 3 (𝓞 ℚ) ℚ (Units.map (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ)) c) := by
  refine Units.ext ?_
  have hc : ((centralScalarGL 3 (𝓞 ℚ) ℚ (Units.map (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ)) c) :
      GL (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) :
      Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) = Matrix.scalar (Fin 3) (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) c) := rfl
  rw [hc]
  ext i j
  by_cases hij : i = j <;> simp [globalPointsGL, scalar3_coe, Matrix.scalar_apply, Matrix.algebraMap_matrix_apply, hij]

private theorem dualWhittakerFn3_dualModeMat_eq (W : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (α b : ℚˣ)
    (g : AdelicGL 3 (𝓞 ℚ) ℚ) :
    dualWhittakerFn3 W
        (iotaGL (globalPoints (𝓞 ℚ) ℚ (dualModeMat α b)) * (weylPrime3 * transposeInv3 g)) =
      W (centralScalarGL 3 (𝓞 ℚ) ℚ (Units.map (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ)) (α * b)⁻¹) *
        (iotaGL (globalPoints (𝓞 ℚ) ℚ (primalModeMat (α * b) α)) * g)) := by
  rw [dualWhittakerFn3_mul_weylPrime3_mul_transposeInv3, ← globalPointsGL_iotaGL_aux1, ←
      globalPointsGL_transposeInv3_aux1,
    ← globalPointsGL_longWeyl3, ← globalPointsGL_weylPrime3_aux1, ← map_mul, ← map_mul,
    longWeyl3_mul_transposeInv3_iotaGL_dualModeMat_mul_weylPrime3, map_mul, globalPointsGL_scalar3,
    globalPointsGL_iotaGL_aux1, mul_assoc]

end RationalPoints

section Head

private theorem tsum_dualWhittakerFn3_dualModeMat_eq_tsum_primalModeMat
    (ω : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (hω : IsAdmissibleTwist ℚ ω)
    (W : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)
    (hWω : ∀ (z : (AdeleRing (𝓞 ℚ) ℚ)ˣ) (g : AdelicGL 3 (𝓞 ℚ) ℚ),
      W (centralScalarGL 3 (𝓞 ℚ) ℚ z * g) = (ω z : ℂ) * W g)
    (α : ℚˣ) (g : AdelicGL 3 (𝓞 ℚ) ℚ) :
    ∑' b : ℚˣ, dualWhittakerFn3 W
        (iotaGL (globalPoints (𝓞 ℚ) ℚ (dualModeMat α b)) * (weylPrime3 * transposeInv3 g)) =
      ∑' b : ℚˣ, W (iotaGL (globalPoints (𝓞 ℚ) ℚ (primalModeMat b α)) * g) := by
  have hterm : ∀ b : ℚˣ, dualWhittakerFn3 W
      (iotaGL (globalPoints (𝓞 ℚ) ℚ (dualModeMat α b)) * (weylPrime3 * transposeInv3 g)) =
        W (iotaGL (globalPoints (𝓞 ℚ) ℚ (primalModeMat (α * b) α)) * g) := by
    intro b
    have h1 : ω (Units.map (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ)) (α * b)⁻¹) = 1 := hω.1 _
    rw [dualWhittakerFn3_dualModeMat_eq, hWω, h1, Units.val_one, one_mul]
  simp_rw [hterm]
  exact (Equiv.mulLeft α).tsum_eq fun b => W (iotaGL (globalPoints (𝓞 ℚ) ℚ (primalModeMat b α)) * g)

end Head

end Transport

section ModeMatrices

variable {K : Type*} [Field K]

private theorem unipotentGL2_mul_apply_one (x : K) (g : GL (Fin 2) K) (j : Fin 2) :
    ((AutomorphicForm.unipotentGL2 x * g : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 1 j =
      (g : Matrix (Fin 2) (Fin 2) K) 1 j := by
  fin_cases j <;> simp [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two]

private theorem unipotentGL2_mul_apply_zero_one (x : K) (g : GL (Fin 2) K) :
    ((AutomorphicForm.unipotentGL2 x * g : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 0 1 =
      (g : Matrix (Fin 2) (Fin 2) K) 0 1 + x * (g : Matrix (Fin 2) (Fin 2) K) 1 1 := by
  simp [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two]

private theorem exists_mirabolicRep_mk_eq (M : GL (Fin 2) K) :
    ∃ x : K, mirabolicRep K (Quotient.mk _ M) = AutomorphicForm.unipotentGL2 x * M := by
  have h := QuotientGroup.rightRel_apply.mp (Quotient.mk_out (s := QuotientGroup.rightRel
    (AutomorphicForm.unipotentGL2Hom (R := K)).range) M)
  obtain ⟨u, hu⟩ := h
  refine ⟨-(Multiplicative.toAdd u), ?_⟩
  have hu' : AutomorphicForm.unipotentGL2Hom u = M * (mirabolicRep K (Quotient.mk _ M))⁻¹ := hu
  have hinv : (AutomorphicForm.unipotentGL2Hom u)⁻¹ = AutomorphicForm.unipotentGL2 (-(Multiplicative.toAdd u)) := by
    rw [← map_inv]
    rfl
  calc mirabolicRep K (Quotient.mk _ M)
      = (AutomorphicForm.unipotentGL2Hom u)⁻¹ * (AutomorphicForm.unipotentGL2Hom u *
          mirabolicRep K (Quotient.mk _ M)) := by rw [inv_mul_cancel_left]
    _ = AutomorphicForm.unipotentGL2 (-(Multiplicative.toAdd u)) * M := by
          rw [hinv, hu', inv_mul_cancel_right]

private theorem eq_unipotentGL2_mul_dualModeMat (α : Kˣ) (g : GL (Fin 2) K)
    (h11 : (g : Matrix (Fin 2) (Fin 2) K) 1 1 = 0) (h10 : (g : Matrix (Fin 2) (Fin 2) K) 1 0 ≠ 0)
    (h01 : (g : Matrix (Fin 2) (Fin 2) K) 0 1 = α * (g : Matrix (Fin 2) (Fin 2) K) 1 0) :
    g = AutomorphicForm.unipotentGL2 ((g : Matrix (Fin 2) (Fin 2) K) 0 0 / (g : Matrix (Fin 2) (Fin 2) K) 1 0) *
      dualModeMat α (Units.mk0 _ h10) := by
  refine Units.ext ?_
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two, h11, h01]
  field_simp

private theorem apply_one_zero_ne_zero (g : GL (Fin 2) K) (h11 : (g : Matrix (Fin 2) (Fin 2) K) 1 1 = 0) :
    (g : Matrix (Fin 2) (Fin 2) K) 1 0 ≠ 0 := by
  intro h10
  have hdet : (g : Matrix (Fin 2) (Fin 2) K).det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det _).mp g.isUnit).ne_zero
  apply hdet
  rw [Matrix.det_fin_two, h11, h10]
  ring

end ModeMatrices

section DualModeFibre

private def dualModeIdx (α b : ℚˣ) : MirabolicIndex ℚ :=
  Quotient.mk _ (dualModeMat α b)

private theorem rep_dualModeIdx_apply_one_one (α b : ℚˣ) :
    ((mirabolicRep ℚ (dualModeIdx α b) : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) 1 1 = 0 := by
  obtain ⟨x, hx⟩ := exists_mirabolicRep_mk_eq (dualModeMat α b)
  rw [dualModeIdx, hx, unipotentGL2_mul_apply_one, dualModeMat_coe]
  simp

private theorem rep_dualModeIdx_apply_one_zero (α b : ℚˣ) :
    ((mirabolicRep ℚ (dualModeIdx α b) : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) 1 0 = b := by
  obtain ⟨x, hx⟩ := exists_mirabolicRep_mk_eq (dualModeMat α b)
  rw [dualModeIdx, hx, unipotentGL2_mul_apply_one, dualModeMat_coe]
  simp

private theorem rep_dualModeIdx_apply_zero_one (α b : ℚˣ) :
    ((mirabolicRep ℚ (dualModeIdx α b) : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) 0 1 = α * b := by
  obtain ⟨x, hx⟩ := exists_mirabolicRep_mk_eq (dualModeMat α b)
  rw [dualModeIdx, hx, unipotentGL2_mul_apply_zero_one, dualModeMat_coe]
  simp

private theorem phaseCoeff_dualModeIdx (α b : ℚˣ) : phaseCoeff (dualModeIdx α b) = α := by
  rw [phaseCoeff, rep_dualModeIdx_apply_zero_one, rep_dualModeIdx_apply_one_zero]
  exact mul_div_cancel_right₀ _ b.ne_zero

private abbrev IsDualModeClass (α : ℚˣ) (i : MirabolicIndex ℚ) : Prop :=
  ((mirabolicRep ℚ i : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) 1 1 = 0 ∧ phaseCoeff i = α

private noncomputable def dualModeEquiv (α : ℚˣ) :
    {i : MirabolicIndex ℚ // IsDualModeClass α i} ≃ ℚˣ where
  toFun i := Units.mk0 _ (apply_one_zero_ne_zero (mirabolicRep ℚ i.1) i.2.1)
  invFun b := ⟨dualModeIdx α b, rep_dualModeIdx_apply_one_one α b, phaseCoeff_dualModeIdx α b⟩
  left_inv i := by
    apply Subtype.ext
    change dualModeIdx α _ = i.1
    have h10 := apply_one_zero_ne_zero (mirabolicRep ℚ i.1) i.2.1
    have h01 : ((mirabolicRep ℚ i.1 : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) 0 1 =
        α * ((mirabolicRep ℚ i.1 : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) 1 0 :=
      (div_eq_iff h10).mp i.2.2
    rw [dualModeIdx]
    conv_rhs => rw [← mirabolicRep_spec ℚ i.1, eq_unipotentGL2_mul_dualModeMat α (mirabolicRep ℚ i.1) i.2.1 h10 h01,
      mirabolic_mk_unipotent_mul]
  right_inv b := by
    apply Units.ext
    exact rep_dualModeIdx_apply_one_zero α b

private theorem tsum_ite_dualMode_eq_tsum (α : ℚˣ) (F : MirabolicIndex ℚ → ℂ) :
    (∑' i : MirabolicIndex ℚ, if IsDualModeClass α i then F i else 0) = ∑' b : ℚˣ, F (dualModeIdx α b) := by
  have h := tsum_subtype {i : MirabolicIndex ℚ | IsDualModeClass α i} F
  simp only [Set.indicator_apply, Set.mem_setOf_eq] at h
  rw [← h]
  exact ((dualModeEquiv α).symm.tsum_eq fun i => F i.1).symm

private theorem iotaGL_globalPoints_unipotentGL2 (x : ℚ) :
    iotaGL (globalPoints (𝓞 ℚ) ℚ (AutomorphicForm.unipotentGL2 x)) =
      upperUnipotent3 (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) x) 0 0 := by
  refine Units.ext ?_
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [coe_iotaGL, embedMat2, globalPoints, Matrix.GeneralLinearGroup.map_apply]

private theorem dualMode_term_eq {ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ} (hψ : IsGlobalAddChar ℚ ψ)
    {W : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ} (hW : IsGL3PsiWhittakerFn ψ W) (α b : ℚˣ) (Y : AdelicGL 3 (𝓞 ℚ) ℚ) :
    dualWhittakerFn3 W (mirabolicTranslate (dualModeIdx α b) * Y) =
      dualWhittakerFn3 W (iotaGL (globalPoints (𝓞 ℚ) ℚ (dualModeMat α b)) * Y) := by
  have hdual := isGL3PsiWhittakerFn_dualWhittakerFn3_aux1 ψ hW
  obtain ⟨x, hx⟩ := exists_mirabolicRep_mk_eq (dualModeMat α b)
  show dualWhittakerFn3 W (iotaGL (globalPoints (𝓞 ℚ) ℚ (mirabolicRep ℚ (dualModeIdx α b))) * _) = _
  rw [dualModeIdx, hx, map_mul, map_mul, iotaGL_globalPoints_unipotentGL2, mul_assoc, hdual, add_zero,
    AddChar.inv_apply, ← map_neg, hψ.principalInvariant, one_mul]

private theorem diagUnitGL2_one_aux1 : diagUnitGL2 (1 : (AdeleRing (𝓞 ℚ) ℚ)ˣ) = 1 := by
  refine Units.ext ?_
  ext i j
  fin_cases i <;> fin_cases j <;> simp [diagUnitGL2]

end DualModeFibre

section Head

private theorem box_integral_dualSeries_radical_mode_eq_tsum_dualModeMat
    (ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ) (hψ : IsGlobalAddChar ℚ ψ)
    (W : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hW : IsGL3PsiWhittakerFn ψ W)
    (hsum' : ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ,
      Summable fun i : MirabolicIndex ℚ => dualWhittakerFn3 W (mirabolicTranslate i * g))
    (α : ℚˣ) (X : AdelicGL 3 (𝓞 ℚ) ℚ) :
    ∫ z : AdeleRing (𝓞 ℚ) ℚ, ∫ y : AdeleRing (𝓞 ℚ) ℚ,
        (∑' i : MirabolicIndex ℚ, dualWhittakerFn3 W (mirabolicTranslate i *
          (weylPrime3 * transposeInv3 (radicalP21 ![z, y] * X)))) * ψ (-(algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) α * z))
      ∂μbox ∂μbox =
    ∑' b : ℚˣ, dualWhittakerFn3 W
      (iotaGL (globalPoints (𝓞 ℚ) ℚ (dualModeMat α b)) * (weylPrime3 * transposeInv3 X)) := by
  set Y : AdelicGL 3 (𝓞 ℚ) ℚ := weylPrime3 * transposeInv3 X with hY
  set T : MirabolicIndex ℚ → ℂ := fun i =>
    if ((mirabolicRep ℚ i : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) 1 1 = 0 then
      dualWhittakerFn3 W (mirabolicTranslate i * Y) else 0 with hT
  have hinner : ∀ z : AdeleRing (𝓞 ℚ) ℚ,
      (∫ y : AdeleRing (𝓞 ℚ) ℚ, (∑' i : MirabolicIndex ℚ, dualWhittakerFn3 W (mirabolicTranslate i *
          (weylPrime3 * transposeInv3 (radicalP21 ![z, y] * X)))) *
            ψ (-(algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) α * z)) ∂μbox) =
        (∑' i : MirabolicIndex ℚ, ψ (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) (phaseCoeff i) * z) * T i) *
          ψ (-(algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) α * z)) := by
    intro z
    rw [integral_mul_const]
    congr 1
    have h := integral_box_dualSeries_radical_unweighted hψ hW hsum' X 1 z
    simp only [inv_one, diagUnitGL2_one_aux1, map_one, one_mul] at h
    rw [h]
    refine tsum_congr fun i => ?_
    simp only [hT]
    split_ifs with hi
    · exact dual_term_lower_eq hW i hi z Y
    · simp
  simp_rw [hinner]
  have hTs : Summable T := by
    refine Summable.of_norm_bounded (summable_norm_iff.mpr (hsum' Y)) fun i => ?_
    simp only [hT]
    split_ifs <;> simp
  have hshift : ∀ z : AdeleRing (𝓞 ℚ) ℚ,
      (∑' i : MirabolicIndex ℚ, ψ (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) (phaseCoeff i) * z) * T i) *
          ψ (-(algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) α * z)) =
        ∑' i : MirabolicIndex ℚ, ψ (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) (phaseCoeff i - α) * z) * T i := by
    intro z
    rw [← tsum_mul_right]
    refine tsum_congr fun i => ?_
    rw [map_sub, sub_mul, sub_eq_add_neg, AddChar.map_add_eq_mul]
    ring
  simp_rw [hshift]
  rw [integral_box_tsum_phase_rat hψ (fun i => phaseCoeff i - α) T hTs]
  have hform : ∀ i : MirabolicIndex ℚ, (if phaseCoeff i - α = 0 then T i else 0) =
      if IsDualModeClass α i then dualWhittakerFn3 W (mirabolicTranslate i * Y) else 0 := by
    intro i
    by_cases h1 : phaseCoeff i = α <;>
      by_cases h2 : ((mirabolicRep ℚ i : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) 1 1 = 0 <;>
        simp [hT, IsDualModeClass, h1, h2, sub_eq_zero]
  simp_rw [hform]
  rw [tsum_ite_dualMode_eq_tsum α fun i => dualWhittakerFn3 W (mirabolicTranslate i * Y)]
  exact tsum_congr fun b => dualMode_term_eq hψ hW α b Y

end Head

section PrimalMatrices

variable {K : Type*} [Field K]

private theorem eq_unipotentGL2_mul_primalModeMat (α : Kˣ) (g : GL (Fin 2) K)
    (h11 : (g : Matrix (Fin 2) (Fin 2) K) 1 1 = 0) (h10 : (g : Matrix (Fin 2) (Fin 2) K) 1 0 = α)
    (h01 : (g : Matrix (Fin 2) (Fin 2) K) 0 1 ≠ 0) :
    g = AutomorphicForm.unipotentGL2 ((g : Matrix (Fin 2) (Fin 2) K) 0 0 / α) * primalModeMat (Units.mk0 _ h01) α := by
  refine Units.ext ?_
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two, h11, h10]

private theorem apply_zero_one_ne_zero (g : GL (Fin 2) K) (h11 : (g : Matrix (Fin 2) (Fin 2) K) 1 1 = 0) :
    (g : Matrix (Fin 2) (Fin 2) K) 0 1 ≠ 0 := by
  intro h01
  have hdet : (g : Matrix (Fin 2) (Fin 2) K).det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det _).mp g.isUnit).ne_zero
  apply hdet
  rw [Matrix.det_fin_two, h11, h01]
  ring

end PrimalMatrices

section PrimalModeFibre

private noncomputable abbrev repMat (i : MirabolicIndex ℚ) : Matrix (Fin 2) (Fin 2) ℚ :=
  ((mirabolicRep ℚ i : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ)

private abbrev IsPrimalModeClass (α : ℚˣ) (i : MirabolicIndex ℚ) : Prop :=
  repMat i 1 1 = 0 ∧ repMat i 1 0 = α

private def primalModeIdx (b α : ℚˣ) : MirabolicIndex ℚ :=
  Quotient.mk _ (primalModeMat b α)

private theorem rep_primalModeIdx_apply_one_one (b α : ℚˣ) :
    repMat (primalModeIdx b α) 1 1 = 0 := by
  obtain ⟨x, hx⟩ := exists_mirabolicRep_mk_eq (primalModeMat b α)
  dsimp only [repMat]
  rw [primalModeIdx, hx, unipotentGL2_mul_apply_one, primalModeMat_coe]
  simp

private theorem rep_primalModeIdx_apply_one_zero (b α : ℚˣ) :
    repMat (primalModeIdx b α) 1 0 = α := by
  obtain ⟨x, hx⟩ := exists_mirabolicRep_mk_eq (primalModeMat b α)
  dsimp only [repMat]
  rw [primalModeIdx, hx, unipotentGL2_mul_apply_one, primalModeMat_coe]
  simp

private theorem rep_primalModeIdx_apply_zero_one (b α : ℚˣ) :
    repMat (primalModeIdx b α) 0 1 = b := by
  obtain ⟨x, hx⟩ := exists_mirabolicRep_mk_eq (primalModeMat b α)
  dsimp only [repMat]
  rw [primalModeIdx, hx, unipotentGL2_mul_apply_zero_one, primalModeMat_coe]
  simp

private noncomputable def primalModeEquiv (α : ℚˣ) : {i : MirabolicIndex ℚ // IsPrimalModeClass α i} ≃ ℚˣ where
  toFun i := Units.mk0 _ (apply_zero_one_ne_zero (mirabolicRep ℚ i.1) i.2.1)
  invFun b := ⟨primalModeIdx b α, rep_primalModeIdx_apply_one_one b α, rep_primalModeIdx_apply_one_zero b α⟩
  left_inv i := by
    apply Subtype.ext
    change primalModeIdx _ α = i.1
    rw [primalModeIdx]
    conv_rhs => rw [← mirabolicRep_spec ℚ i.1,
      eq_unipotentGL2_mul_primalModeMat α (mirabolicRep ℚ i.1) i.2.1 i.2.2
        (apply_zero_one_ne_zero (mirabolicRep ℚ i.1) i.2.1),
      mirabolic_mk_unipotent_mul]
  right_inv b := by
    apply Units.ext
    exact rep_primalModeIdx_apply_zero_one b α

private theorem tsum_ite_primalMode_eq_tsum (α : ℚˣ) (F : MirabolicIndex ℚ → ℂ) :
    (∑' i : MirabolicIndex ℚ, if IsPrimalModeClass α i then F i else 0) = ∑' b : ℚˣ, F (primalModeIdx b α) := by
  have h := tsum_subtype {i : MirabolicIndex ℚ | IsPrimalModeClass α i} F
  simp only [Set.indicator_apply, Set.mem_setOf_eq] at h
  rw [← h]
  exact ((primalModeEquiv α).symm.tsum_eq fun i => F i.1).symm

private theorem primalMode_term_eq {ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ} (hψ : IsGlobalAddChar ℚ ψ)
    {W : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ} (hW : IsGL3PsiWhittakerFn ψ W) (b α : ℚˣ) (X : AdelicGL 3 (𝓞 ℚ) ℚ) :
    W (mirabolicTranslate (primalModeIdx b α) * X) = W (iotaGL (globalPoints (𝓞 ℚ) ℚ (primalModeMat b α)) * X) := by
  obtain ⟨x, hx⟩ := exists_mirabolicRep_mk_eq (primalModeMat b α)
  show W (iotaGL (globalPoints (𝓞 ℚ) ℚ (mirabolicRep ℚ (primalModeIdx b α))) * _) = _
  rw [primalModeIdx, hx, map_mul, map_mul, iotaGL_globalPoints_unipotentGL2, mul_assoc, hW, add_zero,
    hψ.principalInvariant, one_mul]

end PrimalModeFibre

section PrimalTerms

private theorem globalPoints_apply_aux1 (h : GL (Fin 2) ℚ) (k l : Fin 2) :
    ((globalPoints (𝓞 ℚ) ℚ h : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) k l =
      algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) ((h : Matrix (Fin 2) (Fin 2) ℚ) k l) :=
  Matrix.GeneralLinearGroup.map_apply _ _ _ _

private theorem primal_term_radical_eq {ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ} {W : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ}
    (hW : IsGL3PsiWhittakerFn ψ W) (i : MirabolicIndex ℚ) (z y : AdeleRing (𝓞 ℚ) ℚ) (X : AdelicGL 3 (𝓞 ℚ) ℚ) :
    W (mirabolicTranslate i * (radicalP21 ![z, y] * X)) =
      ψ (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) (repMat i 1 0) * z + algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) (repMat i 1 1) * y) *
        W (mirabolicTranslate i * X) := by
  have hrad : (radicalP21 ![z, y] : GL (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) = upperUnipotent3 0 y z := rfl
  show W (iotaGL (globalPoints (𝓞 ℚ) ℚ (mirabolicRep ℚ i)) * (radicalP21 ![z, y] * X)) =
    _ * W (iotaGL (globalPoints (𝓞 ℚ) ℚ (mirabolicRep ℚ i)) * X)
  rw [hrad, ← mul_assoc, iotaGL_mul_upperUnipotent3_zero_aux1, mul_assoc, hW, zero_add, globalPoints_apply_aux1,
    globalPoints_apply_aux1]

end PrimalTerms

section Head

private theorem box_integral_mirabolicSeries_radical_mode_eq_tsum_primalModeMat
    (ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ) (hψ : IsGlobalAddChar ℚ ψ)
    (W : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hW : IsGL3PsiWhittakerFn ψ W)
    (hsum : ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ, Summable fun i : MirabolicIndex ℚ => W (mirabolicTranslate i * g))
    (α : ℚˣ) (X : AdelicGL 3 (𝓞 ℚ) ℚ) :
    ∫ z : AdeleRing (𝓞 ℚ) ℚ, ∫ y : AdeleRing (𝓞 ℚ) ℚ,
        (∑' i : MirabolicIndex ℚ, W (mirabolicTranslate i * (radicalP21 ![z, y] * X))) *
          ψ (-(algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) α * z))
      ∂μbox ∂μbox =
    ∑' b : ℚˣ, W (iotaGL (globalPoints (𝓞 ℚ) ℚ (primalModeMat b α)) * X) := by
  have hψ1 : ∀ t : AdeleRing (𝓞 ℚ) ℚ, ‖ψ t‖ = 1 := fun t => by
    simpa using NumberField.AdelicFourier.norm_apply_eq_one_of_isGlobalAddChar ℚ hψ t
  set C : MirabolicIndex ℚ → ℂ := fun i => W (mirabolicTranslate i * X) with hC
  have hCs : Summable C := hsum X
  set T' : MirabolicIndex ℚ → ℂ := fun i => if repMat i 1 1 = 0 then C i else 0 with hT'
  have hT's : Summable T' := by
    refine Summable.of_norm_bounded (summable_norm_iff.mpr hCs) fun i => ?_
    simp only [hT']
    split_ifs <;> simp
  have hinner : ∀ z : AdeleRing (𝓞 ℚ) ℚ,
      (∫ y : AdeleRing (𝓞 ℚ) ℚ, (∑' i : MirabolicIndex ℚ, W (mirabolicTranslate i * (radicalP21 ![z, y] * X))) *
          ψ (-(algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) α * z)) ∂μbox) =
        (∑' i : MirabolicIndex ℚ, ψ (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) (repMat i 1 0) * z) * T' i) *
          ψ (-(algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) α * z)) := by
    intro z
    rw [integral_mul_const]
    congr 1
    set T : MirabolicIndex ℚ → ℂ := fun i => ψ (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) (repMat i 1 0) * z) * C i with hT
    have hTs : Summable T := by
      refine Summable.of_norm_bounded (summable_norm_iff.mpr hCs) fun i => ?_
      simp only [hT]
      rw [norm_mul, hψ1, one_mul]
    have hfun : (fun y : AdeleRing (𝓞 ℚ) ℚ =>
          ∑' i : MirabolicIndex ℚ, W (mirabolicTranslate i * (radicalP21 ![z, y] * X))) =
        fun y => ∑' i : MirabolicIndex ℚ, ψ (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) (repMat i 1 1) * y) * T i := by
      funext y
      refine tsum_congr fun i => ?_
      rw [primal_term_radical_eq hW, AddChar.map_add_eq_mul]
      simp only [hT, hC]
      ring
    rw [hfun, integral_box_tsum_phase_rat hψ (fun i => repMat i 1 1) T hTs]
    refine tsum_congr fun i => ?_
    simp only [hT, hT']
    split_ifs <;> simp
  simp_rw [hinner]
  have hshift : ∀ z : AdeleRing (𝓞 ℚ) ℚ,
      (∑' i : MirabolicIndex ℚ, ψ (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) (repMat i 1 0) * z) * T' i) *
          ψ (-(algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) α * z)) =
        ∑' i : MirabolicIndex ℚ, ψ (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) (repMat i 1 0 - α) * z) * T' i := by
    intro z
    rw [← tsum_mul_right]
    refine tsum_congr fun i => ?_
    rw [map_sub, sub_mul, sub_eq_add_neg, AddChar.map_add_eq_mul]
    ring
  simp_rw [hshift]
  rw [integral_box_tsum_phase_rat hψ (fun i => repMat i 1 0 - α) T' hT's]
  have hform : ∀ i : MirabolicIndex ℚ, (if repMat i 1 0 - α = 0 then T' i else 0) =
      if IsPrimalModeClass α i then C i else 0 := by
    intro i
    by_cases h1 : repMat i 1 0 = α <;> by_cases h2 : repMat i 1 1 = 0 <;>
      simp [hT', IsPrimalModeClass, h1, h2, sub_eq_zero]
  simp_rw [hform]
  rw [tsum_ite_primalMode_eq_tsum α C]
  exact tsum_congr fun b => primalMode_term_eq hψ hW b α X

end Head
end
end LanglandsTunnell.CubicInduction
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_mirabolicSeries_eq_dual_of_radicalCoefficient_eq.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_mirabolicSeries_eq_dual_of_radicalCoefficient_eq.LanglandsTunnell.CubicInduction"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_mirabolicSeries_eq_dual_of_radicalCoefficient_eq.LanglandsTunnell"

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "Converse.IsAdmissibleTwist TateLocal.addCharLevel TateLocal.localBorel TateLocal.borelSpace_localBorel TateLocal.integersPositiveCompacts TateLocal.coe_integersPositiveCompacts TateLocal.selfDualHaarAt TateLocal.higherUnitsAt TateLocal.forall_eq_one_and_exists_ne_one_of_addCharLevel"
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "matrixFin_ext matrixAdele_ext localMatN mapMatrix_localMatN_self mapMatrix_localMatN_of_ne finMatN mapMatrix_arch_finMatN mapMatrix_fin_finMatN localToAdelic3 converseCongruenceSet3 HasVanishingUnipotentIntegralAlong IsCongruenceEquivariantAlong lowerUnipotent21 longWeyl3 longWeyl3_coe dualWhittakerFn3 dualWhittakerFn3_apply weylPrime3 weylPrime3_coe weylPrime3_mul_self transposeInv3_weylPrime3 weylPrime3_mul_transposeInv3_radicalP21_mul_weylPrime3 IsGL3PsiWhittakerFn transposeInv3 IsCuspidalAlongP21 psiLoc mirabolicTranslate AdelicGL globalPointsGL centralScalarGL upperUnipotent3 upperUnipotent3_coe upperUnipotent3_zero radicalP21 radicalP21_zero radicalP21_coe radicalP21_add embedMat2 iotaGL coe_iotaGL iota MirabolicIndex mirabolicRep mirabolicRep_spec mirabolic_mk_unipotent_mul localMaximalCompact3 componentAtN archComponentN componentAt3 archComponent3 LocalGL3 cosetSum IsCosetEigenfunction IsRightInvariant diagUnitGL2 diagHom diagHom_apply isCuspidalAlongP21_mirabolicSeries"
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"
section
open IsDedekindDomain NumberField NumberField.AdelicHaar AutomorphicForm Matrix MeasureTheory
open scoped NNReal ENNReal Pointwise ProbabilityTheory
attribute [local instance] NumberField.Idele.ideleBorel NumberField.AdelicHaar.adeleBorel

section Transport

variable {A : Type*} [CommRing A]

private theorem iotaGL_mul_upperUnipotent3_zero_aux2 (h : GL (Fin 2) A) (y z : A) :
    iotaGL h * upperUnipotent3 0 y z =
      upperUnipotent3 0 ((h : Matrix (Fin 2) (Fin 2) A) 1 0 * z + (h : Matrix (Fin 2) (Fin 2) A) 1 1 * y)
        ((h : Matrix (Fin 2) (Fin 2) A) 0 0 * z + (h : Matrix (Fin 2) (Fin 2) A) 0 1 * y) * iotaGL h := by
  refine Units.ext ?_
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Units.val_mul, coe_iotaGL, embedMat2, Matrix.mul_apply, Fin.sum_univ_three]

end Transport
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_mirabolicSeries_eq_dual_of_radicalCoefficient_eq.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_mirabolicSeries_eq_dual_of_radicalCoefficient_eq.LanglandsTunnell.CubicInduction"

section PrimalTerms

private noncomputable abbrev repMat_aux2 (i : MirabolicIndex ℚ) : Matrix (Fin 2) (Fin 2) ℚ :=
  ((mirabolicRep ℚ i : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ)

private theorem globalPoints_apply_aux2 (h : GL (Fin 2) ℚ) (k l : Fin 2) :
    ((globalPoints (𝓞 ℚ) ℚ h : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) k l =
      algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) ((h : Matrix (Fin 2) (Fin 2) ℚ) k l) :=
  Matrix.GeneralLinearGroup.map_apply _ _ _ _

private theorem primal_term_radical_eq_aux2 {ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ} {W : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ}
    (hW : IsGL3PsiWhittakerFn ψ W) (i : MirabolicIndex ℚ) (z y : AdeleRing (𝓞 ℚ) ℚ) (X : AdelicGL 3 (𝓞 ℚ) ℚ) :
    W (mirabolicTranslate i * (radicalP21 ![z, y] * X)) =
      ψ (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) (repMat_aux2 i 1 0) * z + algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) (repMat_aux2 i 1
          1) * y) *
        W (mirabolicTranslate i * X) := by
  have hrad : (radicalP21 ![z, y] : GL (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) = upperUnipotent3 0 y z := rfl
  show W (iotaGL (globalPoints (𝓞 ℚ) ℚ (mirabolicRep ℚ i)) * (radicalP21 ![z, y] * X)) =
    _ * W (iotaGL (globalPoints (𝓞 ℚ) ℚ (mirabolicRep ℚ i)) * X)
  rw [hrad, ← mul_assoc, iotaGL_mul_upperUnipotent3_zero_aux2, mul_assoc, hW, zero_add, globalPoints_apply_aux2,
    globalPoints_apply_aux2]

private theorem continuous_mirabolicSeries_radical {ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ} (hψ : IsGlobalAddChar ℚ ψ)
    {W : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ} (hW : IsGL3PsiWhittakerFn ψ W) (X : AdelicGL 3 (𝓞 ℚ) ℚ)
    (hs : Summable fun i : MirabolicIndex ℚ => W (mirabolicTranslate i * X)) :
    Continuous fun p : AdeleRing (𝓞 ℚ) ℚ × AdeleRing (𝓞 ℚ) ℚ =>
      ∑' i : MirabolicIndex ℚ, W (mirabolicTranslate i * (radicalP21 ![p.1, p.2] * X)) := by
  have hone : ∀ t : AdeleRing (𝓞 ℚ) ℚ, ‖ψ t‖ = 1 := fun t => by
    simpa using NumberField.AdelicFourier.norm_apply_eq_one_of_isGlobalAddChar ℚ hψ t
  have hfun : (fun p : AdeleRing (𝓞 ℚ) ℚ × AdeleRing (𝓞 ℚ) ℚ =>
        ∑' i : MirabolicIndex ℚ, W (mirabolicTranslate i * (radicalP21 ![p.1, p.2] * X))) =
      fun p => ∑' i : MirabolicIndex ℚ,
        ψ (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) (repMat_aux2 i 1 0) * p.1 +
            algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) (repMat_aux2 i 1 1) * p.2) * W (mirabolicTranslate i * X) := by
    funext p
    exact tsum_congr fun i => primal_term_radical_eq_aux2 hW i p.1 p.2 X
  rw [hfun]
  refine continuous_tsum (fun i => ?_) (summable_norm_iff.mpr hs) fun i p => ?_
  · exact (hψ.continuous.comp
      ((continuous_const.mul continuous_fst).add (continuous_const.mul continuous_snd))).mul continuous_const
  · simp [hone]

end PrimalTerms
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_mirabolicSeries_eq_dual_of_radicalCoefficient_eq.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_mirabolicSeries_eq_dual_of_radicalCoefficient_eq.LanglandsTunnell.CubicInduction"
end
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_mirabolicSeries_eq_dual_of_radicalCoefficient_eq.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_mirabolicSeries_eq_dual_of_radicalCoefficient_eq.LanglandsTunnell.CubicInduction"
end LanglandsTunnell.CubicInduction
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_mirabolicSeries_eq_dual_of_radicalCoefficient_eq.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_mirabolicSeries_eq_dual_of_radicalCoefficient_eq.LanglandsTunnell.CubicInduction"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_mirabolicSeries_eq_dual_of_radicalCoefficient_eq.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_mirabolicSeries_eq_dual_of_radicalCoefficient_eq.LanglandsTunnell.CubicInduction"

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "Converse.IsAdmissibleTwist TateLocal.addCharLevel TateLocal.localBorel TateLocal.borelSpace_localBorel TateLocal.integersPositiveCompacts TateLocal.coe_integersPositiveCompacts TateLocal.selfDualHaarAt TateLocal.higherUnitsAt TateLocal.forall_eq_one_and_exists_ne_one_of_addCharLevel"
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "matrixFin_ext matrixAdele_ext localMatN mapMatrix_localMatN_self mapMatrix_localMatN_of_ne finMatN mapMatrix_arch_finMatN mapMatrix_fin_finMatN localToAdelic3 converseCongruenceSet3 HasVanishingUnipotentIntegralAlong IsCongruenceEquivariantAlong lowerUnipotent21 longWeyl3 longWeyl3_coe dualWhittakerFn3 dualWhittakerFn3_apply weylPrime3 weylPrime3_coe weylPrime3_mul_self transposeInv3_weylPrime3 weylPrime3_mul_transposeInv3_radicalP21_mul_weylPrime3 IsGL3PsiWhittakerFn transposeInv3 IsCuspidalAlongP21 psiLoc mirabolicTranslate AdelicGL globalPointsGL centralScalarGL upperUnipotent3 upperUnipotent3_coe upperUnipotent3_zero radicalP21 radicalP21_zero radicalP21_coe radicalP21_add embedMat2 iotaGL coe_iotaGL iota MirabolicIndex mirabolicRep mirabolicRep_spec mirabolic_mk_unipotent_mul localMaximalCompact3 componentAtN archComponentN componentAt3 archComponent3 LocalGL3 cosetSum IsCosetEigenfunction IsRightInvariant diagUnitGL2 diagHom diagHom_apply isCuspidalAlongP21_mirabolicSeries"
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"
noncomputable section
p2m_open "Matrix IsDedekindDomain NumberField MeasureTheory AutomorphicForm LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_mirabolicSeries_eq_dual_of_radicalCoefficient_eq.LanglandsTunnell.CubicInduction"

private def mirabolicSeries (W : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (g : AdelicGL 3 (𝓞 ℚ) ℚ) : ℂ :=
  ∑' i : MirabolicIndex ℚ, W (mirabolicTranslate i * g)

private theorem mirabolicSeries_apply (W : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (g : AdelicGL 3 (𝓞 ℚ) ℚ) :
    mirabolicSeries W g = ∑' i : MirabolicIndex ℚ, W (mirabolicTranslate i * g) :=
  rfl

private theorem centralScalarGL_mul_comm (z : (AdeleRing (𝓞 ℚ) ℚ)ˣ) (x : AdelicGL 3 (𝓞 ℚ) ℚ) :
    centralScalarGL 3 (𝓞 ℚ) ℚ z * x = x * centralScalarGL 3 (𝓞 ℚ) ℚ z := by
  apply Units.ext
  ext i j
  simp [centralScalarGL, Matrix.GeneralLinearGroup.scalar, Matrix.diagonal_mul, Matrix.mul_diagonal, mul_comm]

private theorem mirabolicTranslate_mul_centralScalarGL (i : MirabolicIndex ℚ) (z : (AdeleRing (𝓞 ℚ) ℚ)ˣ) :
    mirabolicTranslate i * centralScalarGL 3 (𝓞 ℚ) ℚ z = centralScalarGL 3 (𝓞 ℚ) ℚ z * mirabolicTranslate i :=
  (centralScalarGL_mul_comm z _).symm

variable {W : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ}

private theorem mirabolicSeries_centralScalarGL_mul {ω : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ}
    (hWω : ∀ (z : (AdeleRing (𝓞 ℚ) ℚ)ˣ) (g : AdelicGL 3 (𝓞 ℚ) ℚ),
      W (centralScalarGL 3 (𝓞 ℚ) ℚ z * g) = (ω z : ℂ) * W g)
    (z : (AdeleRing (𝓞 ℚ) ℚ)ˣ) (g : AdelicGL 3 (𝓞 ℚ) ℚ) :
    mirabolicSeries W (centralScalarGL 3 (𝓞 ℚ) ℚ z * g) = (ω z : ℂ) * mirabolicSeries W g := by
  simp only [mirabolicSeries_apply]
  rw [← tsum_mul_left]
  congr 1
  funext i
  rw [← mul_assoc, mirabolicTranslate_mul_centralScalarGL, mul_assoc, hWω]

private theorem isCongruenceEquivariantAlong_mirabolicSeries {v : HeightOneSpectrum (𝓞 ℚ)} {n : ℕ}
    {χ : (v.adicCompletion ℚ)ˣ →* ℂˣ} (hWK : IsCongruenceEquivariantAlong v n χ W) :
    IsCongruenceEquivariantAlong v n χ (mirabolicSeries W) := by
  intro k hk u hu g
  simp only [mirabolicSeries_apply]
  rw [← tsum_mul_left]
  congr 1
  funext i
  rw [← mul_assoc, hWK k hk u hu]

private theorem isRightInvariant_mirabolicSeries {H : Subgroup (AdelicGL 3 (𝓞 ℚ) ℚ)} (hinv : IsRightInvariant H W) :
    IsRightInvariant H (mirabolicSeries W) := by
  intro g u hu
  simp only [mirabolicSeries_apply]
  congr 1
  funext i
  rw [← mul_assoc, hinv _ u hu]

private theorem isCosetEigenfunction_mirabolicSeries
    (hsum : ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ, Summable fun i : MirabolicIndex ℚ => W (mirabolicTranslate i * g))
    {H : Subgroup (AdelicGL 3 (𝓞 ℚ) ℚ)} {t : AdelicGL 3 (𝓞 ℚ) ℚ} {lam : ℂ}
    (hT : IsCosetEigenfunction H t W lam) : IsCosetEigenfunction H t (mirabolicSeries W) lam := by
  intro ι _ reps hreps g
  simp only [cosetSum, mirabolicSeries_apply]
  have hs : ∀ j ∈ (Finset.univ : Finset ι),
      Summable fun i : MirabolicIndex ℚ => W (mirabolicTranslate i * (g * reps j)) :=
    fun j _ => hsum (g * reps j)
  rw [← Summable.tsum_finsetSum hs, ← tsum_mul_left]
  congr 1
  funext i
  have h := hT ι reps hreps (mirabolicTranslate i * g)
  simp only [cosetSum, mul_assoc] at h
  exact h

private theorem exists_unipotentGL2_mul_of_mk_eq {X Y : GL (Fin 2) ℚ}
    (h : (Quotient.mk _ X : MirabolicIndex ℚ) = Quotient.mk _ Y) :
    ∃ t : ℚ, Y = AutomorphicForm.unipotentGL2 t * X := by
  have h' := QuotientGroup.rightRel_apply.mp (Quotient.exact h)
  obtain ⟨t, ht⟩ := h'
  refine ⟨t.toAdd, ?_⟩
  have ht' : AutomorphicForm.unipotentGL2 t.toAdd = Y * X⁻¹ := ht
  rw [ht', inv_mul_cancel_right]

private theorem iota_globalPoints_unipotentGL2 (t : ℚ) :
    iota (𝓞 ℚ) ℚ (globalPoints (𝓞 ℚ) ℚ (AutomorphicForm.unipotentGL2 t)) =
      upperUnipotent3 (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) t) 0 0 := by
  refine Units.ext ?_
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [iota, coe_iotaGL, embedMat2, globalPoints, Matrix.GeneralLinearGroup.map_apply]

private theorem apply_iota_globalPoints_unipotentGL2_mul {ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ} (hψ : IsGlobalAddChar ℚ ψ)
    (hW : IsGL3PsiWhittakerFn ψ W) (t : ℚ) (X : GL (Fin 2) ℚ) (y : AdelicGL 3 (𝓞 ℚ) ℚ) :
    W (iota (𝓞 ℚ) ℚ (globalPoints (𝓞 ℚ) ℚ (AutomorphicForm.unipotentGL2 t * X)) * y) =
      W (iota (𝓞 ℚ) ℚ (globalPoints (𝓞 ℚ) ℚ X) * y) := by
  rw [map_mul, map_mul, iota_globalPoints_unipotentGL2, mul_assoc, hW _ _ _ _, add_zero, hψ.principalInvariant t,
    one_mul]

private theorem apply_mirabolicTranslate_mk_mul {ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ} (hψ : IsGlobalAddChar ℚ ψ)
    (hW : IsGL3PsiWhittakerFn ψ W) (X : GL (Fin 2) ℚ) (y : AdelicGL 3 (𝓞 ℚ) ℚ) :
    W (mirabolicTranslate (Quotient.mk _ X) * y) = W (iota (𝓞 ℚ) ℚ (globalPoints (𝓞 ℚ) ℚ X) * y) := by
  obtain ⟨t, ht⟩ := exists_unipotentGL2_mul_of_mk_eq (mirabolicRep_spec ℚ (Quotient.mk _ X)).symm
  rw [mirabolicTranslate, ht, apply_iota_globalPoints_unipotentGL2_mul hψ hW]

private def mirabolicIndexMulRight (A : GL (Fin 2) ℚ) : MirabolicIndex ℚ ≃ MirabolicIndex ℚ where
  toFun := Quotient.map' (· * A) fun X Y hXY => by
    rw [QuotientGroup.rightRel_apply] at hXY ⊢
    simpa only [_root_.mul_inv_rev, mul_assoc, mul_inv_cancel_left] using hXY
  invFun := Quotient.map' (· * A⁻¹) fun X Y hXY => by
    rw [QuotientGroup.rightRel_apply] at hXY ⊢
    simpa only [_root_.mul_inv_rev, inv_inv, mul_assoc, inv_mul_cancel_left] using hXY
  left_inv c := by
    induction c using Quotient.inductionOn with
    | h X => exact congrArg (Quotient.mk _) (mul_inv_cancel_right X A)
  right_inv c := by
    induction c using Quotient.inductionOn with
    | h X => exact congrArg (Quotient.mk _) (inv_mul_cancel_right X A)

private theorem mirabolicIndexMulRight_apply (A : GL (Fin 2) ℚ) (c : MirabolicIndex ℚ) :
    mirabolicIndexMulRight A c = Quotient.mk _ (mirabolicRep ℚ c * A) := by
  conv_lhs => rw [← mirabolicRep_spec ℚ c]
  rfl

private theorem mirabolicSeries_iota_globalPoints_mul {ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ} (hψ : IsGlobalAddChar ℚ ψ)
    (hW : IsGL3PsiWhittakerFn ψ W) (A : GL (Fin 2) ℚ) (g : AdelicGL 3 (𝓞 ℚ) ℚ) :
    mirabolicSeries W (iota (𝓞 ℚ) ℚ (globalPoints (𝓞 ℚ) ℚ A) * g) = mirabolicSeries W g := by
  simp only [mirabolicSeries_apply]
  rw [← (mirabolicIndexMulRight A).tsum_eq fun c => W (mirabolicTranslate c * g)]
  congr 1
  funext c
  beta_reduce
  rw [mirabolicIndexMulRight_apply, apply_mirabolicTranslate_mk_mul hψ hW, map_mul, map_mul, mirabolicTranslate,
    ← mul_assoc]

private theorem iotaGL_mul_upperUnipotent3_zero {A : Type*} [CommRing A] (h : GL (Fin 2) A) (y z : A) :
    iotaGL h * upperUnipotent3 0 y z =
      upperUnipotent3 0 ((h : Matrix (Fin 2) (Fin 2) A) 1 0 * z + (h : Matrix (Fin 2) (Fin 2) A) 1 1 * y)
        ((h : Matrix (Fin 2) (Fin 2) A) 0 0 * z + (h : Matrix (Fin 2) (Fin 2) A) 0 1 * y) * iotaGL h := by
  apply Units.ext
  ext i j
  rw [Units.val_mul, Units.val_mul, coe_iotaGL, upperUnipotent3_coe, upperUnipotent3_coe]
  fin_cases i <;> fin_cases j <;> simp [embedMat2, Matrix.mul_apply, Fin.sum_univ_three]
  all_goals ring

private theorem globalPoints_apply (X : GL (Fin 2) ℚ) (a b : Fin 2) :
    ((globalPoints (𝓞 ℚ) ℚ X : AdelicGL2 (𝓞 ℚ) ℚ) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) a b =
      algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) ((X : Matrix (Fin 2) (Fin 2) ℚ) a b) :=
  Matrix.GeneralLinearGroup.map_apply _ _ _ _

private theorem mirabolicSeries_upperUnipotent3_algebraMap_mul {ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ}
    (hψ : IsGlobalAddChar ℚ ψ) (hW : IsGL3PsiWhittakerFn ψ W) (y z : ℚ) (g : AdelicGL 3 (𝓞 ℚ) ℚ) :
    mirabolicSeries W
        (upperUnipotent3 0 (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) y) (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) z) * g) =
      mirabolicSeries W g := by
  simp only [mirabolicSeries_apply]
  congr 1
  funext i
  rw [← mul_assoc, show mirabolicTranslate i = iotaGL (globalPoints (𝓞 ℚ) ℚ (mirabolicRep ℚ i)) from rfl,
    iotaGL_mul_upperUnipotent3_zero, mul_assoc, hW, zero_add, globalPoints_apply, globalPoints_apply,
    ← map_mul (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ)), ← map_mul (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ)),
    ← map_add (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ)), hψ.principalInvariant, one_mul]

private theorem globalPointsGL_scalar (q : ℚˣ) :
    globalPointsGL 3 (𝓞 ℚ) ℚ (Matrix.GeneralLinearGroup.scalar (Fin 3) q) =
      centralScalarGL 3 (𝓞 ℚ) ℚ (Units.map (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ)).toMonoidHom q) := by
  apply Units.ext
  ext i j
  rw [globalPointsGL, Matrix.GeneralLinearGroup.map_apply, centralScalarGL]
  by_cases h : i = j
  · subst h
    simp [Matrix.algebraMap_matrix_apply]
  · simp [h, Matrix.algebraMap_matrix_apply]

private theorem globalPointsGL_upperUnipotent3 (x y z : ℚ) :
    globalPointsGL 3 (𝓞 ℚ) ℚ (upperUnipotent3 x y z) =
      upperUnipotent3 (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) x) (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) y)
        (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) z) := by
  apply Units.ext
  ext i j
  rw [globalPointsGL, Matrix.GeneralLinearGroup.map_apply, upperUnipotent3_coe, upperUnipotent3_coe]
  fin_cases i <;> fin_cases j <;> simp

private theorem globalPointsGL_iotaGL (X : GL (Fin 2) ℚ) :
    globalPointsGL 3 (𝓞 ℚ) ℚ (iotaGL X) = iota (𝓞 ℚ) ℚ (globalPoints (𝓞 ℚ) ℚ X) := by
  apply Units.ext
  ext i j
  rw [globalPointsGL, Matrix.GeneralLinearGroup.map_apply]
  fin_cases i <;> fin_cases j <;> simp [iota, embedMat2, globalPoints_apply]

private theorem globalPointsGL_eq_of_parabolic (γ : GL (Fin 3) ℚ)
    (h0 : (γ : Matrix (Fin 3) (Fin 3) ℚ) 2 0 = 0) (h1 : (γ : Matrix (Fin 3) (Fin 3) ℚ) 2 1 = 0) :
    ∃ (y z : ℚ) (t : ℚˣ) (A : GL (Fin 2) ℚ),
      globalPointsGL 3 (𝓞 ℚ) ℚ γ =
        upperUnipotent3 0 (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) y) (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) z) *
          (centralScalarGL 3 (𝓞 ℚ) ℚ (Units.map (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ)).toMonoidHom t) *
            iota (𝓞 ℚ) ℚ (globalPoints (𝓞 ℚ) ℚ A)) := by
  set M : Matrix (Fin 3) (Fin 3) ℚ := (γ : Matrix (Fin 3) (Fin 3) ℚ) with hM
  have hdet : M.det ≠ 0 := by
    rw [hM, ← Matrix.GeneralLinearGroup.val_det_apply]
    exact (Matrix.GeneralLinearGroup.det γ).ne_zero
  have hsplit : M.det = M 2 2 * (M 0 0 * M 1 1 - M 0 1 * M 1 0) := by
    rw [Matrix.det_fin_three, h0, h1]
    ring
  have ht : M 2 2 ≠ 0 := fun h => hdet (by rw [hsplit, h, zero_mul])
  have hblock : M 0 0 * M 1 1 - M 0 1 * M 1 0 ≠ 0 := fun h => hdet (by rw [hsplit, h, mul_zero])
  have hA : (!![M 0 0 / M 2 2, M 0 1 / M 2 2; M 1 0 / M 2 2, M 1 1 / M 2 2] : Matrix (Fin 2) (Fin 2) ℚ).det ≠ 0 := by
    rw [Matrix.det_fin_two_of, show M 0 0 / M 2 2 * (M 1 1 / M 2 2) - M 0 1 / M 2 2 * (M 1 0 / M 2 2) =
      (M 0 0 * M 1 1 - M 0 1 * M 1 0) / (M 2 2 * M 2 2) by ring]
    exact div_ne_zero hblock (mul_ne_zero ht ht)
  refine ⟨M 1 2 / M 2 2, M 0 2 / M 2 2, Units.mk0 (M 2 2) ht, Matrix.GeneralLinearGroup.mkOfDetNeZero _ hA, ?_⟩

  have hγ : γ = upperUnipotent3 0 (M 1 2 / M 2 2) (M 0 2 / M 2 2) *
      (Matrix.GeneralLinearGroup.scalar (Fin 3) (Units.mk0 (M 2 2) ht) *
        iotaGL (Matrix.GeneralLinearGroup.mkOfDetNeZero _ hA)) := by
    have hAval : ((Matrix.GeneralLinearGroup.mkOfDetNeZero _ hA : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) =
        !![M 0 0 / M 2 2, M 0 1 / M 2 2; M 1 0 / M 2 2, M 1 1 / M 2 2] := rfl
    apply Units.ext
    ext i j
    rw [Units.val_mul, Units.val_mul, upperUnipotent3_coe, coe_iotaGL, hAval]
    fin_cases i <;> fin_cases j <;>
      simp [← hM, h0, h1, ht, embedMat2, Matrix.GeneralLinearGroup.scalar, Matrix.mul_apply, Fin.sum_univ_three]
    all_goals field_simp
  rw [hγ, map_mul, map_mul, globalPointsGL_upperUnipotent3, map_zero, globalPointsGL_scalar, globalPointsGL_iotaGL]

private theorem mirabolicSeries_globalPointsGL_mul_of_parabolic
    {ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ} (hψ : IsGlobalAddChar ℚ ψ) (hW : IsGL3PsiWhittakerFn ψ W)
    {ω : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ}
    (hWω : ∀ (z : (AdeleRing (𝓞 ℚ) ℚ)ˣ) (g : AdelicGL 3 (𝓞 ℚ) ℚ),
      W (centralScalarGL 3 (𝓞 ℚ) ℚ z * g) = (ω z : ℂ) * W g)
    (hω : ∀ q : ℚˣ, ω (Units.map (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ)).toMonoidHom q) = 1)
    (γ : GL (Fin 3) ℚ) (hγ0 : (γ : Matrix (Fin 3) (Fin 3) ℚ) 2 0 = 0) (hγ1 : (γ : Matrix (Fin 3) (Fin 3) ℚ) 2 1 = 0)
    (g : AdelicGL 3 (𝓞 ℚ) ℚ) :
    mirabolicSeries W (globalPointsGL 3 (𝓞 ℚ) ℚ γ * g) = mirabolicSeries W g := by
  obtain ⟨y, z, t, A, hγ⟩ := globalPointsGL_eq_of_parabolic γ hγ0 hγ1
  rw [hγ, mul_assoc, mirabolicSeries_upperUnipotent3_algebraMap_mul hψ hW, mul_assoc,
    mirabolicSeries_centralScalarGL_mul hWω, hω, Units.val_one, one_mul, mirabolicSeries_iota_globalPoints_mul hψ hW]
end
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_mirabolicSeries_eq_dual_of_radicalCoefficient_eq.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_mirabolicSeries_eq_dual_of_radicalCoefficient_eq.LanglandsTunnell.CubicInduction"
end LanglandsTunnell.CubicInduction
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_mirabolicSeries_eq_dual_of_radicalCoefficient_eq.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_mirabolicSeries_eq_dual_of_radicalCoefficient_eq.LanglandsTunnell.CubicInduction"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_mirabolicSeries_eq_dual_of_radicalCoefficient_eq.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_mirabolicSeries_eq_dual_of_radicalCoefficient_eq.LanglandsTunnell.CubicInduction"

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "Converse.IsAdmissibleTwist TateLocal.addCharLevel TateLocal.localBorel TateLocal.borelSpace_localBorel TateLocal.integersPositiveCompacts TateLocal.coe_integersPositiveCompacts TateLocal.selfDualHaarAt TateLocal.higherUnitsAt TateLocal.forall_eq_one_and_exists_ne_one_of_addCharLevel"
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "matrixFin_ext matrixAdele_ext localMatN mapMatrix_localMatN_self mapMatrix_localMatN_of_ne finMatN mapMatrix_arch_finMatN mapMatrix_fin_finMatN localToAdelic3 converseCongruenceSet3 HasVanishingUnipotentIntegralAlong IsCongruenceEquivariantAlong lowerUnipotent21 longWeyl3 longWeyl3_coe dualWhittakerFn3 dualWhittakerFn3_apply weylPrime3 weylPrime3_coe weylPrime3_mul_self transposeInv3_weylPrime3 weylPrime3_mul_transposeInv3_radicalP21_mul_weylPrime3 IsGL3PsiWhittakerFn transposeInv3 IsCuspidalAlongP21 psiLoc mirabolicTranslate AdelicGL globalPointsGL centralScalarGL upperUnipotent3 upperUnipotent3_coe upperUnipotent3_zero radicalP21 radicalP21_zero radicalP21_coe radicalP21_add embedMat2 iotaGL coe_iotaGL iota MirabolicIndex mirabolicRep mirabolicRep_spec mirabolic_mk_unipotent_mul localMaximalCompact3 componentAtN archComponentN componentAt3 archComponent3 LocalGL3 cosetSum IsCosetEigenfunction IsRightInvariant diagUnitGL2 diagHom diagHom_apply isCuspidalAlongP21_mirabolicSeries"
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"
section
open IsDedekindDomain NumberField NumberField.AdelicHaar AutomorphicForm MeasureTheory
open scoped ENNReal Pointwise ProbabilityTheory
attribute [local instance] NumberField.AdelicHaar.adeleBorel

section Quotient

private abbrev PrincipalQuotient : Type :=
  AdeleRing (𝓞 ℚ) ℚ ⧸ AdeleRing.principalSubgroup (𝓞 ℚ) ℚ

private theorem addChar_mul_algebraMap_add_aux4 {ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ}
    (hψ : IsPrincipalInvariantAddChar ℚ ψ) (β α : ℚ) (y : AdeleRing (𝓞 ℚ) ℚ) :
    ψ (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) β * (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) α + y)) =
      ψ (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) β * y) := by
  rw [mul_add, AddChar.map_add_eq_mul, ← map_mul (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ)), hψ (β * α), one_mul]

private theorem eq_zero_of_algebraMap_add_mem_adelicBox {u : AdeleRing (𝓞 ℚ) ℚ} (hu : u ∈ AdelicBox.adelicBox ℚ)
    {q : ℚ} (hq : algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) q + u ∈ AdelicBox.adelicBox ℚ) : q = 0 := by
  obtain ⟨k, -, huniq⟩ := AdelicBox.existsUnique_algebraMap_add_mem_adelicBox ℚ u
  have h0 : (0 : ℚ) = k := huniq 0 (by simpa using hu)
  rw [huniq q hq, ← h0]

private theorem discreteTopology_principalSubgroup : DiscreteTopology (AdeleRing.principalSubgroup (𝓞 ℚ) ℚ) := by
  obtain ⟨U, hUo, ⟨u, hu⟩, hUbox⟩ := AdelicBox.exists_isOpen_subset_adelicBox ℚ
  refine discreteTopology_of_isOpen_singleton_zero ?_
  refine isOpen_induced_iff.mpr
    ⟨(fun x : AdeleRing (𝓞 ℚ) ℚ => x + u) ⁻¹' U, hUo.preimage (continuous_id.add continuous_const), ?_⟩
  refine Set.ext fun γ => ?_
  simp only [Set.mem_preimage, Set.mem_singleton_iff]
  constructor
  · intro h
    obtain ⟨q, hq⟩ := RingHom.mem_range.mp γ.2
    rw [← hq] at h
    have hq0 := eq_zero_of_algebraMap_add_mem_adelicBox (hUbox hu) (hUbox h)
    apply Subtype.ext
    rw [← hq, hq0, map_zero]
    rfl
  · intro h
    rw [h]
    simpa using hu

private theorem countable_principalSubgroup_aux4 : Countable (AdeleRing.principalSubgroup (𝓞 ℚ) ℚ) := by
  refine Function.Surjective.countable (f := fun α : ℚ =>
    (⟨algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) α, ⟨α, rfl⟩⟩ : AdeleRing.principalSubgroup (𝓞 ℚ) ℚ)) ?_
  rintro ⟨x, hx⟩
  obtain ⟨α, rfl⟩ := RingHom.mem_range.mp hx
  exact ⟨α, rfl⟩

private theorem compactSpace_principalQuotient : CompactSpace PrincipalQuotient := by
  obtain ⟨C, hC, hboxC⟩ := AdelicBox.exists_isCompact_adelicBox_subset ℚ
  refine ⟨?_⟩
  have himg : IsCompact ((QuotientAddGroup.mk : AdeleRing (𝓞 ℚ) ℚ → PrincipalQuotient) '' C) :=
    hC.image QuotientAddGroup.continuous_mk
  convert himg using 1
  refine (Set.eq_univ_of_forall fun z => ?_).symm
  obtain ⟨v, rfl⟩ := QuotientAddGroup.mk_surjective z
  obtain ⟨k, hk, -⟩ := AdelicBox.existsUnique_algebraMap_add_mem_adelicBox ℚ v
  refine ⟨algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) k + v, hboxC hk, ?_⟩
  refine QuotientAddGroup.eq.mpr (RingHom.mem_range.mpr ⟨-k, ?_⟩)
  rw [map_neg]
  abel

private noncomputable def descend (f : AdeleRing (𝓞 ℚ) ℚ → ℂ)
    (hf : ∀ (q : ℚ) (x : AdeleRing (𝓞 ℚ) ℚ), f (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) q + x) = f x) :
    PrincipalQuotient → ℂ :=
  Quotient.lift f fun a b hab => by
    obtain ⟨q, hq⟩ := RingHom.mem_range.mp (QuotientAddGroup.leftRel_apply.mp hab)
    have hb : b = algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) q + a := by
      rw [hq]
      abel
    rw [hb, hf]

private theorem continuous_descend (f : AdeleRing (𝓞 ℚ) ℚ → ℂ) (hfc : Continuous f)
    (hf : ∀ (q : ℚ) (x : AdeleRing (𝓞 ℚ) ℚ), f (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) q + x) = f x) :
    Continuous (descend f hf) :=
  hfc.quotient_lift _

end Quotient
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_mirabolicSeries_eq_dual_of_radicalCoefficient_eq.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_mirabolicSeries_eq_dual_of_radicalCoefficient_eq.LanglandsTunnell.CubicInduction"

section CharacterAlgebra

variable {ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ}

private theorem addChar_ne_zero (hψ : IsGlobalAddChar ℚ ψ) (t : AdeleRing (𝓞 ℚ) ℚ) : ψ t ≠ 0 := by
  have h1 : ‖ψ t‖ = 1 := by simpa using NumberField.AdelicFourier.norm_apply_eq_one_of_isGlobalAddChar ℚ hψ t
  intro h0
  rw [h0, norm_zero] at h1
  exact zero_ne_one h1

private noncomputable def charQ (hψ : IsGlobalAddChar ℚ ψ) (α : ℚ) : C(PrincipalQuotient, ℂ) where
  toFun := descend (fun x => ψ (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) α * x))
    (fun q x => addChar_mul_algebraMap_add_aux4 hψ.principalInvariant α q x)
  continuous_toFun := continuous_descend _ (hψ.continuous.comp (continuous_const.mul continuous_id)) _

private theorem charQ_mk (hψ : IsGlobalAddChar ℚ ψ) (α : ℚ) (x : AdeleRing (𝓞 ℚ) ℚ) :
    charQ hψ α (x : PrincipalQuotient) = ψ (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) α * x) :=
  rfl

private theorem charQ_zero (hψ : IsGlobalAddChar ℚ ψ) : charQ hψ 0 = 1 := by
  refine ContinuousMap.ext fun z => ?_
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective z
  rw [charQ_mk, map_zero, zero_mul, AddChar.map_zero_eq_one]
  rfl

private theorem charQ_mul (hψ : IsGlobalAddChar ℚ ψ) (α β : ℚ) : charQ hψ α * charQ hψ β = charQ hψ (α + β) := by
  refine ContinuousMap.ext fun z => ?_
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective z
  rw [ContinuousMap.mul_apply, charQ_mk, charQ_mk, charQ_mk, map_add, add_mul, AddChar.map_add_eq_mul]

private theorem charQ_star (hψ : IsGlobalAddChar ℚ ψ) (α : ℚ) : star (charQ hψ α) = charQ hψ (-α) := by
  refine ContinuousMap.ext fun z => ?_
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective z
  rw [ContinuousMap.star_apply, charQ_mk, charQ_mk, map_neg, neg_mul, AddChar.map_neg_eq_inv, Complex.star_def,
    Complex.inv_eq_conj]
  simpa using NumberField.AdelicFourier.norm_apply_eq_one_of_isGlobalAddChar ℚ hψ _

private theorem mul_mem_charSpan (hψ : IsGlobalAddChar ℚ ψ) {a b : C(PrincipalQuotient, ℂ)}
    (ha : a ∈ Submodule.span ℂ (Set.range (charQ hψ))) (hb : b ∈ Submodule.span ℂ (Set.range (charQ hψ))) :
    a * b ∈ Submodule.span ℂ (Set.range (charQ hψ)) := by
  induction ha using Submodule.span_induction with
  | mem x hx =>
    induction hb using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨α, rfl⟩ := hx
      obtain ⟨β, rfl⟩ := hy
      rw [charQ_mul]
      exact Submodule.subset_span ⟨α + β, rfl⟩
    | zero =>
      rw [mul_zero]
      exact Submodule.zero_mem _
    | add y z _ _ hy hz =>
      rw [mul_add]
      exact Submodule.add_mem _ hy hz
    | smul c y _ hy =>
      rw [mul_smul_comm]
      exact Submodule.smul_mem _ c hy
  | zero =>
    rw [zero_mul]
    exact Submodule.zero_mem _
  | add x y _ _ hx hy =>
    rw [add_mul]
    exact Submodule.add_mem _ hx hy
  | smul c x _ hx =>
    rw [smul_mul_assoc]
    exact Submodule.smul_mem _ c hx

private theorem star_mem_charSpan (hψ : IsGlobalAddChar ℚ ψ) {a : C(PrincipalQuotient, ℂ)}
    (ha : a ∈ Submodule.span ℂ (Set.range (charQ hψ))) : star a ∈ Submodule.span ℂ (Set.range (charQ hψ)) := by
  induction ha using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨α, rfl⟩ := hx
    rw [charQ_star]
    exact Submodule.subset_span ⟨-α, rfl⟩
  | zero =>
    rw [star_zero]
    exact Submodule.zero_mem _
  | add x y _ _ hx hy =>
    rw [star_add]
    exact Submodule.add_mem _ hx hy
  | smul c x _ hx =>
    rw [star_smul]
    exact Submodule.smul_mem _ (star c) hx

private noncomputable def charSpan (hψ : IsGlobalAddChar ℚ ψ) : StarSubalgebra ℂ C(PrincipalQuotient, ℂ) where
  carrier := (Submodule.span ℂ (Set.range (charQ hψ)) : Set C(PrincipalQuotient, ℂ))
  mul_mem' ha hb := mul_mem_charSpan hψ ha hb
  one_mem' := by
    rw [SetLike.mem_coe, ← charQ_zero hψ]
    exact Submodule.subset_span ⟨0, rfl⟩
  add_mem' ha hb := Submodule.add_mem _ ha hb
  zero_mem' := Submodule.zero_mem _
  algebraMap_mem' r := by
    rw [SetLike.mem_coe, Algebra.algebraMap_eq_smul_one, ← charQ_zero hψ]
    exact Submodule.smul_mem _ r (Submodule.subset_span ⟨0, rfl⟩)
  star_mem' ha := star_mem_charSpan hψ ha

private theorem mem_charSpan_iff (hψ : IsGlobalAddChar ℚ ψ) (a : C(PrincipalQuotient, ℂ)) :
    a ∈ charSpan hψ ↔ a ∈ Submodule.span ℂ (Set.range (charQ hψ)) :=
  Iff.rfl

private theorem charSpan_separatesPoints (hψ : IsGlobalAddChar ℚ ψ) : (charSpan hψ).SeparatesPoints := by
  intro z w hzw
  obtain ⟨u, rfl⟩ := QuotientAddGroup.mk_surjective z
  obtain ⟨v, rfl⟩ := QuotientAddGroup.mk_surjective w
  have hnot : ¬ ∀ ξ : ℚ, ψ ((-u + v) * algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) ξ) = 1 := fun hall =>
    hzw (QuotientAddGroup.eq.mpr
      (NumberField.AdelicFourier.mem_range_algebraMap_of_forall_apply_mul_eq_one ℚ hψ (-u + v) hall))
  obtain ⟨ξ, hξ⟩ := not_forall.mp hnot
  refine ⟨charQ hψ ξ, ⟨charQ hψ ξ, (mem_charSpan_iff hψ _).mpr (Submodule.subset_span ⟨ξ, rfl⟩), rfl⟩, ?_⟩
  intro heq
  apply hξ
  rw [charQ_mk, charQ_mk] at heq
  rw [mul_comm, mul_add, mul_neg, AddChar.map_add_eq_mul, AddChar.map_neg_eq_inv, ← heq,
    inv_mul_cancel₀ (addChar_ne_zero hψ _)]

private theorem integral_mul_eq_zero_of_mem_charSpan (hψ : IsGlobalAddChar ℚ ψ) [MeasurableSpace PrincipalQuotient]
    [BorelSpace PrincipalQuotient] [CompactSpace PrincipalQuotient] (μ : Measure PrincipalQuotient) [IsFiniteMeasure μ]
    (β : C(PrincipalQuotient, ℂ))
    (h0 : ∀ α : ℚ, ∫ z, charQ hψ α z * β z ∂μ = 0) {g : C(PrincipalQuotient, ℂ)} (hg : g ∈ charSpan hψ) :
    ∫ z, g z * β z ∂μ = 0 := by
  have hi : ∀ g : C(PrincipalQuotient, ℂ), Integrable (fun z => g z * β z) μ := fun g =>
    (g.continuous.mul β.continuous).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  rw [mem_charSpan_iff] at hg
  induction hg using Submodule.span_induction with
  | mem g hg =>
    obtain ⟨α, rfl⟩ := hg
    exact h0 α
  | zero => simp
  | add g₁ g₂ _ _ h₁ h₂ =>
    simp only [ContinuousMap.add_apply, add_mul]
    rw [integral_add (hi g₁) (hi g₂), h₁, h₂, add_zero]
  | smul c g _ hg =>
    simp only [ContinuousMap.smul_apply, smul_mul_assoc]
    rw [integral_smul, hg, smul_zero]

end CharacterAlgebra
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_mirabolicSeries_eq_dual_of_radicalCoefficient_eq.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_mirabolicSeries_eq_dual_of_radicalCoefficient_eq.LanglandsTunnell.CubicInduction"

section Head

private theorem eq_zero_of_forall_integral_box_mul_addChar_eq_zero
    (ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ) (hψ : IsGlobalAddChar ℚ ψ) (f : AdeleRing (𝓞 ℚ) ℚ → ℂ) (hfc : Continuous f)
    (hfp : ∀ (q : ℚ) (x : AdeleRing (𝓞 ℚ) ℚ), f (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) q + x) = f x)
    (hcoef : ∀ α : ℚ, ∫ x : AdeleRing (𝓞 ℚ) ℚ, f x * ψ (-(algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) α * x)) ∂μbox = 0)
    (x : AdeleRing (𝓞 ℚ) ℚ) : f x = 0 := by
  haveI := borelSpace_adeleBorel (𝓞 ℚ) ℚ
  haveI := isAddHaarMeasure_adelicAddHaar (𝓞 ℚ) ℚ
  haveI := AdelicBox.isProbabilityMeasure_cond_adelicBox ℚ
  haveI := discreteTopology_principalSubgroup
  haveI := countable_principalSubgroup_aux4
  haveI := compactSpace_principalQuotient
  letI : MeasurableSpace PrincipalQuotient := borel _
  haveI : BorelSpace PrincipalQuotient := ⟨rfl⟩
  have hmk : Measurable (QuotientAddGroup.mk : AdeleRing (𝓞 ℚ) ℚ → PrincipalQuotient) :=
    QuotientAddGroup.continuous_mk.measurable
  set μ : Measure PrincipalQuotient :=
    Measure.map (QuotientAddGroup.mk : AdeleRing (𝓞 ℚ) ℚ → PrincipalQuotient) μbox with hμ
  haveI : IsFiniteMeasure μ := Measure.isFiniteMeasure_map _ _
  let β : C(PrincipalQuotient, ℂ) := ⟨descend f hfp, continuous_descend f hfc hfp⟩
  have h0 : ∀ α : ℚ, ∫ z, charQ hψ α z * β z ∂μ = 0 := by
    intro α
    rw [hμ, integral_map (f := fun w => charQ hψ α w * β w) hmk.aemeasurable
      ((charQ hψ α).continuous.mul β.continuous).aestronglyMeasurable]
    have hα := hcoef (-α)
    simp only [map_neg, neg_mul, neg_neg] at hα
    rw [← hα]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    show ψ (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) α * y) * f y = f y * ψ (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) α * y)
    ring
  have hae : (β : PrincipalQuotient → ℂ) =ᵐ[μ] 0 :=
    ContinuousMap.ae_eq_zero_of_forall_mem_starSubalgebra_integral_mul_eq_zero μ (charSpan hψ)
      (charSpan_separatesPoints hψ) β fun g hg => integral_mul_eq_zero_of_mem_charSpan hψ μ β h0 hg
  have hae' : ∀ᵐ y ∂(μbox), f y = 0 := by
    have h := ae_of_ae_map (p := fun z => (β : PrincipalQuotient → ℂ) z = (0 : PrincipalQuotient → ℂ) z)
      hmk.aemeasurable (hμ ▸ hae)
    filter_upwards [h] with y hy
    exact hy
  set S : Set (AdeleRing (𝓞 ℚ) ℚ) := {y | f y ≠ 0} with hS
  have hSo : IsOpen S := isOpen_ne_fun hfc continuous_const
  have hScond : μbox S = 0 := ae_iff.mp hae'
  have hSbox : adelicAddHaar (𝓞 ℚ) ℚ (S ∩ AdelicBox.adelicBox ℚ) = 0 := by
    rw [ProbabilityTheory.cond_apply (AdelicBox.measurableSet_adelicBox ℚ)] at hScond
    rcases mul_eq_zero.mp hScond with h | h
    · exact absurd h (ENNReal.inv_ne_zero.mpr (AdelicBox.adelicAddHaar_adelicBox_lt_top ℚ).ne)
    · rwa [Set.inter_comm]
  have hinv : ∀ γ : AdeleRing.principalSubgroup (𝓞 ℚ) ℚ, γ +ᵥ S = S := by
    intro γ
    refine Set.ext fun y => ?_
    rw [Set.mem_vadd_set_iff_neg_vadd_mem]
    obtain ⟨q, hq⟩ := RingHom.mem_range.mp γ.2
    show f (((-γ : AdeleRing.principalSubgroup (𝓞 ℚ) ℚ) : AdeleRing (𝓞 ℚ) ℚ) + y) ≠ 0 ↔ f y ≠ 0
    rw [AddSubgroup.coe_neg, ← hq, ← map_neg, hfp]
  have hSnull : adelicAddHaar (𝓞 ℚ) ℚ S = 0 :=
    (AdelicBox.isAddFundamentalDomain_adelicBox_adelicAddHaar ℚ).measure_zero_of_invariant S hinv hSbox
  have hSempty : S = ∅ := (hSo.measure_eq_zero_iff _).mp hSnull
  by_contra hx
  have hxS : x ∈ S := hx
  rw [hSempty] at hxS
  exact hxS

end Head
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_mirabolicSeries_eq_dual_of_radicalCoefficient_eq.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_mirabolicSeries_eq_dual_of_radicalCoefficient_eq.LanglandsTunnell.CubicInduction"

section Iterated

private theorem integrable_slice_mul_addChar {ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ} (hψ : IsGlobalAddChar ℚ ψ)
    {F : AdeleRing (𝓞 ℚ) ℚ → AdeleRing (𝓞 ℚ) ℚ → ℂ}
    (hFc : Continuous fun p : AdeleRing (𝓞 ℚ) ℚ × AdeleRing (𝓞 ℚ) ℚ => F p.1 p.2) (β : ℚ) (z : AdeleRing (𝓞 ℚ) ℚ) :
    Integrable (fun y => F z y * ψ (-(algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) β * y))) μbox := by
  haveI := borelSpace_adeleBorel (𝓞 ℚ) ℚ
  haveI := AdelicBox.isProbabilityMeasure_cond_adelicBox ℚ
  obtain ⟨C, hC, hboxC⟩ := AdelicBox.exists_isCompact_adelicBox_subset ℚ
  have hFz : Continuous fun y => F z y := hFc.comp (by fun_prop : Continuous fun y : AdeleRing (𝓞 ℚ) ℚ => (z, y))
  have hwc : Continuous fun y : AdeleRing (𝓞 ℚ) ℚ => ψ (-(algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) β * y)) :=
    hψ.continuous.comp (continuous_const.mul continuous_id).neg
  obtain ⟨M, hM⟩ := hC.exists_bound_of_continuousOn hFz.continuousOn
  refine (integrable_const M).mono' (hFz.mul hwc).aestronglyMeasurable ?_
  filter_upwards [(ProbabilityTheory.ae_cond_mem (AdelicBox.measurableSet_adelicBox ℚ)).mono fun w hw => hboxC hw]
    with w hw
  rw [norm_mul, (by simpa using NumberField.AdelicFourier.norm_apply_eq_one_of_isGlobalAddChar ℚ hψ _ : ‖ψ _‖ = 1),
    mul_one]
  exact hM w hw

private theorem continuous_integral_slice_mul_addChar {ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ} (hψ : IsGlobalAddChar ℚ ψ)
    {F : AdeleRing (𝓞 ℚ) ℚ → AdeleRing (𝓞 ℚ) ℚ → ℂ}
    (hFc : Continuous fun p : AdeleRing (𝓞 ℚ) ℚ × AdeleRing (𝓞 ℚ) ℚ => F p.1 p.2) (β : ℚ) :
    Continuous fun z => ∫ w, F z w * ψ (-(algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) β * w)) ∂μbox := by
  haveI := borelSpace_adeleBorel (𝓞 ℚ) ℚ
  haveI := AdelicBox.isProbabilityMeasure_cond_adelicBox ℚ
  have hψ1 : ∀ t : AdeleRing (𝓞 ℚ) ℚ, ‖ψ t‖ = 1 := fun t => by
    simpa using NumberField.AdelicFourier.norm_apply_eq_one_of_isGlobalAddChar ℚ hψ t
  obtain ⟨C, hC, hboxC⟩ := AdelicBox.exists_isCompact_adelicBox_subset ℚ
  have hmem : ∀ᵐ w ∂(μbox), w ∈ C :=
    (ProbabilityTheory.ae_cond_mem (AdelicBox.measurableSet_adelicBox ℚ)).mono fun w hw => hboxC hw
  refine continuous_iff_continuousAt.mpr fun z₀ => ?_
  refine Metric.tendsto_nhds.mpr fun ε hε => ?_
  have hev : ∀ᶠ z in nhds z₀, ∀ w ∈ C, ‖F z w - F z₀ w‖ < ε / 2 := by
    refine hC.eventually_forall_of_forall_eventually fun w _ => ?_
    have hc : Continuous fun p : AdeleRing (𝓞 ℚ) ℚ × AdeleRing (𝓞 ℚ) ℚ => ‖F p.1 p.2 - F z₀ p.2‖ :=
      (hFc.sub (hFc.comp (by fun_prop : Continuous fun p : AdeleRing (𝓞 ℚ) ℚ × AdeleRing (𝓞 ℚ) ℚ => (z₀, p.2)))).norm
    have h0 : ‖F (z₀, w).1 (z₀, w).2 - F z₀ (z₀, w).2‖ < ε / 2 := by
      simpa using half_pos hε
    exact (hc.tendsto (z₀, w)).eventually (gt_mem_nhds h0)
  filter_upwards [hev] with z hz
  rw [dist_eq_norm,
    ← integral_sub (integrable_slice_mul_addChar hψ hFc β z) (integrable_slice_mul_addChar hψ hFc β z₀)]
  have hb : ∀ᵐ w ∂(μbox), ‖F z w * ψ (-(algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) β * w)) -
      F z₀ w * ψ (-(algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) β * w))‖ ≤ ε / 2 := by
    filter_upwards [hmem] with w hw
    rw [← sub_mul, norm_mul, hψ1, mul_one]
    exact (hz w hw).le
  have hle := norm_integral_le_of_norm_le_const hb
  refine lt_of_le_of_lt ?_ (half_lt_self hε)
  simpa using hle

private theorem eq_zero_of_forall_integral_box_box_mul_addChar_eq_zero
    (ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ) (hψ : IsGlobalAddChar ℚ ψ) (F : AdeleRing (𝓞 ℚ) ℚ → AdeleRing (𝓞 ℚ) ℚ → ℂ)
    (hFc : Continuous fun p : AdeleRing (𝓞 ℚ) ℚ × AdeleRing (𝓞 ℚ) ℚ => F p.1 p.2)
    (hF₁ : ∀ (q : ℚ) (z y : AdeleRing (𝓞 ℚ) ℚ), F (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) q + z) y = F z y)
    (hF₂ : ∀ (q : ℚ) (z y : AdeleRing (𝓞 ℚ) ℚ), F z (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) q + y) = F z y)
    (hcoef : ∀ α β : ℚ,
      ∫ z : AdeleRing (𝓞 ℚ) ℚ, (∫ y : AdeleRing (𝓞 ℚ) ℚ, F z y * ψ (-(algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) β * y)) ∂μbox) *
        ψ (-(algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) α * z)) ∂μbox = 0)
    (z y : AdeleRing (𝓞 ℚ) ℚ) : F z y = 0 := by
  have hG : ∀ (β : ℚ) (z : AdeleRing (𝓞 ℚ) ℚ),
      (∫ w, F z w * ψ (-(algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) β * w)) ∂μbox) = 0 := fun β z =>
    eq_zero_of_forall_integral_box_mul_addChar_eq_zero ψ hψ
      (fun z => ∫ w, F z w * ψ (-(algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) β * w)) ∂μbox)
      (continuous_integral_slice_mul_addChar hψ hFc β) (fun q z => by simp only [hF₁]) (fun α => hcoef α β) z
  exact eq_zero_of_forall_integral_box_mul_addChar_eq_zero ψ hψ (fun w => F z w)
    (hFc.comp (by fun_prop : Continuous fun w : AdeleRing (𝓞 ℚ) ℚ => (z, w))) (fun q w => hF₂ q z w)
    (fun β => hG β z) y

end Iterated
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_mirabolicSeries_eq_dual_of_radicalCoefficient_eq.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_mirabolicSeries_eq_dual_of_radicalCoefficient_eq.LanglandsTunnell.CubicInduction"
end
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_mirabolicSeries_eq_dual_of_radicalCoefficient_eq.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_mirabolicSeries_eq_dual_of_radicalCoefficient_eq.LanglandsTunnell.CubicInduction"
end LanglandsTunnell.CubicInduction
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_mirabolicSeries_eq_dual_of_radicalCoefficient_eq.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_mirabolicSeries_eq_dual_of_radicalCoefficient_eq.LanglandsTunnell.CubicInduction"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_mirabolicSeries_eq_dual_of_radicalCoefficient_eq.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_mirabolicSeries_eq_dual_of_radicalCoefficient_eq.LanglandsTunnell.CubicInduction"

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "Converse.IsAdmissibleTwist TateLocal.addCharLevel TateLocal.localBorel TateLocal.borelSpace_localBorel TateLocal.integersPositiveCompacts TateLocal.coe_integersPositiveCompacts TateLocal.selfDualHaarAt TateLocal.higherUnitsAt TateLocal.forall_eq_one_and_exists_ne_one_of_addCharLevel"
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "matrixFin_ext matrixAdele_ext localMatN mapMatrix_localMatN_self mapMatrix_localMatN_of_ne finMatN mapMatrix_arch_finMatN mapMatrix_fin_finMatN localToAdelic3 converseCongruenceSet3 HasVanishingUnipotentIntegralAlong IsCongruenceEquivariantAlong lowerUnipotent21 longWeyl3 longWeyl3_coe dualWhittakerFn3 dualWhittakerFn3_apply weylPrime3 weylPrime3_coe weylPrime3_mul_self transposeInv3_weylPrime3 weylPrime3_mul_transposeInv3_radicalP21_mul_weylPrime3 IsGL3PsiWhittakerFn transposeInv3 IsCuspidalAlongP21 psiLoc mirabolicTranslate AdelicGL globalPointsGL centralScalarGL upperUnipotent3 upperUnipotent3_coe upperUnipotent3_zero radicalP21 radicalP21_zero radicalP21_coe radicalP21_add embedMat2 iotaGL coe_iotaGL iota MirabolicIndex mirabolicRep mirabolicRep_spec mirabolic_mk_unipotent_mul localMaximalCompact3 componentAtN archComponentN componentAt3 archComponent3 LocalGL3 cosetSum IsCosetEigenfunction IsRightInvariant diagUnitGL2 diagHom diagHom_apply isCuspidalAlongP21_mirabolicSeries"
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"
section
open IsDedekindDomain NumberField NumberField.AdelicHaar AutomorphicForm Matrix MeasureTheory
open scoped NNReal ENNReal Pointwise ProbabilityTheory

section Periodicity

private theorem vec_add_fst (q : ℚ) (z y : 𝔸) :
    (![algebraMap ℚ 𝔸 q + z, y] : Fin 2 → 𝔸) = ![algebraMap ℚ 𝔸 q, algebraMap ℚ 𝔸 0] + ![z, y] := by
  ext i
  fin_cases i <;> simp

private theorem vec_add_snd (q : ℚ) (z y : 𝔸) :
    (![z, algebraMap ℚ 𝔸 q + y] : Fin 2 → 𝔸) = ![algebraMap ℚ 𝔸 0, algebraMap ℚ 𝔸 q] + ![z, y] := by
  ext i
  fin_cases i <;> simp

private theorem radical_fst_periodic_of_rational_radical_invariant (G : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)
    (hG : ∀ (t₁ t₂ : ℚ) (g : AdelicGL 3 (𝓞 ℚ) ℚ),
      G (radicalP21 ![algebraMap ℚ 𝔸 t₁, algebraMap ℚ 𝔸 t₂] * g) = G g)
    (X : AdelicGL 3 (𝓞 ℚ) ℚ) (q : ℚ) (z y : 𝔸) :
    G (radicalP21 ![algebraMap ℚ 𝔸 q + z, y] * X) = G (radicalP21 ![z, y] * X) := by
  rw [vec_add_fst, radicalP21_add, mul_assoc, hG]

private theorem radical_snd_periodic_of_rational_radical_invariant (G : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)
    (hG : ∀ (t₁ t₂ : ℚ) (g : AdelicGL 3 (𝓞 ℚ) ℚ),
      G (radicalP21 ![algebraMap ℚ 𝔸 t₁, algebraMap ℚ 𝔸 t₂] * g) = G g)
    (X : AdelicGL 3 (𝓞 ℚ) ℚ) (q : ℚ) (z y : 𝔸) :
    G (radicalP21 ![z, algebraMap ℚ 𝔸 q + y] * X) = G (radicalP21 ![z, y] * X) := by
  rw [vec_add_snd, radicalP21_add, mul_assoc, hG]

private theorem mirabolicSeries_radicalP21_algebraMap_mul
    (ψ : AddChar 𝔸 ℂ) (hψ : IsGlobalAddChar ℚ ψ) (W : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hW : IsGL3PsiWhittakerFn ψ W)
    (t₁ t₂ : ℚ) (g : AdelicGL 3 (𝓞 ℚ) ℚ) :
    (∑' i : MirabolicIndex ℚ, W (mirabolicTranslate i
        * (radicalP21 ![algebraMap ℚ 𝔸 t₁, algebraMap ℚ 𝔸 t₂] * g))) = (∑' i : MirabolicIndex ℚ,
        W (mirabolicTranslate i * (g))) := by
  simp only [radicalP21, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
  exact mirabolicSeries_upperUnipotent3_algebraMap_mul hψ hW t₂ t₁ g

private theorem primal_sub_dual_radical_fst_periodic
    (ψ : AddChar 𝔸 ℂ) (hψ : IsGlobalAddChar ℚ ψ) (W : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hW : IsGL3PsiWhittakerFn ψ W)
    (hrad₁ : ∀ (t₁ t₂ : ℚ) (g : AdelicGL 3 (𝓞 ℚ) ℚ),
      (∑' i : MirabolicIndex ℚ, dualWhittakerFn3 W (mirabolicTranslate i
          * (weylPrime3 * transposeInv3 (radicalP21 ![algebraMap ℚ 𝔸 t₁, algebraMap ℚ 𝔸 t₂] * g)))) =
          (∑' i : MirabolicIndex ℚ, dualWhittakerFn3 W (mirabolicTranslate i
          * (weylPrime3 * transposeInv3 (g)))))
    (X : AdelicGL 3 (𝓞 ℚ) ℚ) (q : ℚ) (z y : 𝔸) :
    (∑' i : MirabolicIndex ℚ, W (mirabolicTranslate i * (radicalP21 ![algebraMap ℚ 𝔸 q + z, y] * X))) -
        (∑' i : MirabolicIndex ℚ, dualWhittakerFn3 W (mirabolicTranslate i
        * (weylPrime3 * transposeInv3 (radicalP21 ![algebraMap ℚ 𝔸 q + z, y] * X)))) =
      (∑' i : MirabolicIndex ℚ, W (mirabolicTranslate i * (radicalP21 ![z, y] * X))) -
          (∑' i : MirabolicIndex ℚ, dualWhittakerFn3 W (mirabolicTranslate i
          * (weylPrime3 * transposeInv3 (radicalP21 ![z, y] * X)))) := by
  have hP := radical_fst_periodic_of_rational_radical_invariant (fun g => (∑' i : MirabolicIndex ℚ,
      W (mirabolicTranslate i * (g))))
    (fun t₁ t₂ g => mirabolicSeries_radicalP21_algebraMap_mul ψ hψ W hW t₁ t₂ g) X q z y
  have hD := radical_fst_periodic_of_rational_radical_invariant (fun g => (∑' i : MirabolicIndex ℚ,
      dualWhittakerFn3 W (mirabolicTranslate i * (weylPrime3 * transposeInv3 (g))))) hrad₁ X q z y
  exact congrArg₂ (fun a b : ℂ => a - b) hP hD

private theorem primal_sub_dual_radical_snd_periodic
    (ψ : AddChar 𝔸 ℂ) (hψ : IsGlobalAddChar ℚ ψ) (W : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hW : IsGL3PsiWhittakerFn ψ W)
    (hrad₁ : ∀ (t₁ t₂ : ℚ) (g : AdelicGL 3 (𝓞 ℚ) ℚ),
      (∑' i : MirabolicIndex ℚ, dualWhittakerFn3 W (mirabolicTranslate i
          * (weylPrime3 * transposeInv3 (radicalP21 ![algebraMap ℚ 𝔸 t₁, algebraMap ℚ 𝔸 t₂] * g)))) =
          (∑' i : MirabolicIndex ℚ, dualWhittakerFn3 W (mirabolicTranslate i
          * (weylPrime3 * transposeInv3 (g)))))
    (X : AdelicGL 3 (𝓞 ℚ) ℚ) (q : ℚ) (z y : 𝔸) :
    (∑' i : MirabolicIndex ℚ, W (mirabolicTranslate i * (radicalP21 ![z, algebraMap ℚ 𝔸 q + y] * X))) -
        (∑' i : MirabolicIndex ℚ, dualWhittakerFn3 W (mirabolicTranslate i
        * (weylPrime3 * transposeInv3 (radicalP21 ![z, algebraMap ℚ 𝔸 q + y] * X)))) =
      (∑' i : MirabolicIndex ℚ, W (mirabolicTranslate i * (radicalP21 ![z, y] * X))) -
          (∑' i : MirabolicIndex ℚ, dualWhittakerFn3 W (mirabolicTranslate i
          * (weylPrime3 * transposeInv3 (radicalP21 ![z, y] * X)))) := by
  have hP := radical_snd_periodic_of_rational_radical_invariant (fun g => (∑' i : MirabolicIndex ℚ,
      W (mirabolicTranslate i * (g))))
    (fun t₁ t₂ g => mirabolicSeries_radicalP21_algebraMap_mul ψ hψ W hW t₁ t₂ g) X q z y
  have hD := radical_snd_periodic_of_rational_radical_invariant (fun g => (∑' i : MirabolicIndex ℚ,
      dualWhittakerFn3 W (mirabolicTranslate i * (weylPrime3 * transposeInv3 (g))))) hrad₁ X q z y
  exact congrArg₂ (fun a b : ℂ => a - b) hP hD

end Periodicity
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_mirabolicSeries_eq_dual_of_radicalCoefficient_eq.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_mirabolicSeries_eq_dual_of_radicalCoefficient_eq.LanglandsTunnell.CubicInduction"

section Continuity

private theorem continuous_primal_sub_dual_radical
    (ψ : AddChar 𝔸 ℂ) (hψ : IsGlobalAddChar ℚ ψ) (W : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hW : IsGL3PsiWhittakerFn ψ W)
    (hsum : ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ, Summable fun i : MirabolicIndex ℚ => W (mirabolicTranslate i * g))
    (hcont₁ : ∀ X : AdelicGL 3 (𝓞 ℚ) ℚ, Continuous fun p : 𝔸 × 𝔸 =>
      (∑' i : MirabolicIndex ℚ, dualWhittakerFn3 W (mirabolicTranslate i
          * (weylPrime3 * transposeInv3 (radicalP21 ![p.1, p.2] * X)))))
    (X : AdelicGL 3 (𝓞 ℚ) ℚ) :
    Continuous fun p : 𝔸 × 𝔸 => (∑' i : MirabolicIndex ℚ, W (mirabolicTranslate i
        * (radicalP21 ![p.1, p.2] * X))) - (∑' i : MirabolicIndex ℚ,
        dualWhittakerFn3 W (mirabolicTranslate i * (weylPrime3 * transposeInv3 (radicalP21 ![p.1, p.2] * X)))) :=
  (continuous_mirabolicSeries_radical hψ hW X (hsum X)).sub (hcont₁ X)

end Continuity
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_mirabolicSeries_eq_dual_of_radicalCoefficient_eq.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_mirabolicSeries_eq_dual_of_radicalCoefficient_eq.LanglandsTunnell.CubicInduction"

section Coefficients

private theorem coefficient_sub {ψ : AddChar 𝔸 ℂ} (hψ : IsGlobalAddChar ℚ ψ) (F F₁ : 𝔸 → 𝔸 → ℂ)
    (hF : Continuous fun p : 𝔸 × 𝔸 => F p.1 p.2) (hF₁ : Continuous fun p : 𝔸 × 𝔸 => F₁ p.1 p.2) (α β : ℚ) :
    (∫ z, (∫ y, (F z y - F₁ z y) * ψ (-(algebraMap ℚ 𝔸 β * y)) ∂μbox) * ψ (-(algebraMap ℚ 𝔸 α * z)) ∂μbox) =
      (∫ z, (∫ y, F z y * ψ (-(algebraMap ℚ 𝔸 β * y)) ∂μbox) * ψ (-(algebraMap ℚ 𝔸 α * z)) ∂μbox) -
        ∫ z, (∫ y, F₁ z y * ψ (-(algebraMap ℚ 𝔸 β * y)) ∂μbox) * ψ (-(algebraMap ℚ 𝔸 α * z)) ∂μbox := by
  have hinner : ∀ z : 𝔸,
      (∫ y, (F z y - F₁ z y) * ψ (-(algebraMap ℚ 𝔸 β * y)) ∂μbox) =
        (∫ y, F z y * ψ (-(algebraMap ℚ 𝔸 β * y)) ∂μbox) - ∫ y, F₁ z y * ψ (-(algebraMap ℚ 𝔸 β * y)) ∂μbox := by
    intro z
    simp_rw [sub_mul]
    exact integral_sub (integrable_slice_mul_addChar hψ hF β z) (integrable_slice_mul_addChar hψ hF₁ β z)
  simp_rw [hinner, sub_mul]
  refine integral_sub ?_ ?_
  · exact integrable_slice_mul_addChar hψ (F := fun _ z => ∫ y, F z y * ψ (-(algebraMap ℚ 𝔸 β * y)) ∂μbox)
      ((continuous_integral_slice_mul_addChar hψ hF β).comp continuous_snd) α 0
  · exact integrable_slice_mul_addChar hψ (F := fun _ z => ∫ y, F₁ z y * ψ (-(algebraMap ℚ 𝔸 β * y)) ∂μbox)
      ((continuous_integral_slice_mul_addChar hψ hF₁ β).comp continuous_snd) α 0

private theorem diagUnitGL2_one_aux5 : diagUnitGL2 (1 : 𝔸ˣ) = 1 := by
  refine Units.ext ?_
  ext i j
  fin_cases i <;> fin_cases j <;> simp [diagUnitGL2]

private theorem box_integral_dualSeries_radical_eq_zero'
    (ψ : AddChar 𝔸 ℂ) (hψ : IsGlobalAddChar ℚ ψ) (W : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hW : IsGL3PsiWhittakerFn ψ W)
    (hsum' : ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ,
      Summable fun i : MirabolicIndex ℚ => dualWhittakerFn3 W (mirabolicTranslate i * g))
    (X : AdelicGL 3 (𝓞 ℚ) ℚ) :
    (∫ z, ∫ y, (∑' i : MirabolicIndex ℚ, dualWhittakerFn3 W (mirabolicTranslate i
        * (weylPrime3 * transposeInv3 (radicalP21 ![z, y] * X)))) ∂μbox ∂μbox) = 0 := by
  have h := box_integral_dualSeries_radical_eq_zero ψ hψ W hW hsum' X 1
  simpa only [diagUnitGL2_one_aux5, map_one, one_mul] using h

private theorem radical_coefficient_zero_zero_primal_sub_dual_eq_zero
    (ψ : AddChar 𝔸 ℂ) (hψ : IsGlobalAddChar ℚ ψ) (W : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hW : IsGL3PsiWhittakerFn ψ W)
    (hsum : ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ, Summable fun i : MirabolicIndex ℚ => W (mirabolicTranslate i * g))
    (hsum' : ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ,
      Summable fun i : MirabolicIndex ℚ => dualWhittakerFn3 W (mirabolicTranslate i * g))
    (hcont₁ : ∀ X : AdelicGL 3 (𝓞 ℚ) ℚ, Continuous fun p : 𝔸 × 𝔸 =>
      (∑' i : MirabolicIndex ℚ, dualWhittakerFn3 W (mirabolicTranslate i
          * (weylPrime3 * transposeInv3 (radicalP21 ![p.1, p.2] * X)))))
    (D : Set (AdelicGL2 (𝓞 ℚ) ℚ)) (U : Ideal (𝓞 ℚ) → Subgroup (AdelicGL2 (𝓞 ℚ) ℚ))
    (gen : HeightOneSpectrum (𝓞 ℚ) → AdelicGL2 (𝓞 ℚ) ℚ)
    (hcusp : IsCuspidalAlongP21 (productionPinsOf ℚ D U gen (AdelicBox.adelicBox ℚ))
      (fun x => ∑' i : MirabolicIndex ℚ, W (mirabolicTranslate i * x)))
    (X : AdelicGL 3 (𝓞 ℚ) ℚ) :
    (∫ z, (∫ y, ((∑' i : MirabolicIndex ℚ, W (mirabolicTranslate i * (radicalP21 ![z, y] * X))) -
        (∑' i : MirabolicIndex ℚ, dualWhittakerFn3 W (mirabolicTranslate i
        * (weylPrime3 * transposeInv3 (radicalP21 ![z, y] * X))))) *
        ψ (-(algebraMap ℚ 𝔸 (0 : ℚ) * y)) ∂μbox) * ψ (-(algebraMap ℚ 𝔸 (0 : ℚ) * z)) ∂μbox) = 0 := by
  have hP : (∫ z, ∫ y, (∑' i : MirabolicIndex ℚ, W (mirabolicTranslate i * (radicalP21 ![z, y] * X))) ∂μbox
      ∂μbox) = 0 := hcusp X
  have hD := box_integral_dualSeries_radical_eq_zero' ψ hψ W hW hsum' X
  rw [coefficient_sub hψ (fun z y => (∑' i : MirabolicIndex ℚ, W (mirabolicTranslate i
      * (radicalP21 ![z, y] * X)))) (fun z y => (∑' i : MirabolicIndex ℚ,
      dualWhittakerFn3 W (mirabolicTranslate i * (weylPrime3 * transposeInv3 (radicalP21 ![z, y] * X)))))
    (continuous_mirabolicSeries_radical hψ hW X (hsum X)) (hcont₁ X) 0 0]
  simp only [map_zero, zero_mul, neg_zero, AddChar.map_zero_eq_one, mul_one]
  rw [hP, hD, sub_zero]

private theorem box_integral_radical_mode_primal_sub_dual_eq_zero
    (ψ : AddChar 𝔸 ℂ) (hψ : IsGlobalAddChar ℚ ψ) (W : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hW : IsGL3PsiWhittakerFn ψ W)
    (ω : 𝔸ˣ →* ℂˣ) (hω : LanglandsTunnell.Converse.IsAdmissibleTwist ℚ ω)
    (hWω : ∀ (z : 𝔸ˣ) (g : AdelicGL 3 (𝓞 ℚ) ℚ), W (centralScalarGL 3 (𝓞 ℚ) ℚ z * g) = ((ω z : ℂˣ) : ℂ) * W g)
    (hsum : ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ, Summable fun i : MirabolicIndex ℚ => W (mirabolicTranslate i * g))
    (hsum' : ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ,
      Summable fun i : MirabolicIndex ℚ => dualWhittakerFn3 W (mirabolicTranslate i * g))
    (α : ℚˣ) (X : AdelicGL 3 (𝓞 ℚ) ℚ) :
    (∫ z, ∫ y, (∑' i : MirabolicIndex ℚ, W (mirabolicTranslate i * (radicalP21 ![z, y] * X))) *
        ψ (-(algebraMap ℚ 𝔸 (α : ℚ) * z)) ∂μbox ∂μbox) -
      (∫ z, ∫ y, (∑' i : MirabolicIndex ℚ, dualWhittakerFn3 W (mirabolicTranslate i
          * (weylPrime3 * transposeInv3 (radicalP21 ![z, y] * X)))) * ψ (-(algebraMap ℚ 𝔸 (α : ℚ) * z))
          ∂μbox ∂μbox) = 0 := by
  rw [box_integral_mirabolicSeries_radical_mode_eq_tsum_primalModeMat ψ hψ W hW hsum α X,
    box_integral_dualSeries_radical_mode_eq_tsum_dualModeMat ψ hψ W hW hsum' α X,
    tsum_dualWhittakerFn3_dualModeMat_eq_tsum_primalModeMat ω hω W hWω α X, sub_self]

private theorem radical_coefficient_zero_primal_sub_dual_eq_zero
    (ψ : AddChar 𝔸 ℂ) (hψ : IsGlobalAddChar ℚ ψ) (W : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hW : IsGL3PsiWhittakerFn ψ W)
    (ω : 𝔸ˣ →* ℂˣ) (hω : LanglandsTunnell.Converse.IsAdmissibleTwist ℚ ω)
    (hWω : ∀ (z : 𝔸ˣ) (g : AdelicGL 3 (𝓞 ℚ) ℚ), W (centralScalarGL 3 (𝓞 ℚ) ℚ z * g) = ((ω z : ℂˣ) : ℂ) * W g)
    (hsum : ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ, Summable fun i : MirabolicIndex ℚ => W (mirabolicTranslate i * g))
    (hsum' : ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ,
      Summable fun i : MirabolicIndex ℚ => dualWhittakerFn3 W (mirabolicTranslate i * g))
    (hcont₁ : ∀ X : AdelicGL 3 (𝓞 ℚ) ℚ, Continuous fun p : 𝔸 × 𝔸 =>
      (∑' i : MirabolicIndex ℚ, dualWhittakerFn3 W (mirabolicTranslate i
          * (weylPrime3 * transposeInv3 (radicalP21 ![p.1, p.2] * X)))))
    (X : AdelicGL 3 (𝓞 ℚ) ℚ) (α : ℚ) (hα : α ≠ 0) :
    (∫ z, (∫ y, ((∑' i : MirabolicIndex ℚ, W (mirabolicTranslate i * (radicalP21 ![z, y] * X))) -
        (∑' i : MirabolicIndex ℚ, dualWhittakerFn3 W (mirabolicTranslate i
        * (weylPrime3 * transposeInv3 (radicalP21 ![z, y] * X))))) *
        ψ (-(algebraMap ℚ 𝔸 (0 : ℚ) * y)) ∂μbox) * ψ (-(algebraMap ℚ 𝔸 α * z)) ∂μbox) = 0 := by
  have h := box_integral_radical_mode_primal_sub_dual_eq_zero ψ hψ W hW ω hω hWω hsum hsum' (Units.mk0 α hα) X
  rw [coefficient_sub hψ (fun z y => (∑' i : MirabolicIndex ℚ, W (mirabolicTranslate i
      * (radicalP21 ![z, y] * X)))) (fun z y => (∑' i : MirabolicIndex ℚ,
      dualWhittakerFn3 W (mirabolicTranslate i * (weylPrime3 * transposeInv3 (radicalP21 ![z, y] * X)))))
    (continuous_mirabolicSeries_radical hψ hW X (hsum X)) (hcont₁ X) α 0]
  simp only [map_zero, zero_mul, neg_zero, AddChar.map_zero_eq_one, mul_one]
  simp_rw [← integral_mul_const]
  simpa only [Units.val_mk0] using h

end Coefficients
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_mirabolicSeries_eq_dual_of_radicalCoefficient_eq.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_mirabolicSeries_eq_dual_of_radicalCoefficient_eq.LanglandsTunnell.CubicInduction"
end
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_mirabolicSeries_eq_dual_of_radicalCoefficient_eq.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_mirabolicSeries_eq_dual_of_radicalCoefficient_eq.LanglandsTunnell.CubicInduction"
end LanglandsTunnell.CubicInduction
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_mirabolicSeries_eq_dual_of_radicalCoefficient_eq.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_mirabolicSeries_eq_dual_of_radicalCoefficient_eq.LanglandsTunnell.CubicInduction"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_mirabolicSeries_eq_dual_of_radicalCoefficient_eq.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_mirabolicSeries_eq_dual_of_radicalCoefficient_eq.LanglandsTunnell.CubicInduction"

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "Converse.IsAdmissibleTwist TateLocal.addCharLevel TateLocal.localBorel TateLocal.borelSpace_localBorel TateLocal.integersPositiveCompacts TateLocal.coe_integersPositiveCompacts TateLocal.selfDualHaarAt TateLocal.higherUnitsAt TateLocal.forall_eq_one_and_exists_ne_one_of_addCharLevel"
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "matrixFin_ext matrixAdele_ext localMatN mapMatrix_localMatN_self mapMatrix_localMatN_of_ne finMatN mapMatrix_arch_finMatN mapMatrix_fin_finMatN localToAdelic3 converseCongruenceSet3 HasVanishingUnipotentIntegralAlong IsCongruenceEquivariantAlong lowerUnipotent21 longWeyl3 longWeyl3_coe dualWhittakerFn3 dualWhittakerFn3_apply weylPrime3 weylPrime3_coe weylPrime3_mul_self transposeInv3_weylPrime3 weylPrime3_mul_transposeInv3_radicalP21_mul_weylPrime3 IsGL3PsiWhittakerFn transposeInv3 IsCuspidalAlongP21 psiLoc mirabolicTranslate AdelicGL globalPointsGL centralScalarGL upperUnipotent3 upperUnipotent3_coe upperUnipotent3_zero radicalP21 radicalP21_zero radicalP21_coe radicalP21_add embedMat2 iotaGL coe_iotaGL iota MirabolicIndex mirabolicRep mirabolicRep_spec mirabolic_mk_unipotent_mul localMaximalCompact3 componentAtN archComponentN componentAt3 archComponent3 LocalGL3 cosetSum IsCosetEigenfunction IsRightInvariant diagUnitGL2 diagHom diagHom_apply isCuspidalAlongP21_mirabolicSeries"
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"
section
open IsDedekindDomain NumberField NumberField.AdelicHaar AutomorphicForm Matrix MeasureTheory
open scoped NNReal ENNReal Pointwise ProbabilityTheory
attribute [local instance] NumberField.Idele.ideleBorel NumberField.AdelicHaar.adeleBorel

section Conjugation

variable {A : Type*} [CommRing A]

private theorem iotaGL_mul_upperUnipotent3_zero_aux6 (h : GL (Fin 2) A) (y z : A) :
    iotaGL h * upperUnipotent3 0 y z =
      upperUnipotent3 0 ((h : Matrix (Fin 2) (Fin 2) A) 1 0 * z + (h : Matrix (Fin 2) (Fin 2) A) 1 1 * y)
        ((h : Matrix (Fin 2) (Fin 2) A) 0 0 * z + (h : Matrix (Fin 2) (Fin 2) A) 0 1 * y) * iotaGL h := by
  refine Units.ext ?_
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Units.val_mul, coe_iotaGL, embedMat2, Matrix.mul_apply, Fin.sum_univ_three]

end Conjugation
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_mirabolicSeries_eq_dual_of_radicalCoefficient_eq.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_mirabolicSeries_eq_dual_of_radicalCoefficient_eq.LanglandsTunnell.CubicInduction"

section BoxInvariance

private theorem regular_adelicAddHaar_rat : (adelicAddHaar (𝓞 ℚ) ℚ).Regular := by
  haveI := borelSpace_adeleBorel (𝓞 ℚ) ℚ
  exact Measure.regular_addHaarMeasure

private theorem map_inv_smul_adelicAddHaar_rat (b : (AdeleRing (𝓞 ℚ) ℚ)ˣ) :
    (adelicAddHaar (𝓞 ℚ) ℚ).map (fun x : AdeleRing (𝓞 ℚ) ℚ => b⁻¹ • x) =
      (distribHaarChar (AdeleRing (𝓞 ℚ) ℚ) b : ℝ≥0) • adelicAddHaar (𝓞 ℚ) ℚ := by
  haveI := borelSpace_adeleBorel (𝓞 ℚ) ℚ
  haveI := isAddHaarMeasure_adelicAddHaar (𝓞 ℚ) ℚ
  haveI := regular_adelicAddHaar_rat
  have hm : Measurable (fun x : AdeleRing (𝓞 ℚ) ℚ => b⁻¹ • x) := (continuous_const_smul _).measurable
  ext s hs
  rw [Measure.map_apply hm hs]
  simp only [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul]
  rw [distribHaarChar_mul (adelicAddHaar (𝓞 ℚ) ℚ) b s]
  congr 1
  ext x
  simp [Set.mem_smul_set_iff_inv_smul_mem]

private theorem setIntegral_adelicBox_comp_add_right_aux6 {f : AdeleRing (𝓞 ℚ) ℚ → ℂ}
    (hf : ∀ (α : ℚ) (y : AdeleRing (𝓞 ℚ) ℚ), f (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) α + y) = f y)
    (s : AdeleRing (𝓞 ℚ) ℚ) :
    ∫ y in AdelicBox.adelicBox ℚ, f (y + s) ∂(NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ) =
      ∫ y in AdelicBox.adelicBox ℚ, f y ∂(NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ) := by
  haveI := NumberField.AdelicHaar.borelSpace_adeleBorel (𝓞 ℚ) ℚ
  haveI := NumberField.AdelicHaar.isAddHaarMeasure_adelicAddHaar (𝓞 ℚ) ℚ
  set μ : Measure (AdeleRing (𝓞 ℚ) ℚ) := NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ with hμ

  have hf' : ∀ (γ : AdeleRing.principalSubgroup (𝓞 ℚ) ℚ) (y : AdeleRing (𝓞 ℚ) ℚ), f (γ +ᵥ y) = f y := by
    intro γ y
    obtain ⟨α, hα⟩ := RingHom.mem_range.mp γ.2
    show f ((γ : AdeleRing (𝓞 ℚ) ℚ) + y) = f y
    rw [← hα]
    exact hf α y
  have hbox := AdelicBox.isAddFundamentalDomain_adelicBox ℚ μ

  haveI : Countable (AdeleRing.principalSubgroup (𝓞 ℚ) ℚ) := by
    refine Function.Surjective.countable (f := fun α : ℚ =>
      (⟨algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) α, ⟨α, rfl⟩⟩ : AdeleRing.principalSubgroup (𝓞 ℚ) ℚ)) ?_
    rintro ⟨x, hx⟩
    obtain ⟨α, rfl⟩ := RingHom.mem_range.mp hx
    exact ⟨α, rfl⟩

  have hbox' : IsAddFundamentalDomain (AdeleRing.principalSubgroup (𝓞 ℚ) ℚ) (s +ᵥ AdelicBox.adelicBox ℚ) μ :=
    hbox.vadd_of_comm s

  have hpre : (fun y : AdeleRing (𝓞 ℚ) ℚ => y + s) ⁻¹' (s +ᵥ AdelicBox.adelicBox ℚ) = AdelicBox.adelicBox ℚ := by
    ext y
    simp only [Set.mem_preimage, Set.mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add]
    rw [show -s + (y + s) = y by abel]
  have hshift := (measurePreserving_add_right μ s).setIntegral_preimage_emb
    (MeasurableEquiv.addRight s).measurableEmbedding f (s +ᵥ AdelicBox.adelicBox ℚ)
  rw [hpre] at hshift
  rw [hshift]
  exact hbox'.setIntegral_eq hbox hf'

private theorem addChar_mul_algebraMap_add_aux6 {ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ}
    (hψ : IsPrincipalInvariantAddChar ℚ ψ) (β α : ℚ) (y : AdeleRing (𝓞 ℚ) ℚ) :
    ψ (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) β * (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) α + y)) =
      ψ (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) β * y) := by
  rw [mul_add, AddChar.map_add_eq_mul, ← map_mul (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ)), hψ (β * α), one_mul]

private noncomputable def principalUnit (d : ℚˣ) : 𝔸ˣ :=
  Units.map (algebraMap ℚ 𝔸 : ℚ →* 𝔸) d

private theorem coe_principalUnit (d : ℚˣ) : ((principalUnit d : 𝔸ˣ) : 𝔸) = algebraMap ℚ 𝔸 (d : ℚ) :=
  rfl

private theorem principalUnit_smul_mem (d : ℚˣ) (γ : AdeleRing.principalSubgroup (𝓞 ℚ) ℚ) :
    principalUnit d • (γ : 𝔸) ∈ AdeleRing.principalSubgroup (𝓞 ℚ) ℚ := by
  obtain ⟨q, hq⟩ := RingHom.mem_range.mp γ.2
  refine RingHom.mem_range.mpr ⟨(d : ℚ) * q, ?_⟩
  simp only [map_mul, hq, Units.smul_def, smul_eq_mul, coe_principalUnit]

private theorem countable_principalSubgroup_aux6 : Countable (AdeleRing.principalSubgroup (𝓞 ℚ) ℚ) := by
  refine Function.Surjective.countable (f := fun α : ℚ =>
    (⟨algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) α, ⟨α, rfl⟩⟩ : AdeleRing.principalSubgroup (𝓞 ℚ) ℚ)) ?_
  rintro ⟨x, hx⟩
  obtain ⟨α, rfl⟩ := RingHom.mem_range.mp hx
  exact ⟨α, rfl⟩

private theorem isAddFundamentalDomain_preimage_inv_principalUnit_smul (d : ℚˣ) :
    IsAddFundamentalDomain (AdeleRing.principalSubgroup (𝓞 ℚ) ℚ)
      ((fun y : 𝔸 => (principalUnit d)⁻¹ • y) ⁻¹' AdelicBox.adelicBox ℚ) (adelicAddHaar (𝓞 ℚ) ℚ) := by
  haveI := borelSpace_adeleBorel (𝓞 ℚ) ℚ
  haveI := isAddHaarMeasure_adelicAddHaar (𝓞 ℚ) ℚ
  haveI := countable_principalSubgroup_aux6
  have hbox := AdelicBox.isAddFundamentalDomain_adelicBox ℚ (adelicAddHaar (𝓞 ℚ) ℚ)

  let e : AdeleRing.principalSubgroup (𝓞 ℚ) ℚ → AdeleRing.principalSubgroup (𝓞 ℚ) ℚ :=
    fun γ => ⟨principalUnit d • (γ : 𝔸), principalUnit_smul_mem d γ⟩
  have he : Function.Bijective e := by
    refine Function.bijective_iff_has_inverse.mpr
      ⟨fun γ => ⟨(principalUnit d)⁻¹ • (γ : 𝔸), by
        first | exact principalUnit_smul_mem d⁻¹ γ | simpa using principalUnit_smul_mem d⁻¹ γ⟩, fun γ => ?_, fun γ => ?_⟩
    · ext; simp [e]
    · ext; simp [e]
  have hf : Measure.QuasiMeasurePreserving (fun y : 𝔸 => (principalUnit d)⁻¹ • y)
      (adelicAddHaar (𝓞 ℚ) ℚ) (adelicAddHaar (𝓞 ℚ) ℚ) := by
    refine ⟨(continuous_const_smul _).measurable, ?_⟩
    rw [map_inv_smul_adelicAddHaar_rat]
    exact Measure.smul_absolutelyContinuous
  refine hbox.preimage_of_equiv hf he fun γ x => ?_
  show (principalUnit d)⁻¹ • ((principalUnit d • (γ : 𝔸)) + x) = (γ : 𝔸) + (principalUnit d)⁻¹ • x
  rw [smul_add, inv_smul_smul]

private theorem distribHaarChar_principalUnit (d : ℚˣ) : distribHaarChar 𝔸 (principalUnit d) = 1 := by
  haveI := borelSpace_adeleBorel (𝓞 ℚ) ℚ
  haveI := isAddHaarMeasure_adelicAddHaar (𝓞 ℚ) ℚ
  haveI := countable_principalSubgroup_aux6
  have hmap := map_inv_smul_adelicAddHaar_rat (principalUnit d)
  have hmeas : Measurable (fun y : 𝔸 => (principalUnit d)⁻¹ • y) := (continuous_const_smul _).measurable
  have h1 := congrArg (fun μ : Measure 𝔸 => μ (AdelicBox.adelicBox ℚ)) hmap
  simp only [Measure.map_apply hmeas (AdelicBox.measurableSet_adelicBox ℚ), Measure.smul_apply, ENNReal.smul_def,
    smul_eq_mul] at h1
  rw [(isAddFundamentalDomain_preimage_inv_principalUnit_smul d).measure_eq
    (AdelicBox.isAddFundamentalDomain_adelicBox ℚ (adelicAddHaar (𝓞 ℚ) ℚ))] at h1
  have h2 : ((distribHaarChar 𝔸 (principalUnit d) : ℝ≥0) : ℝ≥0∞) * adelicAddHaar (𝓞 ℚ) ℚ (AdelicBox.adelicBox ℚ) =
      1 * adelicAddHaar (𝓞 ℚ) ℚ (AdelicBox.adelicBox ℚ) := by
    rw [one_mul]; exact h1.symm
  have h3 := (ENNReal.mul_left_inj (AdelicBox.adelicAddHaar_adelicBox_pos ℚ).ne'
    (AdelicBox.adelicAddHaar_adelicBox_lt_top ℚ).ne).mp h2
  exact_mod_cast h3

private theorem setIntegral_adelicBox_comp_algebraMap_mul {K : 𝔸 → ℂ}
    (hK : ∀ (q : ℚ) (y : 𝔸), K (algebraMap ℚ 𝔸 q + y) = K y) (d : ℚˣ) :
    ∫ y in AdelicBox.adelicBox ℚ, K (algebraMap ℚ 𝔸 (d : ℚ) * y) ∂(adelicAddHaar (𝓞 ℚ) ℚ) =
      ∫ y in AdelicBox.adelicBox ℚ, K y ∂(adelicAddHaar (𝓞 ℚ) ℚ) := by
  haveI := borelSpace_adeleBorel (𝓞 ℚ) ℚ
  haveI := isAddHaarMeasure_adelicAddHaar (𝓞 ℚ) ℚ
  haveI := countable_principalSubgroup_aux6
  have hK' : ∀ (γ : AdeleRing.principalSubgroup (𝓞 ℚ) ℚ) (y : 𝔸), K (γ +ᵥ y) = K y := by
    intro γ y
    obtain ⟨q, hq⟩ := RingHom.mem_range.mp γ.2
    show K ((γ : 𝔸) + y) = K y
    rw [← hq]
    exact hK q y

  have hS : (MeasurableEquiv.smul (principalUnit d) : 𝔸 → 𝔸) ⁻¹'
      ((fun y : 𝔸 => (principalUnit d)⁻¹ • y) ⁻¹' AdelicBox.adelicBox ℚ) = AdelicBox.adelicBox ℚ := by
    ext y
    simp [MeasurableEquiv.smul, inv_smul_smul]
  have hmapeq : (adelicAddHaar (𝓞 ℚ) ℚ).map (MeasurableEquiv.smul (principalUnit d)) = adelicAddHaar (𝓞 ℚ) ℚ := by
    have h := map_inv_smul_adelicAddHaar_rat (principalUnit d)⁻¹
    rw [inv_inv, map_inv, distribHaarChar_principalUnit, inv_one, one_smul] at h
    first | exact h | simpa [MeasurableEquiv.smul] using h | (simp only [MeasurableEquiv.smul, MeasurableEquiv.coe_mk]; exact h)
  have hstep := setIntegral_map_equiv (μ := adelicAddHaar (𝓞 ℚ) ℚ) (MeasurableEquiv.smul (principalUnit d)) K
    ((fun y : 𝔸 => (principalUnit d)⁻¹ • y) ⁻¹' AdelicBox.adelicBox ℚ)
  rw [hS, hmapeq] at hstep
  have hint : ∀ y : 𝔸, K (algebraMap ℚ 𝔸 (d : ℚ) * y) = K (MeasurableEquiv.smul (principalUnit d) y) := by
    intro y
    simp [MeasurableEquiv.smul, Units.smul_def, coe_principalUnit]
  simp_rw [hint]
  rw [← hstep]
  exact (isAddFundamentalDomain_preimage_inv_principalUnit_smul d).setIntegral_eq
    (AdelicBox.isAddFundamentalDomain_adelicBox ℚ (adelicAddHaar (𝓞 ℚ) ℚ)) hK'

private theorem integral_cond_adelicBox_comp_add_right {f : 𝔸 → ℂ}
    (hf : ∀ (q : ℚ) (y : 𝔸), f (algebraMap ℚ 𝔸 q + y) = f y) (s : 𝔸) :
    ∫ y, f (y + s) ∂μbox = ∫ y, f y ∂μbox := by
  simp only [ProbabilityTheory.cond, integral_smul_measure, setIntegral_adelicBox_comp_add_right_aux6 hf s]

private theorem integral_cond_adelicBox_comp_algebraMap_mul {K : 𝔸 → ℂ}
    (hK : ∀ (q : ℚ) (y : 𝔸), K (algebraMap ℚ 𝔸 q + y) = K y) (d : ℚˣ) :
    ∫ y, K (algebraMap ℚ 𝔸 (d : ℚ) * y) ∂μbox = ∫ y, K y ∂μbox := by
  simp only [ProbabilityTheory.cond, integral_smul_measure, setIntegral_adelicBox_comp_algebraMap_mul hK d]

end BoxInvariance
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_mirabolicSeries_eq_dual_of_radicalCoefficient_eq.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_mirabolicSeries_eq_dual_of_radicalCoefficient_eq.LanglandsTunnell.CubicInduction"

section Head

private theorem addChar_neg_mul_algebraMap_add {ψ : AddChar 𝔸 ℂ} (hψ : IsGlobalAddChar ℚ ψ) (β q : ℚ)
    (y : 𝔸) :
    ψ (-(algebraMap ℚ 𝔸 β * (algebraMap ℚ 𝔸 q + y))) = ψ (-(algebraMap ℚ 𝔸 β * y)) := by
  rw [← neg_mul, ← map_neg, addChar_mul_algebraMap_add_aux6 hψ.principalInvariant, map_neg, neg_mul]

private theorem integral_box_box_radical_coefficient_iotaGL_mul_eq (ψ : AddChar 𝔸 ℂ) (hψ : IsGlobalAddChar ℚ ψ)
    (G : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (X : AdelicGL 3 (𝓞 ℚ) ℚ) (H : GL (Fin 2) 𝔸) (c β : ℚ) (hβ : β ≠ 0)
    (hH₀₀ : (H : Matrix (Fin 2) (Fin 2) 𝔸) 0 0 = 1) (hH₀₁ : (H : Matrix (Fin 2) (Fin 2) 𝔸) 0 1 = 0)
    (hH₁₀ : (H : Matrix (Fin 2) (Fin 2) 𝔸) 1 0 = algebraMap ℚ 𝔸 c)
    (hH₁₁ : (H : Matrix (Fin 2) (Fin 2) 𝔸) 1 1 = algebraMap ℚ 𝔸 β)
    (hG : ∀ g, G (iotaGL H * g) = G g)
    (hper : ∀ (q : ℚ) (z y : 𝔸),
      G (radicalP21 ![z, algebraMap ℚ 𝔸 q + y] * X) = G (radicalP21 ![z, y] * X)) :
    ∫ z, (∫ y, G (radicalP21 ![z, y] * (iotaGL H * X)) * ψ (-(algebraMap ℚ 𝔸 1 * y)) ∂μbox) *
        ψ (-(algebraMap ℚ 𝔸 0 * z)) ∂μbox =
      ∫ z, (∫ y, G (radicalP21 ![z, y] * X) * ψ (-(algebraMap ℚ 𝔸 β * y)) ∂μbox) *
        ψ (-(algebraMap ℚ 𝔸 c * z)) ∂μbox := by
  refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
  simp only [map_zero, map_one, zero_mul, one_mul, neg_zero, AddChar.map_zero_eq_one, mul_one]

  set u : ℚˣ := (Units.mk0 β hβ)⁻¹ with hu
  have hu' : ((u : ℚˣ) : ℚ) = β⁻¹ := by simp [hu]
  have hβu : ∀ t : 𝔸, algebraMap ℚ 𝔸 β * (algebraMap ℚ 𝔸 (u : ℚ) * t) = t := by
    intro t
    rw [← mul_assoc, ← map_mul, hu', mul_inv_cancel₀ hβ, map_one, one_mul]

  have hconj : ∀ y : 𝔸,
      G (radicalP21 ![z, y] * (iotaGL H * X)) =
        G (radicalP21 ![z, algebraMap ℚ 𝔸 (u : ℚ) * (y + -(algebraMap ℚ 𝔸 c * z))] * X) := by
    intro y
    rw [← hG (radicalP21 ![z, algebraMap ℚ 𝔸 (u : ℚ) * (y + -(algebraMap ℚ 𝔸 c * z))] * X), ← mul_assoc,
      ← mul_assoc]
    congr 2
    have hl : (radicalP21 ![z, y] : AdelicGL 3 (𝓞 ℚ) ℚ) = upperUnipotent3 0 y z := rfl
    have hr : (radicalP21 ![z, algebraMap ℚ 𝔸 (u : ℚ) * (y + -(algebraMap ℚ 𝔸 c * z))] :
        AdelicGL 3 (𝓞 ℚ) ℚ) =
      upperUnipotent3 0 (algebraMap ℚ 𝔸 (u : ℚ) * (y + -(algebraMap ℚ 𝔸 c * z))) z := rfl
    have hy : algebraMap ℚ 𝔸 c * z + (y + -(algebraMap ℚ 𝔸 c * z)) = y := by ring
    rw [hr, iotaGL_mul_upperUnipotent3_zero_aux6, hH₀₀, hH₀₁, hH₁₀, hH₁₁, hβu, one_mul, zero_mul, add_zero, hy, hl]

  have hKper : ∀ (q : ℚ) (y : 𝔸),
      G (radicalP21 ![z, algebraMap ℚ 𝔸 q + y] * X) * ψ (-(algebraMap ℚ 𝔸 β * (algebraMap ℚ 𝔸 q + y))) =
        G (radicalP21 ![z, y] * X) * ψ (-(algebraMap ℚ 𝔸 β * y)) := by
    intro q y
    rw [hper, addChar_neg_mul_algebraMap_add hψ]
  have hdil : ∫ y, G (radicalP21 ![z, algebraMap ℚ 𝔸 (u : ℚ) * y] * X) *
        ψ (-(algebraMap ℚ 𝔸 β * (algebraMap ℚ 𝔸 (u : ℚ) * y))) ∂μbox =
      ∫ y, G (radicalP21 ![z, y] * X) * ψ (-(algebraMap ℚ 𝔸 β * y)) ∂μbox :=
    integral_cond_adelicBox_comp_algebraMap_mul
      (K := fun y => G (radicalP21 ![z, y] * X) * ψ (-(algebraMap ℚ 𝔸 β * y))) hKper u
  have hfper : ∀ (q : ℚ) (w : 𝔸),
      G (radicalP21 ![z, algebraMap ℚ 𝔸 (u : ℚ) * (algebraMap ℚ 𝔸 q + w)] * X) * ψ (-(algebraMap ℚ 𝔸 q + w)) =
        G (radicalP21 ![z, algebraMap ℚ 𝔸 (u : ℚ) * w] * X) * ψ (-w) := by
    intro q w
    rw [mul_add, ← map_mul, hper, ← one_mul (algebraMap ℚ 𝔸 q + w), ← map_one (algebraMap ℚ 𝔸),
      addChar_neg_mul_algebraMap_add hψ, map_one, one_mul]
  have htr : ∫ y, G (radicalP21 ![z, algebraMap ℚ 𝔸 (u : ℚ) * (y + -(algebraMap ℚ 𝔸 c * z))] * X) *
        ψ (-(y + -(algebraMap ℚ 𝔸 c * z))) ∂μbox =
      ∫ y, G (radicalP21 ![z, algebraMap ℚ 𝔸 (u : ℚ) * y] * X) * ψ (-y) ∂μbox :=
    integral_cond_adelicBox_comp_add_right
      (f := fun w => G (radicalP21 ![z, algebraMap ℚ 𝔸 (u : ℚ) * w] * X) * ψ (-w)) hfper
      (-(algebraMap ℚ 𝔸 c * z))

  simp only [hβu] at hdil
  rw [← hdil, ← htr]
  simp only [hconj]
  have hsplit : ∀ y : 𝔸, ψ (-(y + -(algebraMap ℚ 𝔸 c * z))) = ψ (-y) * ψ (algebraMap ℚ 𝔸 c * z) := by
    intro y
    rw [neg_add, neg_neg, AddChar.map_add_eq_mul]
  simp only [hsplit, ← mul_assoc, integral_mul_const]
  rw [mul_assoc, ← AddChar.map_add_eq_mul, add_neg_cancel, AddChar.map_zero_eq_one, mul_one]

end Head
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_mirabolicSeries_eq_dual_of_radicalCoefficient_eq.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_mirabolicSeries_eq_dual_of_radicalCoefficient_eq.LanglandsTunnell.CubicInduction"
end
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_mirabolicSeries_eq_dual_of_radicalCoefficient_eq.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_mirabolicSeries_eq_dual_of_radicalCoefficient_eq.LanglandsTunnell.CubicInduction"
end LanglandsTunnell.CubicInduction
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_mirabolicSeries_eq_dual_of_radicalCoefficient_eq.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_mirabolicSeries_eq_dual_of_radicalCoefficient_eq.LanglandsTunnell.CubicInduction"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_mirabolicSeries_eq_dual_of_radicalCoefficient_eq.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_mirabolicSeries_eq_dual_of_radicalCoefficient_eq.LanglandsTunnell.CubicInduction"

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "Converse.IsAdmissibleTwist TateLocal.addCharLevel TateLocal.localBorel TateLocal.borelSpace_localBorel TateLocal.integersPositiveCompacts TateLocal.coe_integersPositiveCompacts TateLocal.selfDualHaarAt TateLocal.higherUnitsAt TateLocal.forall_eq_one_and_exists_ne_one_of_addCharLevel"
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "matrixFin_ext matrixAdele_ext localMatN mapMatrix_localMatN_self mapMatrix_localMatN_of_ne finMatN mapMatrix_arch_finMatN mapMatrix_fin_finMatN localToAdelic3 converseCongruenceSet3 HasVanishingUnipotentIntegralAlong IsCongruenceEquivariantAlong lowerUnipotent21 longWeyl3 longWeyl3_coe dualWhittakerFn3 dualWhittakerFn3_apply weylPrime3 weylPrime3_coe weylPrime3_mul_self transposeInv3_weylPrime3 weylPrime3_mul_transposeInv3_radicalP21_mul_weylPrime3 IsGL3PsiWhittakerFn transposeInv3 IsCuspidalAlongP21 psiLoc mirabolicTranslate AdelicGL globalPointsGL centralScalarGL upperUnipotent3 upperUnipotent3_coe upperUnipotent3_zero radicalP21 radicalP21_zero radicalP21_coe radicalP21_add embedMat2 iotaGL coe_iotaGL iota MirabolicIndex mirabolicRep mirabolicRep_spec mirabolic_mk_unipotent_mul localMaximalCompact3 componentAtN archComponentN componentAt3 archComponent3 LocalGL3 cosetSum IsCosetEigenfunction IsRightInvariant diagUnitGL2 diagHom diagHom_apply isCuspidalAlongP21_mirabolicSeries"
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"
section
open IsDedekindDomain NumberField NumberField.AdelicHaar AutomorphicForm Matrix MeasureTheory LanglandsTunnell.Converse
open scoped NNReal ENNReal Pointwise ProbabilityTheory

section TransposeDual

variable {A : Type*} [CommRing A]

private theorem transposeInv3_mul_aux7 (g h : GL (Fin 3) A) :
    transposeInv3 (g * h) = transposeInv3 g * transposeInv3 h := by
  refine Units.ext ?_
  change ((((g * h)⁻¹ : GL (Fin 3) A)) : Matrix (Fin 3) (Fin 3) A)ᵀ = _
  rw [_root_.mul_inv_rev, Units.val_mul, Matrix.transpose_mul]
  rfl

private theorem transposeInv3_one_aux7 : transposeInv3 (1 : GL (Fin 3) A) = 1 := by
  refine Units.ext ?_
  change ((((1 : GL (Fin 3) A))⁻¹ : GL (Fin 3) A) : Matrix (Fin 3) (Fin 3) A)ᵀ = 1
  rw [inv_one, Units.val_one, Matrix.transpose_one]

private theorem transposeInv3_transposeInv3_aux7 (g : GL (Fin 3) A) : transposeInv3 (transposeInv3 g) = g := by
  refine Units.ext ?_
  change ((((transposeInv3 g)⁻¹ : GL (Fin 3) A)) : Matrix (Fin 3) (Fin 3) A)ᵀ = _
  have h : ((((transposeInv3 g)⁻¹ : GL (Fin 3) A)) : Matrix (Fin 3) (Fin 3) A) =
      ((g : GL (Fin 3) A) : Matrix (Fin 3) (Fin 3) A)ᵀ := rfl
  rw [h, Matrix.transpose_transpose]

private theorem transposeInv3_longWeyl3_aux7 : transposeInv3 (longWeyl3 : GL (Fin 3) A) = longWeyl3 := by
  refine Units.ext ?_
  change ((((longWeyl3 : GL (Fin 3) A))⁻¹ : GL (Fin 3) A) : Matrix (Fin 3) (Fin 3) A)ᵀ = _
  have h : ((((longWeyl3 : GL (Fin 3) A))⁻¹ : GL (Fin 3) A) : Matrix (Fin 3) (Fin 3) A) =
      !![0, 0, 1; 0, 1, 0; 1, 0, 0] := rfl
  rw [h, longWeyl3_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.transpose_apply]

private theorem longWeyl3_mul_self_aux7 : (longWeyl3 : GL (Fin 3) A) * longWeyl3 = 1 := by
  refine Units.ext ?_
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_three]

private theorem longWeyl3_mul_transposeInv3_upperUnipotent3_mul_longWeyl3_aux7 (x y z : A) :
    (longWeyl3 * transposeInv3 (upperUnipotent3 x y z) * longWeyl3 : GL (Fin 3) A) =
      upperUnipotent3 (-y) (-x) (x * y - z) := by
  refine Units.ext ?_
  have hinv : (((upperUnipotent3 x y z : GL (Fin 3) A)⁻¹ : GL (Fin 3) A) : Matrix (Fin 3) (Fin 3) A) =
      !![1, -x, x * y - z; 0, 1, -y; 0, 0, 1] := rfl
  have htr : ((transposeInv3 (upperUnipotent3 x y z) : GL (Fin 3) A) : Matrix (Fin 3) (Fin 3) A) =
      !![1, 0, 0; -x, 1, 0; x * y - z, -y, 1] := by
    change (((upperUnipotent3 x y z : GL (Fin 3) A)⁻¹ : GL (Fin 3) A) : Matrix (Fin 3) (Fin 3) A)ᵀ = _
    rw [hinv]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.transpose_apply]
  rw [Units.val_mul, Units.val_mul, htr, longWeyl3_coe, upperUnipotent3_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]

private theorem longWeyl3_mul_transposeInv3_upperUnipotent3_aux7 (x y z : A) :
    (longWeyl3 * transposeInv3 (upperUnipotent3 x y z) : GL (Fin 3) A) =
      upperUnipotent3 (-y) (-x) (x * y - z) * longWeyl3 := by
  rw [← longWeyl3_mul_transposeInv3_upperUnipotent3_mul_longWeyl3_aux7, mul_assoc, longWeyl3_mul_self_aux7, mul_one]

private theorem isGL3PsiWhittakerFn_dualWhittakerFn3_aux7 {R : Type*} [CommRing R] (ψ : AddChar A R)
    {W : GL (Fin 3) A → R} (hW : IsGL3PsiWhittakerFn ψ W) :
    IsGL3PsiWhittakerFn ψ⁻¹ (dualWhittakerFn3 W) := by
  intro x y z g
  rw [dualWhittakerFn3_apply, dualWhittakerFn3_apply, transposeInv3_mul_aux7, ← mul_assoc,
    AddChar.inv_apply, longWeyl3_mul_transposeInv3_upperUnipotent3_aux7, mul_assoc,
    hW (-y) (-x) (x * y - z) (longWeyl3 * transposeInv3 g), show -y + -x = -(x + y) by ring]

private theorem dualWhittakerFn3_dualWhittakerFn3_aux7 {R : Type*} (W : GL (Fin 3) A → R) :
    dualWhittakerFn3 (dualWhittakerFn3 W) = W := by
  funext g
  rw [dualWhittakerFn3_apply, dualWhittakerFn3_apply, transposeInv3_mul_aux7, transposeInv3_longWeyl3_aux7,
    transposeInv3_transposeInv3_aux7, ← mul_assoc, longWeyl3_mul_self_aux7, one_mul]

private theorem dualWhittakerFn3_apply_mul_weylPrime3_mul_transposeInv3_aux7 {R : Type*} (W : GL (Fin 3) A → R)
    (h g : GL (Fin 3) A) :
    dualWhittakerFn3 W (h * (weylPrime3 * transposeInv3 g)) =
      W (longWeyl3 * transposeInv3 h * weylPrime3 * g) := by
  rw [dualWhittakerFn3_apply, transposeInv3_mul_aux7, transposeInv3_mul_aux7, transposeInv3_weylPrime3,
    transposeInv3_transposeInv3_aux7, ← mul_assoc, ← mul_assoc]

private theorem weylPrime3_mul_transposeInv3_radicalP21_mul_weylPrime3_eq_aux7 (v : Fin 2 → A) :
    (weylPrime3 * transposeInv3 (radicalP21 v) * weylPrime3 : GL (Fin 3) A) =
      lowerUnipotent21 (-(v 0)) * upperUnipotent3 0 (-(v 1)) 0 := by
  refine Units.ext ?_
  rw [weylPrime3_mul_transposeInv3_radicalP21_mul_weylPrime3]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_three]

end TransposeDual
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_mirabolicSeries_eq_dual_of_radicalCoefficient_eq.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_mirabolicSeries_eq_dual_of_radicalCoefficient_eq.LanglandsTunnell.CubicInduction"

section RationalPoints

private theorem globalPointsGL_transposeInv3_aux7 (h : GL (Fin 3) ℚ) :
    globalPointsGL 3 (𝓞 ℚ) ℚ (transposeInv3 h) = transposeInv3 (globalPointsGL 3 (𝓞 ℚ) ℚ h) := by
  refine Units.ext ?_
  have h1 : ((globalPointsGL 3 (𝓞 ℚ) ℚ h)⁻¹ : GL (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) = globalPointsGL 3 (𝓞 ℚ) ℚ h⁻¹ :=
    (map_inv (globalPointsGL 3 (𝓞 ℚ) ℚ) h).symm
  change ((((h⁻¹ : GL (Fin 3) ℚ) : Matrix (Fin 3) (Fin 3) ℚ))ᵀ).map (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ)) =
    ((((globalPointsGL 3 (𝓞 ℚ) ℚ h)⁻¹ : GL (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)))ᵀ
  rw [h1]
  ext i j
  rfl

private theorem globalPointsGL_weylPrime3_aux7 : globalPointsGL 3 (𝓞 ℚ) ℚ weylPrime3 = weylPrime3 := by
  refine Units.ext ?_
  ext i j
  fin_cases i <;> fin_cases j <;> simp [globalPointsGL]

private theorem globalPointsGL_iotaGL_eq (h : GL (Fin 2) ℚ) :
    globalPointsGL 3 (𝓞 ℚ) ℚ (iotaGL h) = iotaGL (globalPoints (𝓞 ℚ) ℚ h) := by
  refine Units.ext ?_
  ext i j
  fin_cases i <;> fin_cases j <;> simp [globalPointsGL, globalPoints, embedMat2]

end RationalPoints
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_mirabolicSeries_eq_dual_of_radicalCoefficient_eq.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_mirabolicSeries_eq_dual_of_radicalCoefficient_eq.LanglandsTunnell.CubicInduction"

section Twist

private theorem isGlobalAddChar_inv {ψ : AddChar 𝔸 ℂ} (hψ : IsGlobalAddChar ℚ ψ) : IsGlobalAddChar ℚ ψ⁻¹ where
  principalInvariant := fun q => by rw [AddChar.inv_apply, ← map_neg, hψ.principalInvariant]
  continuous := by
    have h : (⇑(ψ⁻¹ : AddChar 𝔸 ℂ) : 𝔸 → ℂ) = fun x => ψ (-x) := funext fun x => AddChar.inv_apply ψ x
    rw [h]
    exact hψ.continuous.comp continuous_neg
  nontrivial := inv_ne_one.mpr hψ.nontrivial

private theorem inv_apply_principal_eq_one {ω : 𝔸ˣ →* ℂˣ} (hω : IsAdmissibleTwist ℚ ω) (q : ℚˣ) :
    (ω⁻¹ : 𝔸ˣ →* ℂˣ) (Units.map (algebraMap ℚ 𝔸).toMonoidHom q) = 1 := by
  rw [MonoidHom.inv_apply, show ω (Units.map (algebraMap ℚ 𝔸).toMonoidHom q) = 1 from hω.1 q, inv_one]

end Twist
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_mirabolicSeries_eq_dual_of_radicalCoefficient_eq.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_mirabolicSeries_eq_dual_of_radicalCoefficient_eq.LanglandsTunnell.CubicInduction"

section Central

private theorem coe_centralScalarGL (z : 𝔸ˣ) :
    ((centralScalarGL 3 (𝓞 ℚ) ℚ z : GL (Fin 3) 𝔸) : Matrix (Fin 3) (Fin 3) 𝔸) = Matrix.scalar (Fin 3) (z : 𝔸) :=
  rfl

private theorem transposeInv3_centralScalarGL (z : 𝔸ˣ) :
    transposeInv3 (centralScalarGL 3 (𝓞 ℚ) ℚ z) = centralScalarGL 3 (𝓞 ℚ) ℚ z⁻¹ := by
  refine Units.ext ?_
  change (((centralScalarGL 3 (𝓞 ℚ) ℚ z)⁻¹ : GL (Fin 3) 𝔸) : Matrix (Fin 3) (Fin 3) 𝔸)ᵀ = _
  rw [← map_inv (centralScalarGL 3 (𝓞 ℚ) ℚ) z, coe_centralScalarGL]
  ext i j
  by_cases hij : i = j <;> simp [Matrix.transpose_apply, Matrix.scalar_apply, hij, eq_comm]

private theorem dualWhittakerFn3_centralScalarGL_mul {ω : 𝔸ˣ →* ℂˣ} {W : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ}
    (hWω : ∀ (z : 𝔸ˣ) (g : AdelicGL 3 (𝓞 ℚ) ℚ), W (centralScalarGL 3 (𝓞 ℚ) ℚ z * g) = (ω z : ℂ) * W g)
    (z : 𝔸ˣ) (g : AdelicGL 3 (𝓞 ℚ) ℚ) :
    dualWhittakerFn3 W (centralScalarGL 3 (𝓞 ℚ) ℚ z * g) = ((ω⁻¹ : 𝔸ˣ →* ℂˣ) z : ℂ) * dualWhittakerFn3 W g := by
  rw [dualWhittakerFn3_apply, dualWhittakerFn3_apply, transposeInv3_mul_aux7, transposeInv3_centralScalarGL, ←
      mul_assoc,
    ← centralScalarGL_mul_comm, mul_assoc, hWω, MonoidHom.inv_apply, map_inv]

end Central
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_mirabolicSeries_eq_dual_of_radicalCoefficient_eq.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_mirabolicSeries_eq_dual_of_radicalCoefficient_eq.LanglandsTunnell.CubicInduction"

section LowerTriangular

variable (c : ℚ) (β : ℚˣ)

private def lowerRat : GL (Fin 2) ℚ where
  val := !![1, 0; c, (β : ℚ)]
  inv := !![1, 0; -c / (β : ℚ), ((β⁻¹ : ℚˣ) : ℚ)]
  val_inv := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;>
      first | ring1 | (field_simp; done) | (field_simp; ring1)
  inv_val := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;>
      first | ring1 | (field_simp; done) | (field_simp; ring1)

@[scoped simp] private theorem lowerRat_coe
    : ((lowerRat c β : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) = !![1, 0; c, (β : ℚ)] :=
  rfl

private def lowerRatInv : GL (Fin 2) ℚ where
  val := !![1, 0; -c / (β : ℚ), ((β⁻¹ : ℚˣ) : ℚ)]
  inv := !![1, 0; c, (β : ℚ)]
  val_inv := (lowerRat c β).inv_val
  inv_val := (lowerRat c β).val_inv

private theorem lowerRatInv_coe :
    ((lowerRatInv c β : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) = !![1, 0; -c / (β : ℚ), ((β⁻¹ : ℚˣ) : ℚ)] :=
  rfl

private theorem lowerRat_inv : (lowerRat c β)⁻¹ = lowerRatInv c β :=
  Units.ext rfl

private theorem globalPoints_lowerRat_apply_zero_zero :
    ((globalPoints (𝓞 ℚ) ℚ (lowerRat c β) : GL (Fin 2) 𝔸) : Matrix (Fin 2) (Fin 2) 𝔸) 0 0 = 1 := by
  rw [globalPoints_apply]; simp

private theorem globalPoints_lowerRat_apply_zero_one :
    ((globalPoints (𝓞 ℚ) ℚ (lowerRat c β) : GL (Fin 2) 𝔸) : Matrix (Fin 2) (Fin 2) 𝔸) 0 1 = 0 := by
  rw [globalPoints_apply]; simp

private theorem globalPoints_lowerRat_apply_one_zero :
    ((globalPoints (𝓞 ℚ) ℚ (lowerRat c β) : GL (Fin 2) 𝔸) : Matrix (Fin 2) (Fin 2) 𝔸) 1 0 = algebraMap ℚ 𝔸 c := by
  rw [globalPoints_apply]; simp

private theorem globalPoints_lowerRat_apply_one_one :
    ((globalPoints (𝓞 ℚ) ℚ (lowerRat c β) : GL (Fin 2) 𝔸) : Matrix (Fin 2) (Fin 2) 𝔸) 1 1 =
      algebraMap ℚ 𝔸 (β : ℚ) := by
  rw [globalPoints_apply]; simp

private def parabolicRat : GL (Fin 3) ℚ where
  val := !![1, 0, -c / (β : ℚ); 0, 1, 0; 0, 0, ((β⁻¹ : ℚˣ) : ℚ)]
  inv := !![1, 0, c; 0, 1, 0; 0, 0, (β : ℚ)]
  val_inv := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three] <;>
      first | ring1 | (field_simp; done) | (field_simp; ring1)
  inv_val := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three] <;>
      first | ring1 | (field_simp; done) | (field_simp; ring1)

private theorem parabolicRat_coe :
    ((parabolicRat c β : GL (Fin 3) ℚ) : Matrix (Fin 3) (Fin 3) ℚ) =
      !![1, 0, -c / (β : ℚ); 0, 1, 0; 0, 0, ((β⁻¹ : ℚˣ) : ℚ)] :=
  rfl

private theorem weylPrime3_mul_transposeInv3_iotaGL_lowerRat :
    (weylPrime3 * transposeInv3 (iotaGL (lowerRat c β)) : GL (Fin 3) ℚ) = parabolicRat c β * weylPrime3 := by
  refine Units.ext ?_
  rw [Units.val_mul, Units.val_mul]
  change (weylPrime3 : GL (Fin 3) ℚ).val * ((((iotaGL (lowerRat c β))⁻¹ : GL (Fin 3) ℚ) : Matrix (Fin 3) (Fin 3) ℚ))ᵀ =
    (parabolicRat c β : Matrix (Fin 3) (Fin 3) ℚ) * (weylPrime3 : GL (Fin 3) ℚ).val
  rw [← map_inv iotaGL, lowerRat_inv, parabolicRat_coe, coe_iotaGL, lowerRatInv_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [embedMat2, Matrix.mul_apply, Fin.sum_univ_three, Matrix.transpose_apply]

private theorem weylPrime3_mul_transposeInv3_iotaGL_globalPoints_lowerRat :
    (weylPrime3 * transposeInv3 (iotaGL (globalPoints (𝓞 ℚ) ℚ (lowerRat c β))) : AdelicGL 3 (𝓞 ℚ) ℚ) =
      globalPointsGL 3 (𝓞 ℚ) ℚ (parabolicRat c β) * weylPrime3 := by
  rw [← globalPointsGL_iotaGL_eq, ← globalPointsGL_transposeInv3_aux7, ← globalPointsGL_weylPrime3_aux7, ← map_mul, ←
      map_mul,
    weylPrime3_mul_transposeInv3_iotaGL_lowerRat]

private theorem tsum_dualWhittakerFn3_weylPrime3_mul_transposeInv3_iotaGL_lowerRat_mul {ψ : AddChar 𝔸 ℂ}
    (hψ : IsGlobalAddChar ℚ ψ) {W : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ} (hW : IsGL3PsiWhittakerFn ψ W) {ω : 𝔸ˣ →* ℂˣ}
    (hω : IsAdmissibleTwist ℚ ω)
    (hWω : ∀ (z : 𝔸ˣ) (g : AdelicGL 3 (𝓞 ℚ) ℚ), W (centralScalarGL 3 (𝓞 ℚ) ℚ z * g) = (ω z : ℂ) * W g)
    (g : AdelicGL 3 (𝓞 ℚ) ℚ) :
    ∑' i : MirabolicIndex ℚ, dualWhittakerFn3 W (mirabolicTranslate i *
        (weylPrime3 * transposeInv3 (iotaGL (globalPoints (𝓞 ℚ) ℚ (lowerRat c β)) * g))) =
      ∑' i : MirabolicIndex ℚ, dualWhittakerFn3 W (mirabolicTranslate i * (weylPrime3 * transposeInv3 g)) := by
  have h1 : (weylPrime3 * transposeInv3 (iotaGL (globalPoints (𝓞 ℚ) ℚ (lowerRat c β)) * g) : AdelicGL 3 (𝓞 ℚ) ℚ) =
      globalPointsGL 3 (𝓞 ℚ) ℚ (parabolicRat c β) * (weylPrime3 * transposeInv3 g) := by
    rw [transposeInv3_mul_aux7, ← mul_assoc, weylPrime3_mul_transposeInv3_iotaGL_globalPoints_lowerRat, mul_assoc]
  rw [h1]
  change mirabolicSeries (dualWhittakerFn3 W)
      (globalPointsGL 3 (𝓞 ℚ) ℚ (parabolicRat c β) * (weylPrime3 * transposeInv3 g)) =
    mirabolicSeries (dualWhittakerFn3 W) (weylPrime3 * transposeInv3 g)
  exact mirabolicSeries_globalPointsGL_mul_of_parabolic (isGlobalAddChar_inv hψ)
    (isGL3PsiWhittakerFn_dualWhittakerFn3_aux7 ψ hW) (dualWhittakerFn3_centralScalarGL_mul hWω)
    (inv_apply_principal_eq_one hω) (parabolicRat c β) (by simp [parabolicRat_coe]) (by simp [parabolicRat_coe]) _

end LowerTriangular
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_mirabolicSeries_eq_dual_of_radicalCoefficient_eq.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_mirabolicSeries_eq_dual_of_radicalCoefficient_eq.LanglandsTunnell.CubicInduction"

section Radical

variable (t₁ t₂ : ℚ)

private theorem globalPointsGL_radicalP21 :
    globalPointsGL 3 (𝓞 ℚ) ℚ (radicalP21 ![t₁, t₂]) = radicalP21 ![algebraMap ℚ 𝔸 t₁, algebraMap ℚ 𝔸 t₂] := by
  show globalPointsGL 3 (𝓞 ℚ) ℚ (upperUnipotent3 0 t₂ t₁) = upperUnipotent3 0 (algebraMap ℚ 𝔸 t₂) (algebraMap ℚ 𝔸 t₁)
  rw [globalPointsGL_upperUnipotent3, map_zero]

private theorem weylPrime3_mul_transposeInv3_radicalP21_rat :
    (weylPrime3 * transposeInv3 (radicalP21 ![t₁, t₂]) : GL (Fin 3) ℚ) =
      lowerUnipotent21 (-t₁) * upperUnipotent3 0 (-t₂) 0 * weylPrime3 := by
  have h := weylPrime3_mul_transposeInv3_radicalP21_mul_weylPrime3_eq_aux7 (A := ℚ) ![t₁, t₂]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] at h
  calc (weylPrime3 * transposeInv3 (radicalP21 ![t₁, t₂]) : GL (Fin 3) ℚ)
      = weylPrime3 * transposeInv3 (radicalP21 ![t₁, t₂]) * (weylPrime3 * weylPrime3) := by
        rw [weylPrime3_mul_self, mul_one]
    _ = weylPrime3 * transposeInv3 (radicalP21 ![t₁, t₂]) * weylPrime3 * weylPrime3 := by simp only [mul_assoc]
    _ = lowerUnipotent21 (-t₁) * upperUnipotent3 0 (-t₂) 0 * weylPrime3 := by rw [h]

private theorem weylPrime3_mul_transposeInv3_radicalP21_algebraMap :
    (weylPrime3 * transposeInv3 (radicalP21 ![algebraMap ℚ 𝔸 t₁, algebraMap ℚ 𝔸 t₂]) : AdelicGL 3 (𝓞 ℚ) ℚ) =
      globalPointsGL 3 (𝓞 ℚ) ℚ (lowerUnipotent21 (-t₁) * upperUnipotent3 0 (-t₂) 0) * weylPrime3 := by
  rw [← globalPointsGL_radicalP21, ← globalPointsGL_transposeInv3_aux7, ← globalPointsGL_weylPrime3_aux7, ← map_mul, ←
      map_mul,
    weylPrime3_mul_transposeInv3_radicalP21_rat]

private theorem tsum_dualWhittakerFn3_weylPrime3_mul_transposeInv3_radicalP21_mul {ψ : AddChar 𝔸 ℂ}
    (hψ : IsGlobalAddChar ℚ ψ) {W : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ} (hW : IsGL3PsiWhittakerFn ψ W) {ω : 𝔸ˣ →* ℂˣ}
    (hω : IsAdmissibleTwist ℚ ω)
    (hWω : ∀ (z : 𝔸ˣ) (g : AdelicGL 3 (𝓞 ℚ) ℚ), W (centralScalarGL 3 (𝓞 ℚ) ℚ z * g) = (ω z : ℂ) * W g)
    (g : AdelicGL 3 (𝓞 ℚ) ℚ) :
    ∑' i : MirabolicIndex ℚ, dualWhittakerFn3 W (mirabolicTranslate i *
        (weylPrime3 * transposeInv3 (radicalP21 ![algebraMap ℚ 𝔸 t₁, algebraMap ℚ 𝔸 t₂] * g))) =
      ∑' i : MirabolicIndex ℚ, dualWhittakerFn3 W (mirabolicTranslate i * (weylPrime3 * transposeInv3 g)) := by
  have h1 : (weylPrime3 * transposeInv3 (radicalP21 ![algebraMap ℚ 𝔸 t₁, algebraMap ℚ 𝔸 t₂] * g) :
      AdelicGL 3 (𝓞 ℚ) ℚ) =
      globalPointsGL 3 (𝓞 ℚ) ℚ (lowerUnipotent21 (-t₁) * upperUnipotent3 0 (-t₂) 0) *
        (weylPrime3 * transposeInv3 g) := by
    rw [transposeInv3_mul_aux7, ← mul_assoc, weylPrime3_mul_transposeInv3_radicalP21_algebraMap, mul_assoc]
  rw [h1]
  change mirabolicSeries (dualWhittakerFn3 W)
      (globalPointsGL 3 (𝓞 ℚ) ℚ (lowerUnipotent21 (-t₁) * upperUnipotent3 0 (-t₂) 0) *
        (weylPrime3 * transposeInv3 g)) =
    mirabolicSeries (dualWhittakerFn3 W) (weylPrime3 * transposeInv3 g)
  exact mirabolicSeries_globalPointsGL_mul_of_parabolic (isGlobalAddChar_inv hψ)
    (isGL3PsiWhittakerFn_dualWhittakerFn3_aux7 ψ hW) (dualWhittakerFn3_centralScalarGL_mul hWω)
    (inv_apply_principal_eq_one hω) (lowerUnipotent21 (-t₁) * upperUnipotent3 0 (-t₂) 0)
    (by simp [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_three])
    (by simp [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_three]) _

end Radical
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_mirabolicSeries_eq_dual_of_radicalCoefficient_eq.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_mirabolicSeries_eq_dual_of_radicalCoefficient_eq.LanglandsTunnell.CubicInduction"
end
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_mirabolicSeries_eq_dual_of_radicalCoefficient_eq.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_mirabolicSeries_eq_dual_of_radicalCoefficient_eq.LanglandsTunnell.CubicInduction"
end LanglandsTunnell.CubicInduction
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_mirabolicSeries_eq_dual_of_radicalCoefficient_eq.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_mirabolicSeries_eq_dual_of_radicalCoefficient_eq.LanglandsTunnell.CubicInduction"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_mirabolicSeries_eq_dual_of_radicalCoefficient_eq.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_mirabolicSeries_eq_dual_of_radicalCoefficient_eq.LanglandsTunnell.CubicInduction"

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "Converse.IsAdmissibleTwist TateLocal.addCharLevel TateLocal.localBorel TateLocal.borelSpace_localBorel TateLocal.integersPositiveCompacts TateLocal.coe_integersPositiveCompacts TateLocal.selfDualHaarAt TateLocal.higherUnitsAt TateLocal.forall_eq_one_and_exists_ne_one_of_addCharLevel"
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "matrixFin_ext matrixAdele_ext localMatN mapMatrix_localMatN_self mapMatrix_localMatN_of_ne finMatN mapMatrix_arch_finMatN mapMatrix_fin_finMatN localToAdelic3 converseCongruenceSet3 HasVanishingUnipotentIntegralAlong IsCongruenceEquivariantAlong lowerUnipotent21 longWeyl3 longWeyl3_coe dualWhittakerFn3 dualWhittakerFn3_apply weylPrime3 weylPrime3_coe weylPrime3_mul_self transposeInv3_weylPrime3 weylPrime3_mul_transposeInv3_radicalP21_mul_weylPrime3 IsGL3PsiWhittakerFn transposeInv3 IsCuspidalAlongP21 psiLoc mirabolicTranslate AdelicGL globalPointsGL centralScalarGL upperUnipotent3 upperUnipotent3_coe upperUnipotent3_zero radicalP21 radicalP21_zero radicalP21_coe radicalP21_add embedMat2 iotaGL coe_iotaGL iota MirabolicIndex mirabolicRep mirabolicRep_spec mirabolic_mk_unipotent_mul localMaximalCompact3 componentAtN archComponentN componentAt3 archComponent3 LocalGL3 cosetSum IsCosetEigenfunction IsRightInvariant diagUnitGL2 diagHom diagHom_apply isCuspidalAlongP21_mirabolicSeries"
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"
section
open IsDedekindDomain NumberField Matrix

section Generic

variable {A : Type*} [CommRing A] [TopologicalSpace A]

private theorem continuous_transposeInv3' : Continuous (transposeInv3 : GL (Fin 3) A → GL (Fin 3) A) := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · show Continuous fun g : GL (Fin 3) A => (((g⁻¹ : GL (Fin 3) A)) : Matrix (Fin 3) (Fin 3) A)ᵀ
    exact Units.continuous_coe_inv.matrix_transpose
  · show Continuous fun g : GL (Fin 3) A => (((g : GL (Fin 3) A)) : Matrix (Fin 3) (Fin 3) A)ᵀ
    exact Units.continuous_val.matrix_transpose

variable [IsTopologicalRing A]

private theorem continuous_upperUnipotent3_of {X : Type*} [TopologicalSpace X] {x y z : X → A}
    (hx : Continuous x) (hy : Continuous y) (hz : Continuous z) :
    Continuous fun p : X => upperUnipotent3 (x p) (y p) (z p) := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · show Continuous fun p : X => (!![1, x p, z p; 0, 1, y p; 0, 0, 1] : Matrix (Fin 3) (Fin 3) A)
    refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp <;> fun_prop
  · show Continuous fun p : X =>
      (!![1, -x p, x p * y p - z p; 0, 1, -(y p); 0, 0, 1] : Matrix (Fin 3) (Fin 3) A)
    refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp <;> fun_prop

private theorem continuous_radicalP21_pair : Continuous fun p : A × A => radicalP21 ![p.1, p.2] := by
  show Continuous fun p : A × A => upperUnipotent3 0 p.2 p.1
  exact continuous_upperUnipotent3_of continuous_const continuous_snd continuous_fst

end Generic
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_mirabolicSeries_eq_dual_of_radicalCoefficient_eq.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_mirabolicSeries_eq_dual_of_radicalCoefficient_eq.LanglandsTunnell.CubicInduction"

private theorem continuous_dualSeries_radical_slice_of_continuous (W : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)
    (_hcont' : Continuous fun g => ∑' i : MirabolicIndex ℚ, dualWhittakerFn3 W (mirabolicTranslate i * g)) :
    ∀ X : AdelicGL 3 (𝓞 ℚ) ℚ, Continuous fun p : 𝔸 × 𝔸 =>
      (∑' i : MirabolicIndex ℚ, dualWhittakerFn3 W (mirabolicTranslate i
          * (weylPrime3 * transposeInv3 (radicalP21 ![p.1, p.2] * X)))) :=
  fun _ => _hcont'.comp (continuous_const.mul (continuous_transposeInv3'.comp
    (continuous_radicalP21_pair.mul continuous_const)))
end
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_mirabolicSeries_eq_dual_of_radicalCoefficient_eq.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_mirabolicSeries_eq_dual_of_radicalCoefficient_eq.LanglandsTunnell.CubicInduction"
end LanglandsTunnell.CubicInduction
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_mirabolicSeries_eq_dual_of_radicalCoefficient_eq.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_mirabolicSeries_eq_dual_of_radicalCoefficient_eq.LanglandsTunnell.CubicInduction"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_mirabolicSeries_eq_dual_of_radicalCoefficient_eq.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_mirabolicSeries_eq_dual_of_radicalCoefficient_eq.LanglandsTunnell.CubicInduction"

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "Converse.IsAdmissibleTwist TateLocal.addCharLevel TateLocal.localBorel TateLocal.borelSpace_localBorel TateLocal.integersPositiveCompacts TateLocal.coe_integersPositiveCompacts TateLocal.selfDualHaarAt TateLocal.higherUnitsAt TateLocal.forall_eq_one_and_exists_ne_one_of_addCharLevel"
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "matrixFin_ext matrixAdele_ext localMatN mapMatrix_localMatN_self mapMatrix_localMatN_of_ne finMatN mapMatrix_arch_finMatN mapMatrix_fin_finMatN localToAdelic3 converseCongruenceSet3 HasVanishingUnipotentIntegralAlong IsCongruenceEquivariantAlong lowerUnipotent21 longWeyl3 longWeyl3_coe dualWhittakerFn3 dualWhittakerFn3_apply weylPrime3 weylPrime3_coe weylPrime3_mul_self transposeInv3_weylPrime3 weylPrime3_mul_transposeInv3_radicalP21_mul_weylPrime3 IsGL3PsiWhittakerFn transposeInv3 IsCuspidalAlongP21 psiLoc mirabolicTranslate AdelicGL globalPointsGL centralScalarGL upperUnipotent3 upperUnipotent3_coe upperUnipotent3_zero radicalP21 radicalP21_zero radicalP21_coe radicalP21_add embedMat2 iotaGL coe_iotaGL iota MirabolicIndex mirabolicRep mirabolicRep_spec mirabolic_mk_unipotent_mul localMaximalCompact3 componentAtN archComponentN componentAt3 archComponent3 LocalGL3 cosetSum IsCosetEigenfunction IsRightInvariant diagUnitGL2 diagHom diagHom_apply isCuspidalAlongP21_mirabolicSeries"
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"
section
open IsDedekindDomain NumberField NumberField.AdelicHaar AutomorphicForm Matrix MeasureTheory LanglandsTunnell.Converse
open scoped NNReal ENNReal Pointwise ProbabilityTheory

section IotaGlue

private theorem mirabolicSeries_iotaGL_globalPoints_mul
    (ψ : AddChar 𝔸 ℂ) (hψ : IsGlobalAddChar ℚ ψ) (W : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hW : IsGL3PsiWhittakerFn ψ W)
    (A : GL (Fin 2) ℚ) (g : AdelicGL 3 (𝓞 ℚ) ℚ) :
    (∑' i : MirabolicIndex ℚ, W (mirabolicTranslate i * (iotaGL (globalPoints (𝓞 ℚ) ℚ A) * g))) =
        (∑' i : MirabolicIndex ℚ, W (mirabolicTranslate i * (g))) :=
  mirabolicSeries_iota_globalPoints_mul hψ hW A g

private theorem primal_sub_dual_iotaGL_globalPoints_mul
    (ψ : AddChar 𝔸 ℂ) (hψ : IsGlobalAddChar ℚ ψ) (W : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hW : IsGL3PsiWhittakerFn ψ W)
    (A : GL (Fin 2) ℚ)
    (hι₁ : ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ, (∑' i : MirabolicIndex ℚ, dualWhittakerFn3 W (mirabolicTranslate i
        * (weylPrime3 * transposeInv3 (iotaGL (globalPoints (𝓞 ℚ) ℚ A) * g)))) = (∑' i : MirabolicIndex ℚ,
        dualWhittakerFn3 W (mirabolicTranslate i * (weylPrime3 * transposeInv3 (g)))))
    (g : AdelicGL 3 (𝓞 ℚ) ℚ) :
    (∑' i : MirabolicIndex ℚ, W (mirabolicTranslate i * (iotaGL (globalPoints (𝓞 ℚ) ℚ A) * g))) -
        (∑' i : MirabolicIndex ℚ, dualWhittakerFn3 W (mirabolicTranslate i
        * (weylPrime3 * transposeInv3 (iotaGL (globalPoints (𝓞 ℚ) ℚ A) * g)))) = (∑' i : MirabolicIndex ℚ,
        W (mirabolicTranslate i * (g))) - (∑' i : MirabolicIndex ℚ,
        dualWhittakerFn3 W (mirabolicTranslate i * (weylPrime3 * transposeInv3 (g)))) := by
  rw [mirabolicSeries_iotaGL_globalPoints_mul ψ hψ W hW A g, hι₁ g]

end IotaGlue
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_mirabolicSeries_eq_dual_of_radicalCoefficient_eq.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_mirabolicSeries_eq_dual_of_radicalCoefficient_eq.LanglandsTunnell.CubicInduction"

private noncomputable def radicalDifference (W : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (g : AdelicGL 3 (𝓞 ℚ) ℚ) (z y : 𝔸) : ℂ :=
  (∑' i : MirabolicIndex ℚ, W (mirabolicTranslate i * (radicalP21 ![z, y] * g))) -
    (∑' i : MirabolicIndex ℚ, dualWhittakerFn3 W (mirabolicTranslate i
      * (weylPrime3 * transposeInv3 (radicalP21 ![z, y] * g))))

private noncomputable def boxCoefficient (ψ : AddChar 𝔸 ℂ) (F : 𝔸 → 𝔸 → ℂ) (α β : ℚ) : ℂ :=
  ∫ z, (∫ y, F z y * ψ (-(algebraMap ℚ 𝔸 β * y)) ∂μbox) * ψ (-(algebraMap ℚ 𝔸 α * z)) ∂μbox

private noncomputable def radicalCoefficient (ψ : AddChar 𝔸 ℂ) (W : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (g : AdelicGL 3 (𝓞 ℚ) ℚ)
    (α β : ℚ) : ℂ :=
  boxCoefficient ψ (radicalDifference W g) α β

private theorem radicalDifference_apply (W : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (g : AdelicGL 3 (𝓞 ℚ) ℚ) (z y : 𝔸) :
    radicalDifference W g z y =
      (∑' i : MirabolicIndex ℚ, W (mirabolicTranslate i * (radicalP21 ![z, y] * g))) -
        (∑' i : MirabolicIndex ℚ, dualWhittakerFn3 W (mirabolicTranslate i
          * (weylPrime3 * transposeInv3 (radicalP21 ![z, y] * g)))) := by
  rfl

private theorem radicalCoefficient_eq
    (ψ : AddChar 𝔸 ℂ) (W : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (g : AdelicGL 3 (𝓞 ℚ) ℚ) (α β : ℚ) :
    radicalCoefficient ψ W g α β =
      ∫ z, (∫ y, radicalDifference W g z y * ψ (-(algebraMap ℚ 𝔸 β * y)) ∂μbox) *
        ψ (-(algebraMap ℚ 𝔸 α * z)) ∂μbox := by
  rfl

private theorem boxCoefficient_sub {ψ : AddChar 𝔸 ℂ} (hψ : IsGlobalAddChar ℚ ψ) (F F₁ : 𝔸 → 𝔸 → ℂ)
    (hF : Continuous fun p : 𝔸 × 𝔸 => F p.1 p.2) (hF₁ : Continuous fun p : 𝔸 × 𝔸 => F₁ p.1 p.2) (α β : ℚ) :
    boxCoefficient ψ (fun z y => F z y - F₁ z y) α β = boxCoefficient ψ F α β - boxCoefficient ψ F₁ α β := by
  simp only [boxCoefficient]
  have hinner : ∀ z : 𝔸,
      (∫ y, (F z y - F₁ z y) * ψ (-(algebraMap ℚ 𝔸 β * y)) ∂μbox) =
        (∫ y, F z y * ψ (-(algebraMap ℚ 𝔸 β * y)) ∂μbox) - ∫ y, F₁ z y * ψ (-(algebraMap ℚ 𝔸 β * y)) ∂μbox := by
    intro z
    simp_rw [sub_mul]
    exact integral_sub (integrable_slice_mul_addChar hψ hF β z) (integrable_slice_mul_addChar hψ hF₁ β z)
  simp_rw [hinner, sub_mul]
  refine integral_sub ?_ ?_
  · exact integrable_slice_mul_addChar hψ (F := fun _ z => ∫ y, F z y * ψ (-(algebraMap ℚ 𝔸 β * y)) ∂μbox)
      ((continuous_integral_slice_mul_addChar hψ hF β).comp continuous_snd) α 0
  · exact integrable_slice_mul_addChar hψ (F := fun _ z => ∫ y, F₁ z y * ψ (-(algebraMap ℚ 𝔸 β * y)) ∂μbox)
      ((continuous_integral_slice_mul_addChar hψ hF₁ β).comp continuous_snd) α 0

private theorem continuous_radicalDifference
    (ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ) (_hψ : IsGlobalAddChar ℚ ψ)
    (W : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)
    (_hW : IsGL3PsiWhittakerFn ψ W)
    (_hsum : ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ, Summable fun i : MirabolicIndex ℚ => W (mirabolicTranslate i * g))
    (_hcont' : Continuous fun g => ∑' i : MirabolicIndex ℚ, dualWhittakerFn3 W (mirabolicTranslate i * g))
    (g : AdelicGL 3 (𝓞 ℚ) ℚ) :
    Continuous fun p : 𝔸 × 𝔸 => radicalDifference W g p.1 p.2 := by
  exact (continuous_mirabolicSeries_radical _hψ _hW g (_hsum g)).sub
    (continuous_dualSeries_radical_slice_of_continuous W _hcont' g)

private theorem radicalDifference_fst_periodic
    (ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ) (_hψ : IsGlobalAddChar ℚ ψ)
    (ω : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (_hω : IsAdmissibleTwist ℚ ω)
    (W : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)
    (_hW : IsGL3PsiWhittakerFn ψ W)
    (_hWω : ∀ (z : (AdeleRing (𝓞 ℚ) ℚ)ˣ) (g : AdelicGL 3 (𝓞 ℚ) ℚ),
      W (centralScalarGL 3 (𝓞 ℚ) ℚ z * g) = (ω z : ℂ) * W g)
    (g : AdelicGL 3 (𝓞 ℚ) ℚ) (q : ℚ) (z y : 𝔸) :
    radicalDifference W g (algebraMap ℚ 𝔸 q + z) y = radicalDifference W g z y := by
  have hrad₁ := fun (t₁ t₂ : ℚ) (g : AdelicGL 3 (𝓞 ℚ) ℚ) =>
    tsum_dualWhittakerFn3_weylPrime3_mul_transposeInv3_radicalP21_mul t₁ t₂ _hψ _hW _hω _hWω g
  exact primal_sub_dual_radical_fst_periodic ψ _hψ W _hW hrad₁ g q z y

private theorem radicalDifference_snd_periodic
    (ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ) (_hψ : IsGlobalAddChar ℚ ψ)
    (ω : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (_hω : IsAdmissibleTwist ℚ ω)
    (W : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)
    (_hW : IsGL3PsiWhittakerFn ψ W)
    (_hWω : ∀ (z : (AdeleRing (𝓞 ℚ) ℚ)ˣ) (g : AdelicGL 3 (𝓞 ℚ) ℚ),
      W (centralScalarGL 3 (𝓞 ℚ) ℚ z * g) = (ω z : ℂ) * W g)
    (g : AdelicGL 3 (𝓞 ℚ) ℚ) (q : ℚ) (z y : 𝔸) :
    radicalDifference W g z (algebraMap ℚ 𝔸 q + y) = radicalDifference W g z y := by
  have hrad₁ := fun (t₁ t₂ : ℚ) (g : AdelicGL 3 (𝓞 ℚ) ℚ) =>
    tsum_dualWhittakerFn3_weylPrime3_mul_transposeInv3_radicalP21_mul t₁ t₂ _hψ _hW _hω _hWω g
  exact primal_sub_dual_radical_snd_periodic ψ _hψ W _hW hrad₁ g q z y

private theorem radicalCoefficient_eq_zero_one_iotaGL_lowerRat_mul
    (ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ) (_hψ : IsGlobalAddChar ℚ ψ)
    (ω : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (_hω : IsAdmissibleTwist ℚ ω)
    (W : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)
    (_hW : IsGL3PsiWhittakerFn ψ W)
    (_hWω : ∀ (z : (AdeleRing (𝓞 ℚ) ℚ)ˣ) (g : AdelicGL 3 (𝓞 ℚ) ℚ),
      W (centralScalarGL 3 (𝓞 ℚ) ℚ z * g) = (ω z : ℂ) * W g)
    (g : AdelicGL 3 (𝓞 ℚ) ℚ) (α β : ℚ) (hβ : β ≠ 0) :
    radicalCoefficient ψ W g α β =
      radicalCoefficient ψ W (iotaGL (globalPoints (𝓞 ℚ) ℚ (lowerRat α (Units.mk0 β hβ))) * g) 0 1 := by
  have hrad₁ := fun (t₁ t₂ : ℚ) (g : AdelicGL 3 (𝓞 ℚ) ℚ) =>
    tsum_dualWhittakerFn3_weylPrime3_mul_transposeInv3_radicalP21_mul t₁ t₂ _hψ _hW _hω _hWω g
  exact (integral_box_box_radical_coefficient_iotaGL_mul_eq ψ _hψ
    (fun h => (∑' i : MirabolicIndex ℚ, W (mirabolicTranslate i * h)) -
        (∑' i : MirabolicIndex ℚ, dualWhittakerFn3 W (mirabolicTranslate i * (weylPrime3 * transposeInv3 h))))
    g (globalPoints (𝓞 ℚ) ℚ (lowerRat α (Units.mk0 β hβ))) α β hβ
    (globalPoints_lowerRat_apply_zero_zero _ _) (globalPoints_lowerRat_apply_zero_one _ _)
    (globalPoints_lowerRat_apply_one_zero _ _) (globalPoints_lowerRat_apply_one_one _ _)
    (primal_sub_dual_iotaGL_globalPoints_mul ψ _hψ W _hW _ fun h =>
      tsum_dualWhittakerFn3_weylPrime3_mul_transposeInv3_iotaGL_lowerRat_mul α (Units.mk0 β hβ) _hψ _hW _hω _hWω h)
    (fun q z y => primal_sub_dual_radical_snd_periodic ψ _hψ W _hW hrad₁ g q z y)).symm

private theorem radicalCoefficient_zero_right_eq_zero
    (ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ) (_hψ : IsGlobalAddChar ℚ ψ)
    (ω : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (_hω : IsAdmissibleTwist ℚ ω)
    (W : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)
    (_hW : IsGL3PsiWhittakerFn ψ W)
    (_hWω : ∀ (z : (AdeleRing (𝓞 ℚ) ℚ)ˣ) (g : AdelicGL 3 (𝓞 ℚ) ℚ),
      W (centralScalarGL 3 (𝓞 ℚ) ℚ z * g) = (ω z : ℂ) * W g)
    (_hsum : ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ, Summable fun i : MirabolicIndex ℚ => W (mirabolicTranslate i * g))
    (_hsum' : ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ,
      Summable fun i : MirabolicIndex ℚ => dualWhittakerFn3 W (mirabolicTranslate i * g))
    (_hcont' : Continuous fun g => ∑' i : MirabolicIndex ℚ, dualWhittakerFn3 W (mirabolicTranslate i * g))
    (g : AdelicGL 3 (𝓞 ℚ) ℚ) (α : ℚ) (hα : α ≠ 0) :
    radicalCoefficient ψ W g α 0 = 0 := by
  have hcont₁ := continuous_dualSeries_radical_slice_of_continuous W _hcont'
  exact radical_coefficient_zero_primal_sub_dual_eq_zero ψ _hψ W _hW ω _hω _hWω _hsum _hsum' hcont₁ g α hα

private theorem radicalCoefficient_zero_zero_eq_zero
    (ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ) (_hψ : IsGlobalAddChar ℚ ψ)
    (W : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)
    (_hW : IsGL3PsiWhittakerFn ψ W)
    (_hsum : ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ, Summable fun i : MirabolicIndex ℚ => W (mirabolicTranslate i * g))
    (_hsum' : ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ,
      Summable fun i : MirabolicIndex ℚ => dualWhittakerFn3 W (mirabolicTranslate i * g))
    (_hcont' : Continuous fun g => ∑' i : MirabolicIndex ℚ, dualWhittakerFn3 W (mirabolicTranslate i * g))
    (D : Set (AdelicGL2 (𝓞 ℚ) ℚ)) (U : Ideal (𝓞 ℚ) → Subgroup (AdelicGL2 (𝓞 ℚ) ℚ))
    (gen : HeightOneSpectrum (𝓞 ℚ) → AdelicGL2 (𝓞 ℚ) ℚ)
    (_hcusp : IsCuspidalAlongP21 (productionPinsOf ℚ D U gen (AdelicBox.adelicBox ℚ))
      (fun x => ∑' i : MirabolicIndex ℚ, W (mirabolicTranslate i * x)))
    (g : AdelicGL 3 (𝓞 ℚ) ℚ) :
    radicalCoefficient ψ W g 0 0 = 0 := by
  have hcont₁ := continuous_dualSeries_radical_slice_of_continuous W _hcont'
  exact radical_coefficient_zero_zero_primal_sub_dual_eq_zero ψ _hψ W _hW _hsum _hsum' hcont₁ D U gen _hcusp g

private theorem radicalCoefficient_zero_one_eq_zero_of_locus
    (ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ) (_hψ : IsGlobalAddChar ℚ ψ)
    (S : Finset (HeightOneSpectrum (𝓞 ℚ)))
    (a : HeightOneSpectrum (𝓞 ℚ) → ℕ)
    (W : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)
    (_hW : IsGL3PsiWhittakerFn ψ W)
    (_hsum : ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ, Summable fun i : MirabolicIndex ℚ => W (mirabolicTranslate i * g))
    (_hcont' : Continuous fun g => ∑' i : MirabolicIndex ℚ, dualWhittakerFn3 W (mirabolicTranslate i * g))
    (_hV : ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ,
      (∀ v ∈ S, componentAt3 (𝓞 ℚ) ℚ v g ∈ converseCongruenceSet3 v (a v)) →
      (∫ z : AdeleRing (𝓞 ℚ) ℚ, ∫ y : AdeleRing (𝓞 ℚ) ℚ,
          (∑' i : MirabolicIndex ℚ, W (mirabolicTranslate i * (radicalP21 ![z, y] * g))) * ψ (-y)
        ∂(ProbabilityTheory.cond (NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ) (AdelicBox.adelicBox ℚ))
        ∂(ProbabilityTheory.cond (NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ) (AdelicBox.adelicBox ℚ))) =
      ∫ z : AdeleRing (𝓞 ℚ) ℚ, ∫ y : AdeleRing (𝓞 ℚ) ℚ,
          (∑' i : MirabolicIndex ℚ, dualWhittakerFn3 W (mirabolicTranslate i *
            (weylPrime3 * transposeInv3 (radicalP21 ![z, y] * g)))) * ψ (-y)
        ∂(ProbabilityTheory.cond (NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ) (AdelicBox.adelicBox ℚ))
        ∂(ProbabilityTheory.cond (NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ) (AdelicBox.adelicBox ℚ)))
    (g : AdelicGL 3 (𝓞 ℚ) ℚ) :
    (∀ v ∈ S, componentAt3 (𝓞 ℚ) ℚ v g ∈ converseCongruenceSet3 v (a v)) →
      radicalCoefficient ψ W g 0 1 = 0 := by
  intro hg
  have hsplit := boxCoefficient_sub _hψ
    (fun z y => ∑' i : MirabolicIndex ℚ, W (mirabolicTranslate i * (radicalP21 ![z, y] * g)))
    (fun z y => ∑' i : MirabolicIndex ℚ, dualWhittakerFn3 W (mirabolicTranslate i
      * (weylPrime3 * transposeInv3 (radicalP21 ![z, y] * g))))
    (continuous_mirabolicSeries_radical _hψ _hW g (_hsum g))
    (continuous_dualSeries_radical_slice_of_continuous W _hcont' g) 0 1
  refine (hsplit.trans (sub_eq_zero.mpr ?_))
  simpa only [boxCoefficient, map_zero, map_one, zero_mul, one_mul, neg_zero, AddChar.map_zero_eq_one, mul_one]
    using _hV g hg

private theorem mirabolicSeries_eq_dualSeries_of_forall_radicalCoefficient_eq_zero
    (ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ) (_hψ : IsGlobalAddChar ℚ ψ)
    (ω : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (_hω : IsAdmissibleTwist ℚ ω)
    (W : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)
    (_hW : IsGL3PsiWhittakerFn ψ W)
    (_hWω : ∀ (z : (AdeleRing (𝓞 ℚ) ℚ)ˣ) (g : AdelicGL 3 (𝓞 ℚ) ℚ),
      W (centralScalarGL 3 (𝓞 ℚ) ℚ z * g) = (ω z : ℂ) * W g)
    (_hsum : ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ, Summable fun i : MirabolicIndex ℚ => W (mirabolicTranslate i * g))
    (_hcont' : Continuous fun g => ∑' i : MirabolicIndex ℚ, dualWhittakerFn3 W (mirabolicTranslate i * g))
    (g : AdelicGL 3 (𝓞 ℚ) ℚ)
    (h : ∀ α β : ℚ, radicalCoefficient ψ W g α β = 0) :
      (∑' i : MirabolicIndex ℚ, W (mirabolicTranslate i * g)) =
        ∑' i : MirabolicIndex ℚ, dualWhittakerFn3 W (mirabolicTranslate i * (weylPrime3 * transposeInv3 g)) := by
  have h0 := eq_zero_of_forall_integral_box_box_mul_addChar_eq_zero ψ _hψ (radicalDifference W g)
    (continuous_radicalDifference ψ _hψ W _hW _hsum _hcont' g)
    (radicalDifference_fst_periodic ψ _hψ ω _hω W _hW _hWω g)
    (radicalDifference_snd_periodic ψ _hψ ω _hω W _hW _hWω g)
    (fun α β => by rw [← radicalCoefficient_eq]; exact h α β) 0 0
  rw [radicalDifference_apply] at h0
  have h1 : radicalP21 ![(0 : 𝔸), 0] = 1 := by
    rw [show (![(0 : 𝔸), 0] : Fin 2 → 𝔸) = 0 from by ext i; fin_cases i <;> rfl]
    exact radicalP21_zero
  rw [h1, one_mul] at h0
  exact sub_eq_zero.mp h0
end
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_mirabolicSeries_eq_dual_of_radicalCoefficient_eq.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_mirabolicSeries_eq_dual_of_radicalCoefficient_eq.LanglandsTunnell.CubicInduction"
end LanglandsTunnell.CubicInduction
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_mirabolicSeries_eq_dual_of_radicalCoefficient_eq.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_mirabolicSeries_eq_dual_of_radicalCoefficient_eq.LanglandsTunnell.CubicInduction"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_mirabolicSeries_eq_dual_of_radicalCoefficient_eq.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_mirabolicSeries_eq_dual_of_radicalCoefficient_eq.LanglandsTunnell.CubicInduction"

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "Converse.IsAdmissibleTwist TateLocal.addCharLevel TateLocal.localBorel TateLocal.borelSpace_localBorel TateLocal.integersPositiveCompacts TateLocal.coe_integersPositiveCompacts TateLocal.selfDualHaarAt TateLocal.higherUnitsAt TateLocal.forall_eq_one_and_exists_ne_one_of_addCharLevel"
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "matrixFin_ext matrixAdele_ext localMatN mapMatrix_localMatN_self mapMatrix_localMatN_of_ne finMatN mapMatrix_arch_finMatN mapMatrix_fin_finMatN localToAdelic3 converseCongruenceSet3 HasVanishingUnipotentIntegralAlong IsCongruenceEquivariantAlong lowerUnipotent21 longWeyl3 longWeyl3_coe dualWhittakerFn3 dualWhittakerFn3_apply weylPrime3 weylPrime3_coe weylPrime3_mul_self transposeInv3_weylPrime3 weylPrime3_mul_transposeInv3_radicalP21_mul_weylPrime3 IsGL3PsiWhittakerFn transposeInv3 IsCuspidalAlongP21 psiLoc mirabolicTranslate AdelicGL globalPointsGL centralScalarGL upperUnipotent3 upperUnipotent3_coe upperUnipotent3_zero radicalP21 radicalP21_zero radicalP21_coe radicalP21_add embedMat2 iotaGL coe_iotaGL iota MirabolicIndex mirabolicRep mirabolicRep_spec mirabolic_mk_unipotent_mul localMaximalCompact3 componentAtN archComponentN componentAt3 archComponent3 LocalGL3 cosetSum IsCosetEigenfunction IsRightInvariant diagUnitGL2 diagHom diagHom_apply isCuspidalAlongP21_mirabolicSeries"
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"
noncomputable section
open IsDedekindDomain NumberField MeasureTheory AutomorphicForm
open scoped ProbabilityTheory Pointwise

section BoxOrthogonality

attribute [local instance] NumberField.AdelicHaar.adeleBorel

private theorem setIntegral_adelicBox_comp_add_right {f : AdeleRing (𝓞 ℚ) ℚ → ℂ}
    (hf : ∀ (α : ℚ) (y : AdeleRing (𝓞 ℚ) ℚ), f (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) α + y) = f y)
    (s : AdeleRing (𝓞 ℚ) ℚ) :
    ∫ y in AdelicBox.adelicBox ℚ, f (y + s) ∂(NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ) =
      ∫ y in AdelicBox.adelicBox ℚ, f y ∂(NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ) := by
  haveI := NumberField.AdelicHaar.borelSpace_adeleBorel (𝓞 ℚ) ℚ
  haveI := NumberField.AdelicHaar.isAddHaarMeasure_adelicAddHaar (𝓞 ℚ) ℚ
  set μ : Measure (AdeleRing (𝓞 ℚ) ℚ) := NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ with hμ

  have hf' : ∀ (γ : AdeleRing.principalSubgroup (𝓞 ℚ) ℚ) (y : AdeleRing (𝓞 ℚ) ℚ), f (γ +ᵥ y) = f y := by
    intro γ y
    obtain ⟨α, hα⟩ := RingHom.mem_range.mp γ.2
    show f ((γ : AdeleRing (𝓞 ℚ) ℚ) + y) = f y
    rw [← hα]
    exact hf α y
  have hbox := AdelicBox.isAddFundamentalDomain_adelicBox ℚ μ

  haveI : Countable (AdeleRing.principalSubgroup (𝓞 ℚ) ℚ) := by
    refine Function.Surjective.countable (f := fun α : ℚ =>
      (⟨algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) α, ⟨α, rfl⟩⟩ : AdeleRing.principalSubgroup (𝓞 ℚ) ℚ)) ?_
    rintro ⟨x, hx⟩
    obtain ⟨α, rfl⟩ := RingHom.mem_range.mp hx
    exact ⟨α, rfl⟩

  have hbox' : IsAddFundamentalDomain (AdeleRing.principalSubgroup (𝓞 ℚ) ℚ) (s +ᵥ AdelicBox.adelicBox ℚ) μ :=
    hbox.vadd_of_comm s

  have hpre : (fun y : AdeleRing (𝓞 ℚ) ℚ => y + s) ⁻¹' (s +ᵥ AdelicBox.adelicBox ℚ) = AdelicBox.adelicBox ℚ := by
    ext y
    simp only [Set.mem_preimage, Set.mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add]
    rw [show -s + (y + s) = y by abel]
  have hshift := (measurePreserving_add_right μ s).setIntegral_preimage_emb
    (MeasurableEquiv.addRight s).measurableEmbedding f (s +ᵥ AdelicBox.adelicBox ℚ)
  rw [hpre] at hshift
  rw [hshift]
  exact hbox'.setIntegral_eq hbox hf'

private theorem addChar_mul_algebraMap_add {ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ}
    (hψ : IsPrincipalInvariantAddChar ℚ ψ) (β α : ℚ) (y : AdeleRing (𝓞 ℚ) ℚ) :
    ψ (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) β * (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) α + y)) =
      ψ (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) β * y) := by
  rw [mul_add, AddChar.map_add_eq_mul, ← map_mul (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ)), hψ (β * α), one_mul]

private theorem setIntegral_adelicBox_addChar_mul_eq_zero
    {ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ} (hψ : IsGlobalAddChar ℚ ψ)
    {β : ℚ} (hβ : β ≠ 0) :
    ∫ y in AdelicBox.adelicBox ℚ, ψ (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) β * y)
      ∂(NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ) = 0 := by
  obtain ⟨t, ht⟩ : ∃ t : AdeleRing (𝓞 ℚ) ℚ, ψ t ≠ 1 := by
    by_contra h
    refine hψ.nontrivial (AddChar.ext ψ 1 fun t => ?_)
    rw [AddChar.one_apply]
    by_contra ht
    exact h ⟨t, ht⟩
  set I : ℂ := ∫ y in AdelicBox.adelicBox ℚ, ψ (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) β * y)
    ∂(NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ) with hI
  have hβt : algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) β * (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) β⁻¹ * t) = t := by
    rw [← mul_assoc, ← map_mul, mul_inv_cancel₀ hβ, map_one, one_mul]
  have hshift := setIntegral_adelicBox_comp_add_right
    (f := fun y => ψ (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) β * y))
    (addChar_mul_algebraMap_add hψ.principalInvariant β) (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) β⁻¹ * t)
  have hmul : (∫ y in AdelicBox.adelicBox ℚ,
      ψ (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) β * (y + algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) β⁻¹ * t))
        ∂(NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ)) = ψ t * I := by
    rw [hI, ← integral_const_mul]
    congr 1
    funext y
    rw [mul_add, AddChar.map_add_eq_mul, hβt, mul_comm]
  have h : ψ t * I = I := by
    rw [← hmul]
    exact hshift
  have h' : (ψ t - 1) * I = 0 := by rw [sub_mul, one_mul, h, sub_self]
  exact (mul_eq_zero.mp h').resolve_left (sub_ne_zero.mpr ht)

private theorem integral_cond_adelicBox_addChar_mul_eq_zero
    {ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ} (hψ : IsGlobalAddChar ℚ ψ)
    {β : ℚ} (hβ : β ≠ 0) :
    ∫ y, ψ (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) β * y)
      ∂((NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ)[|AdelicBox.adelicBox ℚ]) = 0 := by
  rw [ProbabilityTheory.cond, integral_smul_measure, setIntegral_adelicBox_addChar_mul_eq_zero hψ hβ, smul_zero]

end BoxOrthogonality
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_mirabolicSeries_eq_dual_of_radicalCoefficient_eq.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_mirabolicSeries_eq_dual_of_radicalCoefficient_eq.LanglandsTunnell.CubicInduction"
end
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_mirabolicSeries_eq_dual_of_radicalCoefficient_eq.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_mirabolicSeries_eq_dual_of_radicalCoefficient_eq.LanglandsTunnell.CubicInduction"
end LanglandsTunnell.CubicInduction
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_mirabolicSeries_eq_dual_of_radicalCoefficient_eq.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_mirabolicSeries_eq_dual_of_radicalCoefficient_eq.LanglandsTunnell.CubicInduction"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_mirabolicSeries_eq_dual_of_radicalCoefficient_eq.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_mirabolicSeries_eq_dual_of_radicalCoefficient_eq.LanglandsTunnell.CubicInduction"

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "Converse.IsAdmissibleTwist TateLocal.addCharLevel TateLocal.localBorel TateLocal.borelSpace_localBorel TateLocal.integersPositiveCompacts TateLocal.coe_integersPositiveCompacts TateLocal.selfDualHaarAt TateLocal.higherUnitsAt TateLocal.forall_eq_one_and_exists_ne_one_of_addCharLevel"
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "matrixFin_ext matrixAdele_ext localMatN mapMatrix_localMatN_self mapMatrix_localMatN_of_ne finMatN mapMatrix_arch_finMatN mapMatrix_fin_finMatN localToAdelic3 converseCongruenceSet3 HasVanishingUnipotentIntegralAlong IsCongruenceEquivariantAlong lowerUnipotent21 longWeyl3 longWeyl3_coe dualWhittakerFn3 dualWhittakerFn3_apply weylPrime3 weylPrime3_coe weylPrime3_mul_self transposeInv3_weylPrime3 weylPrime3_mul_transposeInv3_radicalP21_mul_weylPrime3 IsGL3PsiWhittakerFn transposeInv3 IsCuspidalAlongP21 psiLoc mirabolicTranslate AdelicGL globalPointsGL centralScalarGL upperUnipotent3 upperUnipotent3_coe upperUnipotent3_zero radicalP21 radicalP21_zero radicalP21_coe radicalP21_add embedMat2 iotaGL coe_iotaGL iota MirabolicIndex mirabolicRep mirabolicRep_spec mirabolic_mk_unipotent_mul localMaximalCompact3 componentAtN archComponentN componentAt3 archComponent3 LocalGL3 cosetSum IsCosetEigenfunction IsRightInvariant diagUnitGL2 diagHom diagHom_apply isCuspidalAlongP21_mirabolicSeries"
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"
section
open IsDedekindDomain NumberField NumberField.AdelicHaar AutomorphicForm MeasureTheory
open scoped ProbabilityTheory

section Furniture

variable {ψ : AddChar 𝔸 ℂ}

private theorem integral_cond_comp_add {f : 𝔸 → ℂ}
    (hf : ∀ (q : ℚ) (y : 𝔸), f (algebraMap ℚ 𝔸 q + y) = f y) (s : 𝔸) :
    ∫ y, f (y + s) ∂μbox = ∫ y, f y ∂μbox := by
  simp only [ProbabilityTheory.cond, integral_smul_measure, setIntegral_adelicBox_comp_add_right hf s]

private theorem phase_algebraMap_add (hψ : IsGlobalAddChar ℚ ψ) (β q : ℚ) (y : 𝔸) :
    ψ (-(algebraMap ℚ 𝔸 β * (algebraMap ℚ 𝔸 q + y))) = ψ (-(algebraMap ℚ 𝔸 β * y)) := by
  simpa only [map_neg, neg_mul] using addChar_mul_algebraMap_add hψ.principalInvariant (-β) q y

private theorem phase_add (β : ℚ) (y t : 𝔸) :
    ψ (-(algebraMap ℚ 𝔸 β * (y + t))) = ψ (-(algebraMap ℚ 𝔸 β * y)) * ψ (-(algebraMap ℚ 𝔸 β * t)) := by
  rw [mul_add, neg_add, AddChar.map_add_eq_mul]

private theorem addChar_neg_ne_one {x : 𝔸} (hx : ψ x ≠ 1) : ψ (-x) ≠ 1 := by
  intro h
  apply hx
  have hmul := AddChar.map_add_eq_mul ψ x (-x)
  rw [add_neg_cancel, AddChar.map_zero_eq_one, h, mul_one] at hmul
  exact hmul.symm

private theorem addChar_neg_eq_one {x : 𝔸} (hx : ψ x = 1) : ψ (-x) = 1 := by
  have hmul := AddChar.map_add_eq_mul ψ x (-x)
  rw [add_neg_cancel, AddChar.map_zero_eq_one, hx, one_mul] at hmul
  exact hmul.symm

private theorem integral_eq_zero_of_comp_add_eq_mul {f : 𝔸 → ℂ}
    (hf : ∀ (q : ℚ) (y : 𝔸), f (algebraMap ℚ 𝔸 q + y) = f y) {t : 𝔸} {k : ℂ}
    (hshift : ∀ y : 𝔸, f (y + t) = f y * k) (hk : k ≠ 1) : ∫ y, f y ∂μbox = 0 := by
  have h1 : ∫ y, f y ∂μbox = (∫ y, f y ∂μbox) * k := by
    conv_lhs => rw [← integral_cond_comp_add hf t]
    simp_rw [hshift]
    exact integral_mul_const k f
  have h2 : (∫ y, f y ∂μbox) * (1 - k) = 0 := by rw [mul_sub, mul_one, ← h1, sub_self]
  exact (mul_eq_zero.mp h2).resolve_right (sub_ne_zero.mpr hk.symm)

end Furniture
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_mirabolicSeries_eq_dual_of_radicalCoefficient_eq.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_mirabolicSeries_eq_dual_of_radicalCoefficient_eq.LanglandsTunnell.CubicInduction"

private theorem boxCoefficient_eq_zero_of_snd_invariant {ψ : AddChar 𝔸 ℂ} (hψ : IsGlobalAddChar ℚ ψ) (F : 𝔸 → 𝔸 → ℂ)
    (hper₂ : ∀ (q : ℚ) (z y : 𝔸), F z (algebraMap ℚ 𝔸 q + y) = F z y)
    (t : 𝔸) (hinv : ∀ z y : 𝔸, F z (y + t) = F z y) (α β : ℚ) (hβt : ψ (algebraMap ℚ 𝔸 β * t) ≠ 1) :
    boxCoefficient ψ F α β = 0 := by
  have hinner : ∀ z : 𝔸, (∫ y, F z y * ψ (-(algebraMap ℚ 𝔸 β * y)) ∂μbox) = 0 := fun z =>
    integral_eq_zero_of_comp_add_eq_mul (f := fun y => F z y * ψ (-(algebraMap ℚ 𝔸 β * y)))
      (fun q y => by simp only [hper₂, phase_algebraMap_add hψ]) (t := t) (k := ψ (-(algebraMap ℚ 𝔸 β * t)))
      (fun y => by simp only [hinv, phase_add, mul_assoc]) (addChar_neg_ne_one hβt)
  simp only [boxCoefficient, hinner, zero_mul, integral_zero]

private theorem boxCoefficient_eq_zero_of_fst_invariant {ψ : AddChar 𝔸 ℂ} (hψ : IsGlobalAddChar ℚ ψ) (F : 𝔸 → 𝔸 → ℂ)
    (hper₁ : ∀ (q : ℚ) (z y : 𝔸), F (algebraMap ℚ 𝔸 q + z) y = F z y)
    (t : 𝔸) (hinv : ∀ z y : 𝔸, F (z + t) y = F z y) (α β : ℚ) (hαt : ψ (algebraMap ℚ 𝔸 α * t) ≠ 1) :
    boxCoefficient ψ F α β = 0 := by
  have hGper : ∀ (q : ℚ) (z : 𝔸), (∫ y, F (algebraMap ℚ 𝔸 q + z) y * ψ (-(algebraMap ℚ 𝔸 β * y)) ∂μbox) =
      ∫ y, F z y * ψ (-(algebraMap ℚ 𝔸 β * y)) ∂μbox := fun q z => by simp only [hper₁]
  have hGinv : ∀ z : 𝔸, (∫ y, F (z + t) y * ψ (-(algebraMap ℚ 𝔸 β * y)) ∂μbox) =
      ∫ y, F z y * ψ (-(algebraMap ℚ 𝔸 β * y)) ∂μbox := fun z => by simp only [hinv]
  exact integral_eq_zero_of_comp_add_eq_mul
    (f := fun z => (∫ y, F z y * ψ (-(algebraMap ℚ 𝔸 β * y)) ∂μbox) * ψ (-(algebraMap ℚ 𝔸 α * z)))
    (fun q z => by simp only [hGper, phase_algebraMap_add hψ]) (t := t) (k := ψ (-(algebraMap ℚ 𝔸 α * t)))
    (fun z => by simp only [hGinv, phase_add, mul_assoc]) (addChar_neg_ne_one hαt)

private theorem boxCoefficient_eq_zero_of_sum_translates_eq_zero {ψ : AddChar 𝔸 ℂ} (hψ : IsGlobalAddChar ℚ ψ)
    (F : 𝔸 → 𝔸 → ℂ) (hF : Continuous fun p : 𝔸 × 𝔸 => F p.1 p.2)
    (hper₂ : ∀ (q : ℚ) (z y : 𝔸), F z (algebraMap ℚ 𝔸 q + y) = F z y)
    {ι : Type*} (R : Finset ι) (hR : R.Nonempty) (τ : ι → 𝔸) (α β : ℚ)
    (hχ : ∀ t ∈ R, ψ (algebraMap ℚ 𝔸 β * τ t) = 1)
    (havg : ∀ z y : 𝔸, ∑ t ∈ R, F z (y + τ t) = 0) :
    boxCoefficient ψ F α β = 0 := by
  have hinner : ∀ z : 𝔸, (∫ y, F z y * ψ (-(algebraMap ℚ 𝔸 β * y)) ∂μbox) = 0 := by
    intro z
    have heach : ∀ s ∈ R, (∫ y, F z (y + τ s) * ψ (-(algebraMap ℚ 𝔸 β * y)) ∂μbox) =
        ∫ y, F z y * ψ (-(algebraMap ℚ 𝔸 β * y)) ∂μbox := by
      intro s hs
      have hphase : ∀ y : 𝔸, ψ (-(algebraMap ℚ 𝔸 β * (y + τ s))) = ψ (-(algebraMap ℚ 𝔸 β * y)) := fun y => by
        rw [phase_add, addChar_neg_eq_one (hχ s hs), mul_one]
      calc (∫ y, F z (y + τ s) * ψ (-(algebraMap ℚ 𝔸 β * y)) ∂μbox)
          = ∫ y, F z (y + τ s) * ψ (-(algebraMap ℚ 𝔸 β * (y + τ s))) ∂μbox := by simp only [hphase]
        _ = ∫ y, F z y * ψ (-(algebraMap ℚ 𝔸 β * y)) ∂μbox :=
          integral_cond_comp_add (f := fun y => F z y * ψ (-(algebraMap ℚ 𝔸 β * y)))
            (fun q y => by simp only [hper₂, phase_algebraMap_add hψ]) (τ s)
    have hsum := integral_finset_sum (μ := μbox) R
      (f := fun s y => F z (y + τ s) * ψ (-(algebraMap ℚ 𝔸 β * y))) fun s _ =>
        integrable_slice_mul_addChar hψ (F := fun z y => F z (y + τ s))
          (hF.comp (by fun_prop : Continuous fun p : 𝔸 × 𝔸 => (p.1, p.2 + τ s))) β z
    simp only [← Finset.sum_mul, havg, zero_mul, integral_zero] at hsum
    rw [Finset.sum_congr rfl heach, Finset.sum_const, nsmul_eq_mul] at hsum
    exact (mul_eq_zero.mp hsum.symm).resolve_left (Nat.cast_ne_zero.mpr (Finset.card_pos.mpr hR).ne')
  simp only [boxCoefficient, hinner, zero_mul, integral_zero]
end
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_mirabolicSeries_eq_dual_of_radicalCoefficient_eq.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_mirabolicSeries_eq_dual_of_radicalCoefficient_eq.LanglandsTunnell.CubicInduction"
end LanglandsTunnell.CubicInduction
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_mirabolicSeries_eq_dual_of_radicalCoefficient_eq.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_mirabolicSeries_eq_dual_of_radicalCoefficient_eq.LanglandsTunnell.CubicInduction"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_mirabolicSeries_eq_dual_of_radicalCoefficient_eq.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_mirabolicSeries_eq_dual_of_radicalCoefficient_eq.LanglandsTunnell.CubicInduction"

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "Converse.IsAdmissibleTwist TateLocal.addCharLevel TateLocal.localBorel TateLocal.borelSpace_localBorel TateLocal.integersPositiveCompacts TateLocal.coe_integersPositiveCompacts TateLocal.selfDualHaarAt TateLocal.higherUnitsAt TateLocal.forall_eq_one_and_exists_ne_one_of_addCharLevel"
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "matrixFin_ext matrixAdele_ext localMatN mapMatrix_localMatN_self mapMatrix_localMatN_of_ne finMatN mapMatrix_arch_finMatN mapMatrix_fin_finMatN localToAdelic3 converseCongruenceSet3 HasVanishingUnipotentIntegralAlong IsCongruenceEquivariantAlong lowerUnipotent21 longWeyl3 longWeyl3_coe dualWhittakerFn3 dualWhittakerFn3_apply weylPrime3 weylPrime3_coe weylPrime3_mul_self transposeInv3_weylPrime3 weylPrime3_mul_transposeInv3_radicalP21_mul_weylPrime3 IsGL3PsiWhittakerFn transposeInv3 IsCuspidalAlongP21 psiLoc mirabolicTranslate AdelicGL globalPointsGL centralScalarGL upperUnipotent3 upperUnipotent3_coe upperUnipotent3_zero radicalP21 radicalP21_zero radicalP21_coe radicalP21_add embedMat2 iotaGL coe_iotaGL iota MirabolicIndex mirabolicRep mirabolicRep_spec mirabolic_mk_unipotent_mul localMaximalCompact3 componentAtN archComponentN componentAt3 archComponent3 LocalGL3 cosetSum IsCosetEigenfunction IsRightInvariant diagUnitGL2 diagHom diagHom_apply isCuspidalAlongP21_mirabolicSeries"
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"
section
private theorem psiLoc_ne_one_of_isGlobalAddChar
    (ψ : AddChar (NumberField.AdeleRing (NumberField.RingOfIntegers ℚ) ℚ) ℂ)
    (hψ : AutomorphicForm.IsGlobalAddChar ℚ ψ)
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ)) :
    psiLoc ψ v ≠ 1 := by
  intro hv
  apply hψ.nontrivial
  have hone : ∀ qy : ℚ × v.adicCompletion ℚ,
      ψ (algebraMap ℚ (NumberField.AdeleRing (NumberField.RingOfIntegers ℚ) ℚ) qy.1 +
        NumberField.StandardAddChar.adeleSingleAt ℚ v qy.2) = 1 := by
    intro qy
    have h2 : ψ (NumberField.StandardAddChar.adeleSingleAt ℚ v qy.2) = 1 := by
      have h3 := DFunLike.congr_fun hv qy.2
      simpa [psiLoc] using h3
    rw [AddChar.map_add_eq_mul, hψ.principalInvariant qy.1, h2, one_mul]
  have hclosed : IsClosed {x : NumberField.AdeleRing (NumberField.RingOfIntegers ℚ) ℚ | ψ x = 1} :=
    isClosed_eq hψ.continuous continuous_const
  have hall : ∀ x : NumberField.AdeleRing (NumberField.RingOfIntegers ℚ) ℚ, ψ x = 1 := fun x =>
    (RatAdele.denseRange_algebraMap_add_adeleSingleAt v).induction_on x hclosed hone
  exact AddChar.eq_one_iff.mpr hall
end
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_mirabolicSeries_eq_dual_of_radicalCoefficient_eq.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_mirabolicSeries_eq_dual_of_radicalCoefficient_eq.LanglandsTunnell.CubicInduction"
end LanglandsTunnell.CubicInduction
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_mirabolicSeries_eq_dual_of_radicalCoefficient_eq.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_mirabolicSeries_eq_dual_of_radicalCoefficient_eq.LanglandsTunnell.CubicInduction"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_mirabolicSeries_eq_dual_of_radicalCoefficient_eq.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_mirabolicSeries_eq_dual_of_radicalCoefficient_eq.LanglandsTunnell.CubicInduction"

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "Converse.IsAdmissibleTwist TateLocal.addCharLevel TateLocal.localBorel TateLocal.borelSpace_localBorel TateLocal.integersPositiveCompacts TateLocal.coe_integersPositiveCompacts TateLocal.selfDualHaarAt TateLocal.higherUnitsAt TateLocal.forall_eq_one_and_exists_ne_one_of_addCharLevel"
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "matrixFin_ext matrixAdele_ext localMatN mapMatrix_localMatN_self mapMatrix_localMatN_of_ne finMatN mapMatrix_arch_finMatN mapMatrix_fin_finMatN localToAdelic3 converseCongruenceSet3 HasVanishingUnipotentIntegralAlong IsCongruenceEquivariantAlong lowerUnipotent21 longWeyl3 longWeyl3_coe dualWhittakerFn3 dualWhittakerFn3_apply weylPrime3 weylPrime3_coe weylPrime3_mul_self transposeInv3_weylPrime3 weylPrime3_mul_transposeInv3_radicalP21_mul_weylPrime3 IsGL3PsiWhittakerFn transposeInv3 IsCuspidalAlongP21 psiLoc mirabolicTranslate AdelicGL globalPointsGL centralScalarGL upperUnipotent3 upperUnipotent3_coe upperUnipotent3_zero radicalP21 radicalP21_zero radicalP21_coe radicalP21_add embedMat2 iotaGL coe_iotaGL iota MirabolicIndex mirabolicRep mirabolicRep_spec mirabolic_mk_unipotent_mul localMaximalCompact3 componentAtN archComponentN componentAt3 archComponent3 LocalGL3 cosetSum IsCosetEigenfunction IsRightInvariant diagUnitGL2 diagHom diagHom_apply isCuspidalAlongP21_mirabolicSeries"
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"
section
private theorem eq_one_of_forall_norm_pow_sub_one_lt {z : ℂ} (h : ∀ n : ℕ, ‖z ^ n - 1‖ < 1 / 2) : z = 1 := by
  by_contra hz
  have hw : 0 < ‖z - 1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hz)
  have hre : ∀ n : ℕ, (1 : ℝ) / 2 ≤ (z ^ n).re := by
    intro n
    have h1 := (Complex.abs_re_le_norm (z ^ n - 1)).trans_lt (h n)
    rw [Complex.sub_re, Complex.one_re] at h1
    linarith [(abs_lt.mp h1).1]
  obtain ⟨N, hN⟩ := Archimedean.arch (1 : ℝ) hw
  rw [nsmul_eq_mul] at hN
  have hsum : (N : ℝ) * (1 / 2) ≤ ‖∑ i ∈ Finset.range N, z ^ i‖ := by
    refine le_trans ?_ (Complex.re_le_norm _)
    rw [Complex.re_sum]
    have h2 := Finset.sum_le_sum fun i (_ : i ∈ Finset.range N) => hre i
    rwa [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at h2
  have hprod : ‖∑ i ∈ Finset.range N, z ^ i‖ * ‖z - 1‖ = ‖z ^ N - 1‖ := by
    rw [← norm_mul, geom_sum_mul]
  have h3 := mul_le_mul_of_nonneg_right hsum hw.le
  rw [hprod] at h3
  linarith [h N]

private theorem exists_forall_eq_one_of_valued_le_exp_of_continuous
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ))
    (χ : AddChar (v.adicCompletion ℚ) ℂ) (hχ : Continuous χ) :
    ∃ k : ℤ, ∀ x : v.adicCompletion ℚ, Valued.v x ≤ WithZero.exp k → χ x = 1 := by
  have hU : (χ : v.adicCompletion ℚ → ℂ) ⁻¹' Metric.ball (1 : ℂ) (1 / 2) ∈ nhds (0 : v.adicCompletion ℚ) := by
    have h1 : Metric.ball (1 : ℂ) (1 / 2) ∈ nhds (χ 0) := by
      rw [AddChar.map_zero_eq_one]
      exact Metric.ball_mem_nhds 1 (by norm_num)
    exact hχ.continuousAt.preimage_mem_nhds h1
  obtain ⟨γ, hγ⟩ := Valued.mem_nhds_zero.1 hU
  have hc0 : MonoidWithZeroHom.ValueGroup₀.embedding γ.1 ≠ 0 :=
    (γ.isUnit.map MonoidWithZeroHom.ValueGroup₀.embedding).ne_zero
  refine ⟨WithZero.log (MonoidWithZeroHom.ValueGroup₀.embedding γ.1) - 1, fun x hx => ?_⟩
  have hball : ∀ y : v.adicCompletion ℚ,
      Valued.v y ≤ WithZero.exp (WithZero.log (MonoidWithZeroHom.ValueGroup₀.embedding γ.1) - 1) →
        ‖χ y - 1‖ < 1 / 2 := by
    intro y hy
    have hlt : Valued.v y < MonoidWithZeroHom.ValueGroup₀.embedding γ.1 := by
      refine hy.trans_lt ?_
      conv_rhs => rw [← WithZero.exp_log hc0]
      exact WithZero.exp_lt_exp.2 (sub_one_lt _)
    have hmem : y ∈ (χ : v.adicCompletion ℚ → ℂ) ⁻¹' Metric.ball (1 : ℂ) (1 / 2) :=
      hγ ((Valuation.restrict_lt_iff_lt_embedding Valued.v).2 hlt)
    simpa [Metric.mem_ball, dist_eq_norm] using hmem
  have hmul : ∀ n : ℕ,
      Valued.v (n • x) ≤ WithZero.exp (WithZero.log (MonoidWithZeroHom.ValueGroup₀.embedding γ.1) - 1) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [succ_nsmul]
      exact (Valued.v.map_add _ _).trans (max_le ih hx)
  apply eq_one_of_forall_norm_pow_sub_one_lt
  intro n
  rw [← AddChar.map_nsmul_eq_pow]
  exact hball _ (hmul n)

private theorem exists_forall_psiLoc_eq_one_of_valued_le_exp
    (ψ : AddChar (NumberField.AdeleRing (NumberField.RingOfIntegers ℚ) ℚ) ℂ)
    (hψ : AutomorphicForm.IsGlobalAddChar ℚ ψ)
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ)) :
    ∃ k : ℤ, ∀ x : v.adicCompletion ℚ, Valued.v x ≤ WithZero.exp k → psiLoc ψ v x = 1 := by
  refine exists_forall_eq_one_of_valued_le_exp_of_continuous v (psiLoc ψ v) ?_
  rw [psiLoc, AddChar.coe_compAddMonoidHom]
  exact hψ.continuous.comp (NumberField.StandardAddChar.continuous_adeleSingleAt ℚ v)
end
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_mirabolicSeries_eq_dual_of_radicalCoefficient_eq.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_mirabolicSeries_eq_dual_of_radicalCoefficient_eq.LanglandsTunnell.CubicInduction"
end LanglandsTunnell.CubicInduction
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_mirabolicSeries_eq_dual_of_radicalCoefficient_eq.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_mirabolicSeries_eq_dual_of_radicalCoefficient_eq.LanglandsTunnell.CubicInduction"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_mirabolicSeries_eq_dual_of_radicalCoefficient_eq.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_mirabolicSeries_eq_dual_of_radicalCoefficient_eq.LanglandsTunnell.CubicInduction"

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "Converse.IsAdmissibleTwist TateLocal.addCharLevel TateLocal.localBorel TateLocal.borelSpace_localBorel TateLocal.integersPositiveCompacts TateLocal.coe_integersPositiveCompacts TateLocal.selfDualHaarAt TateLocal.higherUnitsAt TateLocal.forall_eq_one_and_exists_ne_one_of_addCharLevel"
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "matrixFin_ext matrixAdele_ext localMatN mapMatrix_localMatN_self mapMatrix_localMatN_of_ne finMatN mapMatrix_arch_finMatN mapMatrix_fin_finMatN localToAdelic3 converseCongruenceSet3 HasVanishingUnipotentIntegralAlong IsCongruenceEquivariantAlong lowerUnipotent21 longWeyl3 longWeyl3_coe dualWhittakerFn3 dualWhittakerFn3_apply weylPrime3 weylPrime3_coe weylPrime3_mul_self transposeInv3_weylPrime3 weylPrime3_mul_transposeInv3_radicalP21_mul_weylPrime3 IsGL3PsiWhittakerFn transposeInv3 IsCuspidalAlongP21 psiLoc mirabolicTranslate AdelicGL globalPointsGL centralScalarGL upperUnipotent3 upperUnipotent3_coe upperUnipotent3_zero radicalP21 radicalP21_zero radicalP21_coe radicalP21_add embedMat2 iotaGL coe_iotaGL iota MirabolicIndex mirabolicRep mirabolicRep_spec mirabolic_mk_unipotent_mul localMaximalCompact3 componentAtN archComponentN componentAt3 archComponent3 LocalGL3 cosetSum IsCosetEigenfunction IsRightInvariant diagUnitGL2 diagHom diagHom_apply isCuspidalAlongP21_mirabolicSeries"
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"
section
open IsDedekindDomain NumberField AutomorphicForm

variable (ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ) (v : HeightOneSpectrum (𝓞 ℚ))

private theorem psiLoc_apply_eq_one_of_addCharLevel_eq_zero
    (hψ : IsGlobalAddChar ℚ ψ) (h0 : LanglandsTunnell.TateLocal.addCharLevel (psiLoc ψ v) = 0) :
    ∀ x : v.adicCompletion ℚ, Valued.v x ≤ 1 → psiLoc ψ v x = 1 := by
  intro x hx
  have h := (LanglandsTunnell.TateLocal.forall_eq_one_and_exists_ne_one_of_addCharLevel ℚ v (psiLoc ψ v)
    (exists_forall_psiLoc_eq_one_of_valued_le_exp ψ hψ v) (psiLoc_ne_one_of_isGlobalAddChar ψ hψ v)).1
  rw [h0] at h
  exact h x (by rw [WithZero.exp_zero]; exact hx)

private theorem exists_psiLoc_ne_one_of_addCharLevel_eq_zero
    (hψ : IsGlobalAddChar ℚ ψ) (h0 : LanglandsTunnell.TateLocal.addCharLevel (psiLoc ψ v) = 0) :
    ∃ x : v.adicCompletion ℚ, Valued.v x ≤ WithZero.exp (1 : ℤ) ∧ psiLoc ψ v x ≠ 1 := by
  have h := (LanglandsTunnell.TateLocal.forall_eq_one_and_exists_ne_one_of_addCharLevel ℚ v (psiLoc ψ v)
    (exists_forall_psiLoc_eq_one_of_valued_le_exp ψ hψ v) (psiLoc_ne_one_of_isGlobalAddChar ψ hψ v)).2
  rw [h0, zero_add] at h
  exact h
end
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_mirabolicSeries_eq_dual_of_radicalCoefficient_eq.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_mirabolicSeries_eq_dual_of_radicalCoefficient_eq.LanglandsTunnell.CubicInduction"
end LanglandsTunnell.CubicInduction
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_mirabolicSeries_eq_dual_of_radicalCoefficient_eq.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_mirabolicSeries_eq_dual_of_radicalCoefficient_eq.LanglandsTunnell.CubicInduction"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_mirabolicSeries_eq_dual_of_radicalCoefficient_eq.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_mirabolicSeries_eq_dual_of_radicalCoefficient_eq.LanglandsTunnell.CubicInduction"

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "Converse.IsAdmissibleTwist TateLocal.addCharLevel TateLocal.localBorel TateLocal.borelSpace_localBorel TateLocal.integersPositiveCompacts TateLocal.coe_integersPositiveCompacts TateLocal.selfDualHaarAt TateLocal.higherUnitsAt TateLocal.forall_eq_one_and_exists_ne_one_of_addCharLevel"
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "matrixFin_ext matrixAdele_ext localMatN mapMatrix_localMatN_self mapMatrix_localMatN_of_ne finMatN mapMatrix_arch_finMatN mapMatrix_fin_finMatN localToAdelic3 converseCongruenceSet3 HasVanishingUnipotentIntegralAlong IsCongruenceEquivariantAlong lowerUnipotent21 longWeyl3 longWeyl3_coe dualWhittakerFn3 dualWhittakerFn3_apply weylPrime3 weylPrime3_coe weylPrime3_mul_self transposeInv3_weylPrime3 weylPrime3_mul_transposeInv3_radicalP21_mul_weylPrime3 IsGL3PsiWhittakerFn transposeInv3 IsCuspidalAlongP21 psiLoc mirabolicTranslate AdelicGL globalPointsGL centralScalarGL upperUnipotent3 upperUnipotent3_coe upperUnipotent3_zero radicalP21 radicalP21_zero radicalP21_coe radicalP21_add embedMat2 iotaGL coe_iotaGL iota MirabolicIndex mirabolicRep mirabolicRep_spec mirabolic_mk_unipotent_mul localMaximalCompact3 componentAtN archComponentN componentAt3 archComponent3 LocalGL3 cosetSum IsCosetEigenfunction IsRightInvariant diagUnitGL2 diagHom diagHom_apply isCuspidalAlongP21_mirabolicSeries"
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"
section
open IsDedekindDomain NumberField

private theorem valued_mul_apply_le {v : HeightOneSpectrum (𝓞 ℚ)} {C : WithZero (Multiplicative ℤ)}
    {A B : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)} {i j : Fin 3}
    (h0 : Valued.v (A i 0) * Valued.v (B 0 j) ≤ C) (h1 : Valued.v (A i 1) * Valued.v (B 1 j) ≤ C)
    (h2 : Valued.v (A i 2) * Valued.v (B 2 j) ≤ C) :
    Valued.v ((A * B) i j) ≤ C := by
  rw [Matrix.mul_apply, Fin.sum_univ_three]
  refine le_trans (Valuation.map_add _ _ _) (max_le ?_ (by rw [map_mul]; exact h2))
  exact le_trans (Valuation.map_add _ _ _) (max_le (by rw [map_mul]; exact h0) (by rw [map_mul]; exact h1))

private theorem valued_mul_le_of_le_one_left {v : HeightOneSpectrum (𝓞 ℚ)} {C : WithZero (Multiplicative ℤ)}
    {x y : v.adicCompletion ℚ} (hx : Valued.v x ≤ 1) (hy : Valued.v y ≤ C) : Valued.v x * Valued.v y ≤ C :=
  (mul_le_mul' hx hy).trans (one_mul C).le

private theorem valued_mul_le_of_le_one_right {v : HeightOneSpectrum (𝓞 ℚ)} {C : WithZero (Multiplicative ℤ)}
    {x y : v.adicCompletion ℚ} (hx : Valued.v x ≤ C) (hy : Valued.v y ≤ 1) : Valued.v x * Valued.v y ≤ C :=
  (mul_le_mul' hx hy).trans (mul_one C).le

private theorem mul_mem_converseCongruenceSet3 {v : HeightOneSpectrum (𝓞 ℚ)} {n : ℕ} {k k' : LocalGL3 v}
    (hk : k ∈ converseCongruenceSet3 v n) (hk' : k' ∈ converseCongruenceSet3 v n) :
    k * k' ∈ converseCongruenceSet3 v n := by
  obtain ⟨hkK, hk01, hk20, hk21⟩ := hk
  obtain ⟨hk'K, hk'01, hk'20, hk'21⟩ := hk'
  have h2n : WithZero.exp (-(2 * (n : ℤ))) ≤ WithZero.exp (-(n : ℤ)) := WithZero.exp_le_exp.mpr (by omega)
  have hnn : WithZero.exp (-(n : ℤ)) * WithZero.exp (-(n : ℤ)) = WithZero.exp (-(2 * (n : ℤ))) := by
    rw [← WithZero.exp_add]
    congr 1
    ring
  refine ⟨(localMaximalCompact3 (𝓞 ℚ) ℚ v).mul_mem hkK hk'K, ?_, ?_, ?_⟩
  · rw [Units.val_mul]
    exact valued_mul_apply_le (valued_mul_le_of_le_one_left (hkK.1 0 0) hk'01)
      (valued_mul_le_of_le_one_right hk01 (hk'K.1 1 1))
      (valued_mul_le_of_le_one_left (hkK.1 0 2) (hk'21.trans h2n))
  · rw [Units.val_mul]
    exact valued_mul_apply_le (valued_mul_le_of_le_one_right hk20 (hk'K.1 0 0))
      (valued_mul_le_of_le_one_right (hk21.trans h2n) (hk'K.1 1 0))
      (valued_mul_le_of_le_one_left (hkK.1 2 2) hk'20)
  · rw [Units.val_mul]
    exact valued_mul_apply_le ((mul_le_mul' hk20 hk'01).trans hnn.le)
      (valued_mul_le_of_le_one_right hk21 (hk'K.1 1 1))
      (valued_mul_le_of_le_one_left (hkK.1 2 2) hk'21)

private theorem valued_det_le_one_of_forall_le
    {v : HeightOneSpectrum (𝓞 ℚ)} {A : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)}
    (hA : ∀ i j, Valued.v (A i j) ≤ 1) : Valued.v A.det ≤ 1 := by
  have hm : ∀ i j l : Fin 3, ∀ i' j' l' : Fin 3, Valued.v (A i j * A i' j' * A l l') ≤ 1 := fun i j l i' j' l' => by
    rw [map_mul, map_mul]
    exact mul_le_one' (mul_le_one' (hA i j) (hA i' j')) (hA l l')
  rw [Matrix.det_fin_three]
  refine le_trans (Valuation.map_sub _ _ _) (max_le ?_ (hm _ _ _ _ _ _))
  refine le_trans (Valuation.map_add _ _ _) (max_le ?_ (hm _ _ _ _ _ _))
  refine le_trans (Valuation.map_add _ _ _) (max_le ?_ (hm _ _ _ _ _ _))
  refine le_trans (Valuation.map_sub _ _ _) (max_le ?_ (hm _ _ _ _ _ _))
  exact le_trans (Valuation.map_sub _ _ _) (max_le (hm _ _ _ _ _ _) (hm _ _ _ _ _ _))

private theorem valued_det_eq_one_of_mem_localMaximalCompact3_aux15 {v : HeightOneSpectrum (𝓞 ℚ)} {k : LocalGL3 v}
    (hk : k ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v) :
    Valued.v ((k : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)).det) = 1 := by
  have h1 : Valued.v ((k : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)).det) ≤ 1 :=
    valued_det_le_one_of_forall_le hk.1
  have h2 : Valued.v (((k⁻¹ : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)).det) ≤ 1 :=
    valued_det_le_one_of_forall_le hk.2
  have hmul : Valued.v ((k : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)).det) *
      Valued.v (((k⁻¹ : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)).det) = 1 := by
    rw [← map_mul, ← Matrix.det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.det_one, map_one]
  refine le_antisymm h1 ?_
  calc (1 : WithZero (Multiplicative ℤ)) = _ := hmul.symm
    _ ≤ Valued.v ((k : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)).det) * 1 := mul_le_mul_right h2 _
    _ = _ := mul_one _

private theorem valued_inv_apply_eq_valued_adjugate {v : HeightOneSpectrum (𝓞 ℚ)} {k : LocalGL3 v}
    (hk : k ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v) (i j : Fin 3) :
    Valued.v (((k⁻¹ : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j) =
      Valued.v ((k : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)).adjugate i j) := by
  rw [Matrix.GeneralLinearGroup.coe_inv, Matrix.inv_def, Matrix.smul_apply, smul_eq_mul, map_mul,
    Ring.inverse_eq_inv, map_inv₀, valued_det_eq_one_of_mem_localMaximalCompact3_aux15 hk, inv_one, one_mul]

private theorem adjugate_apply_zero_one {v : HeightOneSpectrum (𝓞 ℚ)}
    (A : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) :
    A.adjugate 0 1 = -(A 0 1 * A 2 2) + A 0 2 * A 2 1 := by
  simp [Matrix.adjugate_fin_three]

private theorem adjugate_apply_two_zero {v : HeightOneSpectrum (𝓞 ℚ)}
    (A : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) :
    A.adjugate 2 0 = A 1 0 * A 2 1 - A 1 1 * A 2 0 := by
  simp [Matrix.adjugate_fin_three]

private theorem adjugate_apply_two_one {v : HeightOneSpectrum (𝓞 ℚ)}
    (A : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) :
    A.adjugate 2 1 = -(A 0 0 * A 2 1) + A 0 1 * A 2 0 := by
  simp [Matrix.adjugate_fin_three]

private theorem inv_mem_converseCongruenceSet3 {v : HeightOneSpectrum (𝓞 ℚ)} {n : ℕ} {k : LocalGL3 v}
    (hk : k ∈ converseCongruenceSet3 v n) : k⁻¹ ∈ converseCongruenceSet3 v n := by
  obtain ⟨hkK, hk01, hk20, hk21⟩ := hk
  have h2n : WithZero.exp (-(2 * (n : ℤ))) ≤ WithZero.exp (-(n : ℤ)) := WithZero.exp_le_exp.mpr (by omega)
  have hnn : WithZero.exp (-(n : ℤ)) * WithZero.exp (-(n : ℤ)) = WithZero.exp (-(2 * (n : ℤ))) := by
    rw [← WithZero.exp_add]
    congr 1
    ring
  refine ⟨(localMaximalCompact3 (𝓞 ℚ) ℚ v).inv_mem hkK, ?_, ?_, ?_⟩
  · rw [valued_inv_apply_eq_valued_adjugate hkK, adjugate_apply_zero_one]
    refine le_trans (Valuation.map_add _ _ _) (max_le ?_ ?_)
    · rw [Valuation.map_neg, map_mul]
      exact valued_mul_le_of_le_one_right hk01 (hkK.1 2 2)
    · rw [map_mul]
      exact valued_mul_le_of_le_one_left (hkK.1 0 2) (hk21.trans h2n)
  · rw [valued_inv_apply_eq_valued_adjugate hkK, adjugate_apply_two_zero]
    refine le_trans (Valuation.map_sub _ _ _) (max_le ?_ ?_)
    · rw [map_mul]
      exact valued_mul_le_of_le_one_left (hkK.1 1 0) (hk21.trans h2n)
    · rw [map_mul]
      exact valued_mul_le_of_le_one_left (hkK.1 1 1) hk20
  · rw [valued_inv_apply_eq_valued_adjugate hkK, adjugate_apply_two_one]
    refine le_trans (Valuation.map_add _ _ _) (max_le ?_ ?_)
    · rw [Valuation.map_neg, map_mul]
      exact valued_mul_le_of_le_one_left (hkK.1 0 0) hk21
    · rw [map_mul]
      exact (mul_le_mul' hk01 hk20).trans hnn.le
end
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_mirabolicSeries_eq_dual_of_radicalCoefficient_eq.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_mirabolicSeries_eq_dual_of_radicalCoefficient_eq.LanglandsTunnell.CubicInduction"
end LanglandsTunnell.CubicInduction
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_mirabolicSeries_eq_dual_of_radicalCoefficient_eq.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_mirabolicSeries_eq_dual_of_radicalCoefficient_eq.LanglandsTunnell.CubicInduction"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_mirabolicSeries_eq_dual_of_radicalCoefficient_eq.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_mirabolicSeries_eq_dual_of_radicalCoefficient_eq.LanglandsTunnell.CubicInduction"

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "Converse.IsAdmissibleTwist TateLocal.addCharLevel TateLocal.localBorel TateLocal.borelSpace_localBorel TateLocal.integersPositiveCompacts TateLocal.coe_integersPositiveCompacts TateLocal.selfDualHaarAt TateLocal.higherUnitsAt TateLocal.forall_eq_one_and_exists_ne_one_of_addCharLevel"
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "matrixFin_ext matrixAdele_ext localMatN mapMatrix_localMatN_self mapMatrix_localMatN_of_ne finMatN mapMatrix_arch_finMatN mapMatrix_fin_finMatN localToAdelic3 converseCongruenceSet3 HasVanishingUnipotentIntegralAlong IsCongruenceEquivariantAlong lowerUnipotent21 longWeyl3 longWeyl3_coe dualWhittakerFn3 dualWhittakerFn3_apply weylPrime3 weylPrime3_coe weylPrime3_mul_self transposeInv3_weylPrime3 weylPrime3_mul_transposeInv3_radicalP21_mul_weylPrime3 IsGL3PsiWhittakerFn transposeInv3 IsCuspidalAlongP21 psiLoc mirabolicTranslate AdelicGL globalPointsGL centralScalarGL upperUnipotent3 upperUnipotent3_coe upperUnipotent3_zero radicalP21 radicalP21_zero radicalP21_coe radicalP21_add embedMat2 iotaGL coe_iotaGL iota MirabolicIndex mirabolicRep mirabolicRep_spec mirabolic_mk_unipotent_mul localMaximalCompact3 componentAtN archComponentN componentAt3 archComponent3 LocalGL3 cosetSum IsCosetEigenfunction IsRightInvariant diagUnitGL2 diagHom diagHom_apply isCuspidalAlongP21_mirabolicSeries"
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"
section
open Matrix IsDedekindDomain NumberField NumberField.StandardAddChar MeasureTheory AutomorphicForm

private theorem componentAt3_localToAdelic3_of_ne {v w : HeightOneSpectrum (𝓞 ℚ)} (hwv : w ≠ v) (k : LocalGL3 v) :
    componentAt3 (𝓞 ℚ) ℚ w (localToAdelic3 v k) = 1 := by
  apply Units.ext
  rw [Units.val_one]
  change ((AdelicLevel.finAdeleEval (𝓞 ℚ) ℚ w).comp (AdelicLevel.adeleFin (𝓞 ℚ) ℚ)).mapMatrix
    (finMatN (Fin 3) (𝓞 ℚ) ℚ (localMatN (Fin 3) (𝓞 ℚ) ℚ v (k : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)))) = 1
  rw [RingHom.mapMatrix_apply, RingHom.coe_comp, ← Matrix.map_map, ← RingHom.mapMatrix_apply,
    ← RingHom.mapMatrix_apply, mapMatrix_fin_finMatN, mapMatrix_localMatN_of_ne (Fin 3) (𝓞 ℚ) ℚ v _ hwv]

private theorem componentAt3_localToAdelic3_self (v : HeightOneSpectrum (𝓞 ℚ)) (k : LocalGL3 v) :
    componentAt3 (𝓞 ℚ) ℚ v (localToAdelic3 v k) = k := by
  apply Units.ext
  change ((AdelicLevel.finAdeleEval (𝓞 ℚ) ℚ v).comp (AdelicLevel.adeleFin (𝓞 ℚ) ℚ)).mapMatrix
    (finMatN (Fin 3) (𝓞 ℚ) ℚ (localMatN (Fin 3) (𝓞 ℚ) ℚ v (k : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)))) = k
  rw [RingHom.mapMatrix_apply, RingHom.coe_comp, ← Matrix.map_map, ← RingHom.mapMatrix_apply,
    ← RingHom.mapMatrix_apply, mapMatrix_fin_finMatN, mapMatrix_localMatN_self]

private theorem componentAt3_upperUnipotent3 (v : HeightOneSpectrum (𝓞 ℚ)) (x y z : AdeleRing (𝓞 ℚ) ℚ) :
    componentAt3 (𝓞 ℚ) ℚ v (upperUnipotent3 x y z) =
      upperUnipotent3 (AdelicLevel.finAdeleEval (𝓞 ℚ) ℚ v (AdelicLevel.adeleFin (𝓞 ℚ) ℚ x))
        (AdelicLevel.finAdeleEval (𝓞 ℚ) ℚ v (AdelicLevel.adeleFin (𝓞 ℚ) ℚ y))
        (AdelicLevel.finAdeleEval (𝓞 ℚ) ℚ v (AdelicLevel.adeleFin (𝓞 ℚ) ℚ z)) := by
  apply Units.ext
  ext i j
  rw [componentAt3, componentAtN, Matrix.GeneralLinearGroup.map_apply, upperUnipotent3_coe, upperUnipotent3_coe]
  fin_cases i <;> fin_cases j <;> simp

private theorem archComponent3_upperUnipotent3 (x y z : AdeleRing (𝓞 ℚ) ℚ) :
    archComponent3 (𝓞 ℚ) ℚ (upperUnipotent3 x y z) =
      upperUnipotent3 (AdelicLevel.adeleArch (𝓞 ℚ) ℚ x)
        (AdelicLevel.adeleArch (𝓞 ℚ) ℚ y)
        (AdelicLevel.adeleArch (𝓞 ℚ) ℚ z) := by
  apply Units.ext
  ext i j
  rw [archComponent3, archComponentN, Matrix.GeneralLinearGroup.map_apply, upperUnipotent3_coe, upperUnipotent3_coe]
  fin_cases i <;> fin_cases j <;> simp

private theorem archComponent3_localToAdelic3 {v : HeightOneSpectrum (𝓞 ℚ)} (k : LocalGL3 v) :
    archComponent3 (𝓞 ℚ) ℚ (localToAdelic3 v k) = 1 := by
  apply Units.ext
  rw [Units.val_one]
  change (AdelicLevel.adeleArch (𝓞 ℚ) ℚ).mapMatrix
    (finMatN (Fin 3) (𝓞 ℚ) ℚ (localMatN (Fin 3) (𝓞 ℚ) ℚ v (k : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)))) = 1
  rw [mapMatrix_arch_finMatN]

private theorem adelicGL_ext {X Y : AdelicGL 3 (𝓞 ℚ) ℚ} (harch : archComponent3 (𝓞 ℚ) ℚ X = archComponent3 (𝓞 ℚ) ℚ Y)
    (hfin : ∀ w : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ w X = componentAt3 (𝓞 ℚ) ℚ w Y) : X = Y := by
  apply Units.ext
  have h₁ := congrArg Units.val harch
  change (AdelicLevel.adeleArch (𝓞 ℚ) ℚ).mapMatrix (X : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) =
    (AdelicLevel.adeleArch (𝓞 ℚ) ℚ).mapMatrix (Y : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) at h₁
  refine matrixAdele_ext (Fin 3) (𝓞 ℚ) ℚ h₁ (matrixFin_ext (Fin 3) (𝓞 ℚ) ℚ fun w => ?_)
  have h₂ := congrArg Units.val (hfin w)
  change ((AdelicLevel.finAdeleEval (𝓞 ℚ) ℚ w).comp (AdelicLevel.adeleFin (𝓞 ℚ) ℚ)).mapMatrix
      (X : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) =
    ((AdelicLevel.finAdeleEval (𝓞 ℚ) ℚ w).comp (AdelicLevel.adeleFin (𝓞 ℚ) ℚ)).mapMatrix
      (Y : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) at h₂
  simp only [RingHom.mapMatrix_apply, RingHom.coe_comp, ← Matrix.map_map] at h₂
  simpa only [RingHom.mapMatrix_apply] using h₂

private theorem localToAdelic3_mul_eq_mul_localToAdelic3 {v : HeightOneSpectrum (𝓞 ℚ)} (h : LocalGL3 v)
    (X : AdelicGL 3 (𝓞 ℚ) ℚ) :
    localToAdelic3 v h * X =
      X * localToAdelic3 v ((componentAt3 (𝓞 ℚ) ℚ v X)⁻¹ * h * componentAt3 (𝓞 ℚ) ℚ v X) := by
  refine adelicGL_ext ?_ fun w => ?_
  · rw [map_mul, map_mul, archComponent3_localToAdelic3, archComponent3_localToAdelic3, one_mul, mul_one]
  · by_cases hw : w = v
    · subst hw
      rw [map_mul, map_mul, componentAt3_localToAdelic3_self, componentAt3_localToAdelic3_self, ← mul_assoc,
        ← mul_assoc, mul_inv_cancel, one_mul]
    · rw [map_mul, map_mul, componentAt3_localToAdelic3_of_ne hw, componentAt3_localToAdelic3_of_ne hw, one_mul,
        mul_one]

private theorem adeleArch_adeleSingleAt {v : HeightOneSpectrum (𝓞 ℚ)} (x : v.adicCompletion ℚ) :
    AdelicLevel.adeleArch (𝓞 ℚ) ℚ (adeleSingleAt ℚ v x) = 0 :=
  rfl

private theorem finAdeleEval_adeleFin_adeleSingleAt {v : HeightOneSpectrum (𝓞 ℚ)} (w : HeightOneSpectrum (𝓞 ℚ))
    (x : v.adicCompletion ℚ) :
    AdelicLevel.finAdeleEval (𝓞 ℚ) ℚ w (AdelicLevel.adeleFin (𝓞 ℚ) ℚ (adeleSingleAt ℚ v x)) =
      finAdeleSingleAt ℚ v x w :=
  rfl

private theorem upperUnipotent3_adeleSingleAt {v : HeightOneSpectrum (𝓞 ℚ)} (x y z : v.adicCompletion ℚ) :
    upperUnipotent3 (adeleSingleAt ℚ v x) (adeleSingleAt ℚ v y) (adeleSingleAt ℚ v z) =
      localToAdelic3 v (upperUnipotent3 x y z) := by
  refine adelicGL_ext ?_ fun w => ?_
  · rw [archComponent3_localToAdelic3, archComponent3_upperUnipotent3, adeleArch_adeleSingleAt,
      adeleArch_adeleSingleAt, adeleArch_adeleSingleAt, upperUnipotent3_zero]
  · rw [componentAt3_upperUnipotent3, finAdeleEval_adeleFin_adeleSingleAt, finAdeleEval_adeleFin_adeleSingleAt,
      finAdeleEval_adeleFin_adeleSingleAt]
    by_cases hw : w = v
    · subst hw
      rw [componentAt3_localToAdelic3_self, finAdeleSingleAt_apply_self, finAdeleSingleAt_apply_self,
        finAdeleSingleAt_apply_self]
    · rw [componentAt3_localToAdelic3_of_ne hw, finAdeleSingleAt_apply_of_ne ℚ v x hw,
        finAdeleSingleAt_apply_of_ne ℚ v y hw, finAdeleSingleAt_apply_of_ne ℚ v z hw, upperUnipotent3_zero]

private theorem upperUnipotent3_zero_adeleSingleAt_zero {v : HeightOneSpectrum (𝓞 ℚ)} (t : v.adicCompletion ℚ) :
    upperUnipotent3 (0 : AdeleRing (𝓞 ℚ) ℚ) (adeleSingleAt ℚ v t) 0 = localToAdelic3 v (upperUnipotent3 0 t 0) := by
  rw [← map_zero (adeleSingleAt ℚ v)]
  exact upperUnipotent3_adeleSingleAt 0 t 0

private theorem radicalP21_adeleSingleAt {v : HeightOneSpectrum (𝓞 ℚ)} (ℓ : Fin 2 → v.adicCompletion ℚ) :
    radicalP21 (fun j => adeleSingleAt ℚ v (ℓ j)) = localToAdelic3 v (radicalP21 ℓ) := by
  show upperUnipotent3 (0 : AdeleRing (𝓞 ℚ) ℚ) (adeleSingleAt ℚ v (ℓ 1)) (adeleSingleAt ℚ v (ℓ 0)) =
    localToAdelic3 v (upperUnipotent3 0 (ℓ 1) (ℓ 0))
  rw [← map_zero (adeleSingleAt ℚ v)]
  exact upperUnipotent3_adeleSingleAt 0 (ℓ 1) (ℓ 0)

private theorem algebraMap_adeleRing_snd_apply (q : ℚ) (w : HeightOneSpectrum (𝓞 ℚ)) :
    (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) q).2 w = algebraMap ℚ (w.adicCompletion ℚ) q := by
  rw [AdeleRing.algebraMap_snd_apply, IsDedekindDomain.HeightOneSpectrum.algebraMap_adicCompletion]
  rfl

private theorem algebraMap_mul_adeleSingleAt {v : HeightOneSpectrum (𝓞 ℚ)} (q : ℚ) (x : v.adicCompletion ℚ) :
    algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) q * adeleSingleAt ℚ v x =
      adeleSingleAt ℚ v (algebraMap ℚ (v.adicCompletion ℚ) q * x) := by
  refine Prod.ext ?_ (FiniteAdeleRing.ext ℚ fun w => ?_)
  · show (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) q).1 * (0 : InfiniteAdeleRing ℚ) = 0
    exact mul_zero _
  · show (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) q).2 w * finAdeleSingleAt ℚ v x w =
      finAdeleSingleAt ℚ v (algebraMap ℚ (v.adicCompletion ℚ) q * x) w
    by_cases hw : w = v
    · subst hw
      rw [finAdeleSingleAt_apply_self, finAdeleSingleAt_apply_self, algebraMap_adeleRing_snd_apply]
    · rw [finAdeleSingleAt_apply_of_ne ℚ v x hw, finAdeleSingleAt_apply_of_ne ℚ v _ hw, mul_zero]

private theorem valued_det_eq_one_of_mem_localMaximalCompact3_aux16 {v : HeightOneSpectrum (𝓞 ℚ)} {k : LocalGL3 v}
    (hk : k ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v) :
    Valued.v ((k : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)).det) = 1 := by
  have h1 : Valued.v ((k : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)).det) ≤ 1 := valued_det_le_one_of_forall_le hk.1
  have h2 : Valued.v (((k⁻¹ : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)).det) ≤ 1 :=
    valued_det_le_one_of_forall_le hk.2
  have h3 : Valued.v ((k : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)).det) *
      Valued.v (((k⁻¹ : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)).det) = 1 := by
    rw [← map_mul, ← Matrix.det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.det_one, map_one]
  exact le_antisymm h1 (by
    calc (1 : WithZero (Multiplicative ℤ)) = _ * _ := h3.symm
      _ ≤ Valued.v ((k : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)).det) * 1 := mul_le_mul' le_rfl h2
      _ = _ := mul_one _)

private theorem valued_apply_two_two_eq_one_of_mem_of_pos {v : HeightOneSpectrum (𝓞 ℚ)} {n : ℕ} (hn : 1 ≤ n)
    {k : LocalGL3 v} (hk : k ∈ converseCongruenceSet3 v n) :
    Valued.v ((k : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 2 2) = 1 := by
  obtain ⟨hkK, -, hk0, hk21⟩ := hk
  have hk1 : Valued.v ((k : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 2 1) ≤ WithZero.exp (-(n : ℤ)) :=
    hk21.trans (WithZero.exp_le_exp.mpr (by omega))
  set A : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ) := (k : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) with hA
  have hdet : Valued.v A.det = 1 := valued_det_eq_one_of_mem_localMaximalCompact3_aux16 hkK
  have hε : WithZero.exp (-(n : ℤ)) < (1 : WithZero (Multiplicative ℤ)) := by
    rw [← WithZero.exp_zero]
    exact WithZero.exp_lt_exp.mpr (by omega)
  have hsmall : ∀ {x y z : v.adicCompletion ℚ}, Valued.v x ≤ 1 → Valued.v y ≤ 1 →
      Valued.v z ≤ WithZero.exp (-(n : ℤ)) → Valued.v (x * y * z) < 1 := fun hx hy hz => by
    rw [map_mul, map_mul]
    calc Valued.v _ * Valued.v _ * Valued.v _ ≤ 1 * 1 * WithZero.exp (-(n : ℤ)) :=
          mul_le_mul' (mul_le_mul' hx hy) hz
      _ = WithZero.exp (-(n : ℤ)) := by rw [mul_one, one_mul]
      _ < 1 := hε
  have hsplit : A.det = A 2 2 * (A 0 0 * A 1 1 - A 0 1 * A 1 0) +
      (A 0 1 * A 1 2 * A 2 0 + A 0 2 * A 1 0 * A 2 1 - A 0 0 * A 1 2 * A 2 1 - A 0 2 * A 1 1 * A 2 0) := by
    rw [Matrix.det_fin_three]
    ring
  have hrest : Valued.v (A 0 1 * A 1 2 * A 2 0 + A 0 2 * A 1 0 * A 2 1 - A 0 0 * A 1 2 * A 2 1 -
      A 0 2 * A 1 1 * A 2 0) < 1 := by
    refine lt_of_le_of_lt (Valuation.map_sub _ _ _) (max_lt ?_ (hsmall (hkK.1 0 2) (hkK.1 1 1) hk0))
    refine lt_of_le_of_lt (Valuation.map_sub _ _ _) (max_lt ?_ (hsmall (hkK.1 0 0) (hkK.1 1 2) hk1))
    exact lt_of_le_of_lt (Valuation.map_add _ _ _)
      (max_lt (hsmall (hkK.1 0 1) (hkK.1 1 2) hk0) (hsmall (hkK.1 0 2) (hkK.1 1 0) hk1))
  by_contra hne
  have hlt : Valued.v (A 2 2) < 1 := lt_of_le_of_ne (hkK.1 2 2) hne
  have hminor : Valued.v (A 0 0 * A 1 1 - A 0 1 * A 1 0) ≤ 1 := by
    refine le_trans (Valuation.map_sub _ _ _) (max_le ?_ ?_)
    · rw [map_mul]
      exact mul_le_one' (hkK.1 0 0) (hkK.1 1 1)
    · rw [map_mul]
      exact mul_le_one' (hkK.1 0 1) (hkK.1 1 0)
  have hmain : Valued.v (A 2 2 * (A 0 0 * A 1 1 - A 0 1 * A 1 0)) < 1 := by
    rw [map_mul]
    calc Valued.v (A 2 2) * Valued.v (A 0 0 * A 1 1 - A 0 1 * A 1 0) ≤ Valued.v (A 2 2) * 1 :=
          mul_le_mul' le_rfl hminor
      _ = Valued.v (A 2 2) := mul_one _
      _ < 1 := hlt
  have hcontra : Valued.v A.det < 1 := by
    rw [hsplit]
    exact lt_of_le_of_lt (Valuation.map_add _ _ _) (max_lt hmain hrest)
  exact absurd hdet hcontra.ne

private theorem globalPoints_entry (X : GL (Fin 2) ℚ) (a b : Fin 2) :
    ((globalPoints (𝓞 ℚ) ℚ X : AdelicGL2 (𝓞 ℚ) ℚ) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) a b =
      algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) ((X : Matrix (Fin 2) (Fin 2) ℚ) a b) :=
  Matrix.GeneralLinearGroup.map_apply _ _ _ _

private theorem finAdeleEval_adeleFin_algebraMap (q : ℚ) (w : HeightOneSpectrum (𝓞 ℚ)) :
    AdelicLevel.finAdeleEval (𝓞 ℚ) ℚ w (AdelicLevel.adeleFin (𝓞 ℚ) ℚ (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) q)) =
      algebraMap ℚ (w.adicCompletion ℚ) q :=
  algebraMap_adeleRing_snd_apply q w

private theorem coe_componentAt3_iotaGL_globalPoints (v : HeightOneSpectrum (𝓞 ℚ)) (γ : GL (Fin 2) ℚ) :
    ((componentAt3 (𝓞 ℚ) ℚ v (iotaGL (globalPoints (𝓞 ℚ) ℚ γ)) : GL (Fin 3) (v.adicCompletion ℚ)) :
        Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) =
      !![algebraMap ℚ (v.adicCompletion ℚ) ((γ : Matrix (Fin 2) (Fin 2) ℚ) 0 0),
          algebraMap ℚ (v.adicCompletion ℚ) ((γ : Matrix (Fin 2) (Fin 2) ℚ) 0 1), 0;
        algebraMap ℚ (v.adicCompletion ℚ) ((γ : Matrix (Fin 2) (Fin 2) ℚ) 1 0),
          algebraMap ℚ (v.adicCompletion ℚ) ((γ : Matrix (Fin 2) (Fin 2) ℚ) 1 1), 0;
        0, 0, 1] := by
  have hM : embedMat2 ((globalPoints (𝓞 ℚ) ℚ γ : AdelicGL2 (𝓞 ℚ) ℚ) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) =
      !![algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) ((γ : Matrix (Fin 2) (Fin 2) ℚ) 0 0),
          algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) ((γ : Matrix (Fin 2) (Fin 2) ℚ) 0 1), 0;
        algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) ((γ : Matrix (Fin 2) (Fin 2) ℚ) 1 0),
          algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) ((γ : Matrix (Fin 2) (Fin 2) ℚ) 1 1), 0;
        0, 0, 1] := by
    rw [embedMat2, globalPoints_entry, globalPoints_entry, globalPoints_entry, globalPoints_entry]
  ext i j
  rw [componentAt3, componentAtN, Matrix.GeneralLinearGroup.map_apply, coe_iotaGL, hM]
  fin_cases i <;> fin_cases j <;>
    first
      | exact finAdeleEval_adeleFin_algebraMap _ _
      | exact map_zero _
      | exact map_one _
end
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_mirabolicSeries_eq_dual_of_radicalCoefficient_eq.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_mirabolicSeries_eq_dual_of_radicalCoefficient_eq.LanglandsTunnell.CubicInduction"
end LanglandsTunnell.CubicInduction
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_mirabolicSeries_eq_dual_of_radicalCoefficient_eq.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_mirabolicSeries_eq_dual_of_radicalCoefficient_eq.LanglandsTunnell.CubicInduction"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_mirabolicSeries_eq_dual_of_radicalCoefficient_eq.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_mirabolicSeries_eq_dual_of_radicalCoefficient_eq.LanglandsTunnell.CubicInduction"

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "Converse.IsAdmissibleTwist TateLocal.addCharLevel TateLocal.localBorel TateLocal.borelSpace_localBorel TateLocal.integersPositiveCompacts TateLocal.coe_integersPositiveCompacts TateLocal.selfDualHaarAt TateLocal.higherUnitsAt TateLocal.forall_eq_one_and_exists_ne_one_of_addCharLevel"
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "matrixFin_ext matrixAdele_ext localMatN mapMatrix_localMatN_self mapMatrix_localMatN_of_ne finMatN mapMatrix_arch_finMatN mapMatrix_fin_finMatN localToAdelic3 converseCongruenceSet3 HasVanishingUnipotentIntegralAlong IsCongruenceEquivariantAlong lowerUnipotent21 longWeyl3 longWeyl3_coe dualWhittakerFn3 dualWhittakerFn3_apply weylPrime3 weylPrime3_coe weylPrime3_mul_self transposeInv3_weylPrime3 weylPrime3_mul_transposeInv3_radicalP21_mul_weylPrime3 IsGL3PsiWhittakerFn transposeInv3 IsCuspidalAlongP21 psiLoc mirabolicTranslate AdelicGL globalPointsGL centralScalarGL upperUnipotent3 upperUnipotent3_coe upperUnipotent3_zero radicalP21 radicalP21_zero radicalP21_coe radicalP21_add embedMat2 iotaGL coe_iotaGL iota MirabolicIndex mirabolicRep mirabolicRep_spec mirabolic_mk_unipotent_mul localMaximalCompact3 componentAtN archComponentN componentAt3 archComponent3 LocalGL3 cosetSum IsCosetEigenfunction IsRightInvariant diagUnitGL2 diagHom diagHom_apply isCuspidalAlongP21_mirabolicSeries"
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"
section
open IsDedekindDomain NumberField NumberField.StandardAddChar AutomorphicForm

private theorem exists_valued_le_one_and_addChar_algebraMap_mul_adeleSingleAt_ne_one
    (ψ : AddChar 𝔸 ℂ) (hψ : IsGlobalAddChar ℚ ψ) (v : HeightOneSpectrum (𝓞 ℚ))
    (h0 : LanglandsTunnell.TateLocal.addCharLevel (psiLoc ψ v) = 0) (β : ℚ)
    (hβ : ¬ Valued.v (algebraMap ℚ (v.adicCompletion ℚ) β) ≤ 1) :
    ∃ ℓ : v.adicCompletion ℚ, Valued.v ℓ ≤ 1 ∧ ψ (algebraMap ℚ 𝔸 β * adeleSingleAt ℚ v ℓ) ≠ 1 := by
  obtain ⟨x, hx, hne⟩ := exists_psiLoc_ne_one_of_addCharLevel_eq_zero ψ v hψ h0
  obtain ⟨b, hb⟩ : ∃ b : v.adicCompletion ℚ, b = algebraMap ℚ (v.adicCompletion ℚ) β := ⟨_, rfl⟩
  rw [← hb] at hβ
  have hb0 : b ≠ 0 := by
    rintro rfl
    exact hβ (by rw [map_zero]; exact zero_le')
  have hv0 : Valued.v b ≠ 0 := (Valuation.ne_zero_iff _).mpr hb0
  have hvb : Valued.v b = WithZero.exp (WithZero.log (Valued.v b)) := (WithZero.exp_log hv0).symm
  have hpos : (0 : ℤ) < WithZero.log (Valued.v b) := by
    refine lt_of_not_ge fun hle => hβ ?_
    calc Valued.v b = WithZero.exp (WithZero.log (Valued.v b)) := hvb
      _ ≤ WithZero.exp (0 : ℤ) := WithZero.exp_le_exp.mpr hle
      _ = 1 := WithZero.exp_zero
  refine ⟨b⁻¹ * x, ?_, ?_⟩
  · calc Valued.v (b⁻¹ * x) = (Valued.v b)⁻¹ * Valued.v x := by rw [map_mul, map_inv₀]
      _ ≤ (Valued.v b)⁻¹ * WithZero.exp (1 : ℤ) := mul_le_mul' le_rfl hx
      _ = WithZero.exp (-WithZero.log (Valued.v b) + 1) := by
          rw [WithZero.exp_add, WithZero.exp_neg, ← hvb]
      _ ≤ WithZero.exp (0 : ℤ) := WithZero.exp_le_exp.mpr (by omega)
      _ = 1 := WithZero.exp_zero
  · rw [algebraMap_mul_adeleSingleAt, ← hb, mul_inv_cancel_left₀ hb0]
    simpa only [psiLoc, AddChar.compAddMonoidHom_apply] using hne

private theorem addChar_algebraMap_mul_adeleSingleAt_eq_one_of_valued_le
    (ψ : AddChar 𝔸 ℂ) (hψ : IsGlobalAddChar ℚ ψ) (v : HeightOneSpectrum (𝓞 ℚ))
    (h0 : LanglandsTunnell.TateLocal.addCharLevel (psiLoc ψ v) = 0) (β : ℚ)
    (hβ : Valued.v (algebraMap ℚ (v.adicCompletion ℚ) β) ≤ WithZero.exp (-1 : ℤ))
    (t : v.adicCompletion ℚ) (ht : Valued.v t ≤ WithZero.exp (1 : ℤ)) :
    ψ (algebraMap ℚ 𝔸 β * adeleSingleAt ℚ v t) = 1 := by
  rw [algebraMap_mul_adeleSingleAt]
  have hint : Valued.v (algebraMap ℚ (v.adicCompletion ℚ) β * t) ≤ 1 := by
    calc Valued.v (algebraMap ℚ (v.adicCompletion ℚ) β * t)
        = Valued.v (algebraMap ℚ (v.adicCompletion ℚ) β) * Valued.v t := map_mul _ _ _
      _ ≤ WithZero.exp (-1 : ℤ) * WithZero.exp (1 : ℤ) := mul_le_mul' hβ ht
      _ = 1 := by rw [← WithZero.exp_add, neg_add_cancel, WithZero.exp_zero]
  simpa only [psiLoc, AddChar.compAddMonoidHom_apply] using
    psiLoc_apply_eq_one_of_addCharLevel_eq_zero ψ v hψ h0 _ hint
end
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_mirabolicSeries_eq_dual_of_radicalCoefficient_eq.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_mirabolicSeries_eq_dual_of_radicalCoefficient_eq.LanglandsTunnell.CubicInduction"
end LanglandsTunnell.CubicInduction
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_mirabolicSeries_eq_dual_of_radicalCoefficient_eq.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_mirabolicSeries_eq_dual_of_radicalCoefficient_eq.LanglandsTunnell.CubicInduction"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_mirabolicSeries_eq_dual_of_radicalCoefficient_eq.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_mirabolicSeries_eq_dual_of_radicalCoefficient_eq.LanglandsTunnell.CubicInduction"

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "Converse.IsAdmissibleTwist TateLocal.addCharLevel TateLocal.localBorel TateLocal.borelSpace_localBorel TateLocal.integersPositiveCompacts TateLocal.coe_integersPositiveCompacts TateLocal.selfDualHaarAt TateLocal.higherUnitsAt TateLocal.forall_eq_one_and_exists_ne_one_of_addCharLevel"
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "matrixFin_ext matrixAdele_ext localMatN mapMatrix_localMatN_self mapMatrix_localMatN_of_ne finMatN mapMatrix_arch_finMatN mapMatrix_fin_finMatN localToAdelic3 converseCongruenceSet3 HasVanishingUnipotentIntegralAlong IsCongruenceEquivariantAlong lowerUnipotent21 longWeyl3 longWeyl3_coe dualWhittakerFn3 dualWhittakerFn3_apply weylPrime3 weylPrime3_coe weylPrime3_mul_self transposeInv3_weylPrime3 weylPrime3_mul_transposeInv3_radicalP21_mul_weylPrime3 IsGL3PsiWhittakerFn transposeInv3 IsCuspidalAlongP21 psiLoc mirabolicTranslate AdelicGL globalPointsGL centralScalarGL upperUnipotent3 upperUnipotent3_coe upperUnipotent3_zero radicalP21 radicalP21_zero radicalP21_coe radicalP21_add embedMat2 iotaGL coe_iotaGL iota MirabolicIndex mirabolicRep mirabolicRep_spec mirabolic_mk_unipotent_mul localMaximalCompact3 componentAtN archComponentN componentAt3 archComponent3 LocalGL3 cosetSum IsCosetEigenfunction IsRightInvariant diagUnitGL2 diagHom diagHom_apply isCuspidalAlongP21_mirabolicSeries"
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"
section
open IsDedekindDomain NumberField NumberField.TateGlobal AutomorphicForm LanglandsTunnell.Converse
open scoped Matrix

section Furniture

variable {A : Type*} [CommRing A]

private theorem transposeInv3_mul_aux18 (g h : GL (Fin 3) A) :
    transposeInv3 (g * h) = transposeInv3 g * transposeInv3 h := by
  refine Units.ext ?_
  change ((((g * h)⁻¹ : GL (Fin 3) A)) : Matrix (Fin 3) (Fin 3) A)ᵀ = _
  rw [_root_.mul_inv_rev, Units.val_mul, Matrix.transpose_mul]
  rfl

private theorem transposeInv3_transposeInv3_aux18 (g : GL (Fin 3) A) : transposeInv3 (transposeInv3 g) = g := by
  refine Units.ext ?_
  change ((((transposeInv3 g)⁻¹ : GL (Fin 3) A)) : Matrix (Fin 3) (Fin 3) A)ᵀ = _
  have h : ((((transposeInv3 g)⁻¹ : GL (Fin 3) A)) : Matrix (Fin 3) (Fin 3) A) =
      ((g : GL (Fin 3) A) : Matrix (Fin 3) (Fin 3) A)ᵀ := rfl
  rw [h, Matrix.transpose_transpose]

private def lowerTransvection31 (x : A) : GL (Fin 3) A where
  val := !![1, 0, 0; 0, 1, 0; x, 0, 1]
  inv := !![1, 0, 0; 0, 1, 0; -x, 0, 1]
  val_inv := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]
  inv_val := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]

private theorem lowerTransvection31_coe (x : A) :
    (lowerTransvection31 x : Matrix (Fin 3) (Fin 3) A) = !![1, 0, 0; 0, 1, 0; x, 0, 1] := rfl

private theorem lowerTransvection31_inv_coe (x : A) :
    (((lowerTransvection31 x)⁻¹ : GL (Fin 3) A) : Matrix (Fin 3) (Fin 3) A) = !![1, 0, 0; 0, 1, 0; -x, 0, 1] :=
  rfl

private theorem upperUnipotent3_inv_coe (x y z : A) :
    (((upperUnipotent3 x y z)⁻¹ : GL (Fin 3) A) : Matrix (Fin 3) (Fin 3) A) =
      !![1, -x, x * y - z; 0, 1, -y; 0, 0, 1] :=
  rfl

end Furniture
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_mirabolicSeries_eq_dual_of_radicalCoefficient_eq.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_mirabolicSeries_eq_dual_of_radicalCoefficient_eq.LanglandsTunnell.CubicInduction"

section Dichotomy

variable {v : HeightOneSpectrum (𝓞 ℚ)}

private theorem exp_neg_le_one (a : ℕ) : WithZero.exp (-(a : ℤ)) ≤ (1 : WithZero (Multiplicative ℤ)) := by
  rw [← WithZero.exp_zero]
  exact WithZero.exp_le_exp.mpr (by omega)

private theorem lowerTransvection31_mem (a : ℕ) {x : v.adicCompletion ℚ}
    (hx : Valued.v x ≤ WithZero.exp (-(a : ℤ))) :
    (lowerTransvection31 x : LocalGL3 v) ∈ converseCongruenceSet3 v a := by
  have hx1 : Valued.v x ≤ 1 := hx.trans (exp_neg_le_one a)
  refine ⟨⟨?_, ?_⟩, ?_, ?_, ?_⟩
  · intro i j
    rw [lowerTransvection31_coe]
    fin_cases i <;> fin_cases j <;> simp [hx1]
  · intro i j
    rw [lowerTransvection31_inv_coe]
    fin_cases i <;> fin_cases j <;> simp [Valuation.map_neg, hx1]
  · rw [lowerTransvection31_coe]
    simp
  · rw [lowerTransvection31_coe]
    simpa using hx
  · rw [lowerTransvection31_coe]
    simp

private theorem upperUnipotent3_zero_zero_one_mem (a : ℕ) :
    (upperUnipotent3 (0 : v.adicCompletion ℚ) 0 1 : LocalGL3 v) ∈ converseCongruenceSet3 v a := by
  refine ⟨⟨?_, ?_⟩, ?_, ?_, ?_⟩
  · intro i j
    rw [upperUnipotent3_coe]
    fin_cases i <;> fin_cases j <;> simp
  · intro i j
    rw [upperUnipotent3_inv_coe]
    fin_cases i <;> fin_cases j <;> simp [Valuation.map_neg]
  · rw [upperUnipotent3_coe]
    simp
  · rw [upperUnipotent3_coe]
    simp
  · rw [upperUnipotent3_coe]
    simp

private theorem lowerTransvection31_mul_upperUnipotent3_apply (x : v.adicCompletion ℚ) :
    (((lowerTransvection31 x * upperUnipotent3 0 0 1 : LocalGL3 v)) :
      Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 2 2 = x + 1 := by
  rw [Units.val_mul, lowerTransvection31_coe, upperUnipotent3_coe]
  simp [Matrix.mul_apply, Fin.sum_univ_three]

end Dichotomy
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_mirabolicSeries_eq_dual_of_radicalCoefficient_eq.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_mirabolicSeries_eq_dual_of_radicalCoefficient_eq.LanglandsTunnell.CubicInduction"

variable {v : HeightOneSpectrum (𝓞 ℚ)} {a : ℕ} {χ : (v.adicCompletion ℚ)ˣ →* ℂˣ} {W : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ}

private theorem mirabolicSeries_mul_localToAdelic3 (hWK : IsCongruenceEquivariantAlong v a χ W)
    {k : LocalGL3 v} (hk : k ∈ converseCongruenceSet3 v a) (u : (v.adicCompletion ℚ)ˣ)
    (hu : (u : v.adicCompletion ℚ) = (k : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 2 2)
    (g : AdelicGL 3 (𝓞 ℚ) ℚ) :
    (∑' i : MirabolicIndex ℚ, W (mirabolicTranslate i * (g * localToAdelic3 v k))) =
      ((χ u : ℂˣ) : ℂ) * ∑' i : MirabolicIndex ℚ, W (mirabolicTranslate i * g) := by
  rw [← tsum_mul_left]
  exact tsum_congr fun i => by rw [← mul_assoc, hWK k hk u hu]

private theorem dualWhittakerFn3_mul_transposeInv3_localToAdelic3 (hWK : IsCongruenceEquivariantAlong v a χ W)
    {k : LocalGL3 v} (hk : k ∈ converseCongruenceSet3 v a) (u : (v.adicCompletion ℚ)ˣ)
    (hu : (u : v.adicCompletion ℚ) = (k : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 2 2)
    (h : AdelicGL 3 (𝓞 ℚ) ℚ) :
    dualWhittakerFn3 W (h * transposeInv3 (localToAdelic3 v k)) = ((χ u : ℂˣ) : ℂ) * dualWhittakerFn3 W h := by
  simp only [dualWhittakerFn3]
  rw [transposeInv3_mul_aux18, transposeInv3_transposeInv3_aux18, ← mul_assoc]
  exact hWK k hk u hu _

private theorem dualMirabolicSeries_mul_localToAdelic3 (hWK : IsCongruenceEquivariantAlong v a χ W)
    {k : LocalGL3 v} (hk : k ∈ converseCongruenceSet3 v a) (u : (v.adicCompletion ℚ)ˣ)
    (hu : (u : v.adicCompletion ℚ) = (k : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 2 2)
    (g : AdelicGL 3 (𝓞 ℚ) ℚ) :
    (∑' i : MirabolicIndex ℚ, dualWhittakerFn3 W (mirabolicTranslate i *
        (weylPrime3 * transposeInv3 (g * localToAdelic3 v k)))) =
      ((χ u : ℂˣ) : ℂ) *
        ∑' i : MirabolicIndex ℚ, dualWhittakerFn3 W (mirabolicTranslate i * (weylPrime3 * transposeInv3 g)) := by
  rw [← tsum_mul_left]
  refine tsum_congr fun i => ?_
  rw [transposeInv3_mul_aux18,
    ← dualWhittakerFn3_mul_transposeInv3_localToAdelic3 hWK hk u hu
      (mirabolicTranslate i * (weylPrime3 * transposeInv3 g))]
  congr 1
  simp only [mul_assoc]

private theorem eq_zero_or_forall_eq_one_of_isCongruenceEquivariantAlong (hWK : IsCongruenceEquivariantAlong v a χ W) :
    (∀ g, W g = 0) ∨
      ∀ u : (v.adicCompletion ℚ)ˣ, Valued.v ((u : v.adicCompletion ℚ) - 1) ≤ WithZero.exp (-(a : ℤ)) → χ u = 1 := by
  by_cases hW : ∀ g, W g = 0
  · exact Or.inl hW
  right
  obtain ⟨g₀, hg₀⟩ := not_forall.mp hW
  intro u hu
  set x : v.adicCompletion ℚ := (u : v.adicCompletion ℚ) - 1 with hx
  have hk : (lowerTransvection31 x : LocalGL3 v) ∈ converseCongruenceSet3 v a := lowerTransvection31_mem a hu
  have hk' : (upperUnipotent3 (0 : v.adicCompletion ℚ) 0 1 : LocalGL3 v) ∈ converseCongruenceSet3 v a :=
    upperUnipotent3_zero_zero_one_mem a
  have hu' : (u : v.adicCompletion ℚ) =
      (((lowerTransvection31 x * upperUnipotent3 0 0 1 : LocalGL3 v)) :
        Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 2 2 := by
    rw [lowerTransvection31_mul_upperUnipotent3_apply, hx, sub_add_cancel]
  have h1 : (1 : (v.adicCompletion ℚ)ˣ) = (((lowerTransvection31 x : LocalGL3 v)) :
      Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 2 2 := by
    rw [lowerTransvection31_coe]; simp
  have h1' : (1 : (v.adicCompletion ℚ)ˣ) = (((upperUnipotent3 (0 : v.adicCompletion ℚ) 0 1 : LocalGL3 v)) :
      Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 2 2 := by
    rw [upperUnipotent3_coe]; simp

  have hwhole := hWK _ (mul_mem_converseCongruenceSet3 hk hk') u hu' g₀
  have hfactors : W (g₀ * localToAdelic3 v (lowerTransvection31 x * upperUnipotent3 0 0 1)) = W g₀ := by
    rw [map_mul, ← mul_assoc, hWK _ hk' 1 h1', hWK _ hk 1 h1, map_one, Units.val_one, one_mul, one_mul]
  have hmul : ((χ u : ℂˣ) : ℂ) * W g₀ = W g₀ := hwhole.symm.trans hfactors
  have hsub : (((χ u : ℂˣ) : ℂ) - 1) * W g₀ = 0 := by rw [sub_mul, one_mul, hmul, sub_self]
  rcases mul_eq_zero.mp hsub with h | h
  · exact Units.val_eq_one.mp (sub_eq_zero.mp h)
  · exact absurd h hg₀
end
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_mirabolicSeries_eq_dual_of_radicalCoefficient_eq.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_mirabolicSeries_eq_dual_of_radicalCoefficient_eq.LanglandsTunnell.CubicInduction"
end LanglandsTunnell.CubicInduction
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_mirabolicSeries_eq_dual_of_radicalCoefficient_eq.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_mirabolicSeries_eq_dual_of_radicalCoefficient_eq.LanglandsTunnell.CubicInduction"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_mirabolicSeries_eq_dual_of_radicalCoefficient_eq.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_mirabolicSeries_eq_dual_of_radicalCoefficient_eq.LanglandsTunnell.CubicInduction"

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "Converse.IsAdmissibleTwist TateLocal.addCharLevel TateLocal.localBorel TateLocal.borelSpace_localBorel TateLocal.integersPositiveCompacts TateLocal.coe_integersPositiveCompacts TateLocal.selfDualHaarAt TateLocal.higherUnitsAt TateLocal.forall_eq_one_and_exists_ne_one_of_addCharLevel"
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "matrixFin_ext matrixAdele_ext localMatN mapMatrix_localMatN_self mapMatrix_localMatN_of_ne finMatN mapMatrix_arch_finMatN mapMatrix_fin_finMatN localToAdelic3 converseCongruenceSet3 HasVanishingUnipotentIntegralAlong IsCongruenceEquivariantAlong lowerUnipotent21 longWeyl3 longWeyl3_coe dualWhittakerFn3 dualWhittakerFn3_apply weylPrime3 weylPrime3_coe weylPrime3_mul_self transposeInv3_weylPrime3 weylPrime3_mul_transposeInv3_radicalP21_mul_weylPrime3 IsGL3PsiWhittakerFn transposeInv3 IsCuspidalAlongP21 psiLoc mirabolicTranslate AdelicGL globalPointsGL centralScalarGL upperUnipotent3 upperUnipotent3_coe upperUnipotent3_zero radicalP21 radicalP21_zero radicalP21_coe radicalP21_add embedMat2 iotaGL coe_iotaGL iota MirabolicIndex mirabolicRep mirabolicRep_spec mirabolic_mk_unipotent_mul localMaximalCompact3 componentAtN archComponentN componentAt3 archComponent3 LocalGL3 cosetSum IsCosetEigenfunction IsRightInvariant diagUnitGL2 diagHom diagHom_apply isCuspidalAlongP21_mirabolicSeries"
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"
section
open IsDedekindDomain NumberField NumberField.TateGlobal NumberField.StandardAddChar AutomorphicForm LanglandsTunnell.Converse

variable {v : HeightOneSpectrum (𝓞 ℚ)}

private theorem radicalP21_inv_coe (ℓ : Fin 2 → v.adicCompletion ℚ) :
    (((radicalP21 ℓ)⁻¹ : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) =
      !![1, -0, 0 * ℓ 1 - ℓ 0; 0, 1, -ℓ 1; 0, 0, 1] :=
  rfl

private theorem radicalP21_mem (n : ℕ) {ℓ : Fin 2 → v.adicCompletion ℚ} (h0 : Valued.v (ℓ 0) ≤ 1)
    (h1 : Valued.v (ℓ 1) ≤ 1) : (radicalP21 ℓ : LocalGL3 v) ∈ converseCongruenceSet3 v n := by
  refine ⟨⟨?_, ?_⟩, ?_, ?_, ?_⟩
  · intro i j
    rw [radicalP21_coe]
    fin_cases i <;> fin_cases j <;> simp [h0, h1]
  · intro i j
    rw [radicalP21_inv_coe]
    fin_cases i <;> fin_cases j <;> simp [Valuation.map_neg, h0, h1]
  · rw [radicalP21_coe]
    simp
  · rw [radicalP21_coe]
    simp
  · rw [radicalP21_coe]
    simp

private theorem conj_apply_two_two_sub_one (X : LocalGL3 v) (ℓ : Fin 2 → v.adicCompletion ℚ) :
    ((X⁻¹ * radicalP21 ℓ * X : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 2 2 - 1 =
      ℓ 0 * (((X⁻¹ : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 2 0 *
          (X : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 2 2) +
        ℓ 1 * (((X⁻¹ : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 2 1 *
          (X : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 2 2) := by
  have hAB : ((X⁻¹ : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) *
      (X : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  rw [Units.val_mul, Units.val_mul, radicalP21_coe]
  revert hAB
  generalize ((X⁻¹ : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) = A
  generalize (X : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) = B
  intro hAB
  have h22 := congrFun (congrFun hAB 2) 2
  rw [Matrix.mul_apply, Fin.sum_univ_three, Matrix.one_apply_eq] at h22
  simp [Matrix.mul_apply, Fin.sum_univ_three]
  linear_combination h22

private theorem valued_conj_apply_two_two_sub_one_le {a : ℕ} {X : LocalGL3 v} (hX : X ∈ converseCongruenceSet3 v a)
    {ℓ : Fin 2 → v.adicCompletion ℚ} (h0 : Valued.v (ℓ 0) ≤ 1) (h1 : Valued.v (ℓ 1) ≤ 1) :
    Valued.v (((X⁻¹ * radicalP21 ℓ * X : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 2 2 - 1) ≤
      WithZero.exp (-(a : ℤ)) := by
  obtain ⟨-, -, hi20, hi21⟩ := inv_mem_converseCongruenceSet3 hX
  have hX22 : Valued.v ((X : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 2 2) ≤ 1 := hX.1.1 2 2
  have hi21' : Valued.v (((X⁻¹ : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 2 1) ≤
      WithZero.exp (-(a : ℤ)) :=
    hi21.trans (WithZero.exp_le_exp.mpr (by omega))
  rw [conj_apply_two_two_sub_one]
  refine Valuation.map_add_le _ ?_ ?_
  · rw [map_mul, map_mul]
    exact (mul_le_mul' h0 (valued_mul_le_of_le_one_right hi20 hX22)).trans (one_mul _).le
  · rw [map_mul, map_mul]
    exact (mul_le_mul' h1 (valued_mul_le_of_le_one_right hi21' hX22)).trans (one_mul _).le

variable {a : ℕ} {χ : (v.adicCompletion ℚ)ˣ →* ℂˣ} {W : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ}

private theorem radicalP21_pair_add (z y s t : AdeleRing (𝓞 ℚ) ℚ) :
    (radicalP21 ![z + s, y + t] : AdelicGL 3 (𝓞 ℚ) ℚ) = radicalP21 ![z, y] * radicalP21 ![s, t] := by
  rw [← radicalP21_add]
  congr 1
  ext j
  fin_cases j <;> rfl

private theorem radicalP21_pair_adeleSingleAt (ℓ : Fin 2 → v.adicCompletion ℚ) :
    (radicalP21 ![adeleSingleAt ℚ v (ℓ 0), adeleSingleAt ℚ v (ℓ 1)] : AdelicGL 3 (𝓞 ℚ) ℚ) =
      localToAdelic3 v (radicalP21 ℓ) := by
  rw [← radicalP21_adeleSingleAt]
  congr 1
  ext j
  fin_cases j <;> rfl

private theorem radicalP21_add_adeleSingleAt_mul (g : AdelicGL 3 (𝓞 ℚ) ℚ) (z y : AdeleRing (𝓞 ℚ) ℚ)
    (ℓ : Fin 2 → v.adicCompletion ℚ) :
    (radicalP21 ![z + adeleSingleAt ℚ v (ℓ 0), y + adeleSingleAt ℚ v (ℓ 1)] : AdelicGL 3 (𝓞 ℚ) ℚ) * g =
      radicalP21 ![z, y] * g *
        localToAdelic3 v ((componentAt3 (𝓞 ℚ) ℚ v g)⁻¹ * radicalP21 ℓ * componentAt3 (𝓞 ℚ) ℚ v g) := by
  rw [radicalP21_pair_add, radicalP21_pair_adeleSingleAt, mul_assoc, localToAdelic3_mul_eq_mul_localToAdelic3,
    ← mul_assoc]

private theorem exists_unit_of_conj (ha : 1 ≤ a) {X : LocalGL3 v} (hX : X ∈ converseCongruenceSet3 v a)
    {ℓ : Fin 2 → v.adicCompletion ℚ} (h0 : Valued.v (ℓ 0) ≤ 1) (h1 : Valued.v (ℓ 1) ≤ 1) :
    ∃ u : (v.adicCompletion ℚ)ˣ,
      (u : v.adicCompletion ℚ) =
          ((X⁻¹ * radicalP21 ℓ * X : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 2 2 ∧
        Valued.v ((u : v.adicCompletion ℚ) - 1) ≤ WithZero.exp (-(a : ℤ)) := by
  have hk : (X⁻¹ * radicalP21 ℓ * X : LocalGL3 v) ∈ converseCongruenceSet3 v a :=
    mul_mem_converseCongruenceSet3 (mul_mem_converseCongruenceSet3 (inv_mem_converseCongruenceSet3 hX)
      (radicalP21_mem a h0 h1)) hX
  have hne : ((X⁻¹ * radicalP21 ℓ * X : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 2 2 ≠ 0 := by
    intro hzero
    have hunit := valued_apply_two_two_eq_one_of_mem_of_pos ha hk
    rw [hzero, map_zero] at hunit
    exact zero_ne_one hunit
  exact ⟨Units.mk0 _ hne, rfl, valued_conj_apply_two_two_sub_one_le hX h0 h1⟩

private theorem mirabolicSeries_radicalP21_add_adeleSingleAt (hWK : IsCongruenceEquivariantAlong v a χ W) (ha : 1 ≤ a)
    {g : AdelicGL 3 (𝓞 ℚ) ℚ} (hg : componentAt3 (𝓞 ℚ) ℚ v g ∈ converseCongruenceSet3 v a)
    (z y : AdeleRing (𝓞 ℚ) ℚ) (ℓ : Fin 2 → v.adicCompletion ℚ) (h0 : Valued.v (ℓ 0) ≤ 1)
    (h1 : Valued.v (ℓ 1) ≤ 1) :
    (∑' i : MirabolicIndex ℚ,
        W (mirabolicTranslate i * (radicalP21 ![z + adeleSingleAt ℚ v (ℓ 0), y + adeleSingleAt ℚ v (ℓ 1)] * g))) =
      ∑' i : MirabolicIndex ℚ, W (mirabolicTranslate i * (radicalP21 ![z, y] * g)) := by
  obtain ⟨u, hu, hu1⟩ := exists_unit_of_conj ha hg h0 h1
  have hk : (componentAt3 (𝓞 ℚ) ℚ v g)⁻¹ * radicalP21 ℓ * componentAt3 (𝓞 ℚ) ℚ v g ∈ converseCongruenceSet3 v a :=
    mul_mem_converseCongruenceSet3 (mul_mem_converseCongruenceSet3 (inv_mem_converseCongruenceSet3 hg)
      (radicalP21_mem a h0 h1)) hg
  rw [radicalP21_add_adeleSingleAt_mul, mirabolicSeries_mul_localToAdelic3 hWK hk u hu]
  rcases eq_zero_or_forall_eq_one_of_isCongruenceEquivariantAlong hWK with hW | hχ
  · simp only [hW, tsum_zero, mul_zero]
  · rw [hχ u hu1, Units.val_one, one_mul]

private theorem dualMirabolicSeries_radicalP21_add_adeleSingleAt
    (hWK : IsCongruenceEquivariantAlong v a χ W) (ha : 1 ≤ a)
    {g : AdelicGL 3 (𝓞 ℚ) ℚ} (hg : componentAt3 (𝓞 ℚ) ℚ v g ∈ converseCongruenceSet3 v a)
    (z y : AdeleRing (𝓞 ℚ) ℚ) (ℓ : Fin 2 → v.adicCompletion ℚ) (h0 : Valued.v (ℓ 0) ≤ 1)
    (h1 : Valued.v (ℓ 1) ≤ 1) :
    (∑' i : MirabolicIndex ℚ, dualWhittakerFn3 W (mirabolicTranslate i * (weylPrime3 * transposeInv3
        (radicalP21 ![z + adeleSingleAt ℚ v (ℓ 0), y + adeleSingleAt ℚ v (ℓ 1)] * g)))) =
      ∑' i : MirabolicIndex ℚ,
        dualWhittakerFn3 W (mirabolicTranslate i * (weylPrime3 * transposeInv3 (radicalP21 ![z, y] * g))) := by
  obtain ⟨u, hu, hu1⟩ := exists_unit_of_conj ha hg h0 h1
  have hk : (componentAt3 (𝓞 ℚ) ℚ v g)⁻¹ * radicalP21 ℓ * componentAt3 (𝓞 ℚ) ℚ v g ∈ converseCongruenceSet3 v a :=
    mul_mem_converseCongruenceSet3 (mul_mem_converseCongruenceSet3 (inv_mem_converseCongruenceSet3 hg)
      (radicalP21_mem a h0 h1)) hg
  rw [radicalP21_add_adeleSingleAt_mul, dualMirabolicSeries_mul_localToAdelic3 hWK hk u hu]
  rcases eq_zero_or_forall_eq_one_of_isCongruenceEquivariantAlong hWK with hW | hχ
  · simp only [hW, dualWhittakerFn3_apply, tsum_zero, mul_zero]
  · rw [hχ u hu1, Units.val_one, one_mul]

private theorem radicalDifference_add_adeleSingleAt (hWK : IsCongruenceEquivariantAlong v a χ W) (ha : 1 ≤ a)
    {g : AdelicGL 3 (𝓞 ℚ) ℚ} (hg : componentAt3 (𝓞 ℚ) ℚ v g ∈ converseCongruenceSet3 v a)
    (z y : AdeleRing (𝓞 ℚ) ℚ) (ℓ : Fin 2 → v.adicCompletion ℚ) (h0 : Valued.v (ℓ 0) ≤ 1)
    (h1 : Valued.v (ℓ 1) ≤ 1) :
    radicalDifference W g (z + adeleSingleAt ℚ v (ℓ 0)) (y + adeleSingleAt ℚ v (ℓ 1)) = radicalDifference W g z y := by
  rw [radicalDifference_apply, radicalDifference_apply,
    mirabolicSeries_radicalP21_add_adeleSingleAt hWK ha hg z y ℓ h0 h1,
    dualMirabolicSeries_radicalP21_add_adeleSingleAt hWK ha hg z y ℓ h0 h1]

private theorem radicalDifference_add_adeleSingleAt_snd (hWK : IsCongruenceEquivariantAlong v a χ W) (ha : 1 ≤ a)
    {g : AdelicGL 3 (𝓞 ℚ) ℚ} (hg : componentAt3 (𝓞 ℚ) ℚ v g ∈ converseCongruenceSet3 v a)
    {t : v.adicCompletion ℚ} (ht : Valued.v t ≤ 1) (z y : AdeleRing (𝓞 ℚ) ℚ) :
    radicalDifference W g z (y + adeleSingleAt ℚ v t) = radicalDifference W g z y := by
  have h := radicalDifference_add_adeleSingleAt hWK ha hg z y ![0, t] (by simp) (by simpa using ht)
  simpa using h

private theorem radicalDifference_add_adeleSingleAt_fst (hWK : IsCongruenceEquivariantAlong v a χ W) (ha : 1 ≤ a)
    {g : AdelicGL 3 (𝓞 ℚ) ℚ} (hg : componentAt3 (𝓞 ℚ) ℚ v g ∈ converseCongruenceSet3 v a)
    {t : v.adicCompletion ℚ} (ht : Valued.v t ≤ 1) (z y : AdeleRing (𝓞 ℚ) ℚ) :
    radicalDifference W g (z + adeleSingleAt ℚ v t) y = radicalDifference W g z y := by
  have h := radicalDifference_add_adeleSingleAt hWK ha hg z y ![t, 0] (by simpa using ht) (by simp)
  simpa using h
end
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_mirabolicSeries_eq_dual_of_radicalCoefficient_eq.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_mirabolicSeries_eq_dual_of_radicalCoefficient_eq.LanglandsTunnell.CubicInduction"
end LanglandsTunnell.CubicInduction
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_mirabolicSeries_eq_dual_of_radicalCoefficient_eq.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_mirabolicSeries_eq_dual_of_radicalCoefficient_eq.LanglandsTunnell.CubicInduction"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_mirabolicSeries_eq_dual_of_radicalCoefficient_eq.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_mirabolicSeries_eq_dual_of_radicalCoefficient_eq.LanglandsTunnell.CubicInduction"

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "Converse.IsAdmissibleTwist TateLocal.addCharLevel TateLocal.localBorel TateLocal.borelSpace_localBorel TateLocal.integersPositiveCompacts TateLocal.coe_integersPositiveCompacts TateLocal.selfDualHaarAt TateLocal.higherUnitsAt TateLocal.forall_eq_one_and_exists_ne_one_of_addCharLevel"
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "matrixFin_ext matrixAdele_ext localMatN mapMatrix_localMatN_self mapMatrix_localMatN_of_ne finMatN mapMatrix_arch_finMatN mapMatrix_fin_finMatN localToAdelic3 converseCongruenceSet3 HasVanishingUnipotentIntegralAlong IsCongruenceEquivariantAlong lowerUnipotent21 longWeyl3 longWeyl3_coe dualWhittakerFn3 dualWhittakerFn3_apply weylPrime3 weylPrime3_coe weylPrime3_mul_self transposeInv3_weylPrime3 weylPrime3_mul_transposeInv3_radicalP21_mul_weylPrime3 IsGL3PsiWhittakerFn transposeInv3 IsCuspidalAlongP21 psiLoc mirabolicTranslate AdelicGL globalPointsGL centralScalarGL upperUnipotent3 upperUnipotent3_coe upperUnipotent3_zero radicalP21 radicalP21_zero radicalP21_coe radicalP21_add embedMat2 iotaGL coe_iotaGL iota MirabolicIndex mirabolicRep mirabolicRep_spec mirabolic_mk_unipotent_mul localMaximalCompact3 componentAtN archComponentN componentAt3 archComponent3 LocalGL3 cosetSum IsCosetEigenfunction IsRightInvariant diagUnitGL2 diagHom diagHom_apply isCuspidalAlongP21_mirabolicSeries"
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"
section
open IsDedekindDomain NumberField

variable {v : HeightOneSpectrum (𝓞 ℚ)}

private noncomputable def mixUnit (X : LocalGL3 v) : v.adicCompletion ℚ :=
  ((X⁻¹ : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 1 1 *
    (X : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 2 2

private noncomputable def mixShift (X : LocalGL3 v) : v.adicCompletion ℚ :=
  ((X⁻¹ : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 0 1 *
    (X : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 2 2

private noncomputable def unipotentCorrection (X : LocalGL3 v) (t : v.adicCompletion ℚ) : LocalGL3 v :=
  (X * upperUnipotent3 0 (t * mixUnit X) (t * mixShift X))⁻¹ * (upperUnipotent3 0 t 0 * X)

private abbrev Mat (v : HeightOneSpectrum (𝓞 ℚ)) := Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)

section Helpers

private theorem exp_mono {a b : ℤ} (h : a ≤ b) : WithZero.exp a ≤ WithZero.exp b :=
  WithZero.exp_le_exp.mpr h

private theorem exp_neg_lt_one {n : ℤ} (hn : 0 < n) : WithZero.exp (-n) < 1 := by
  rw [← WithZero.exp_zero]
  exact WithZero.exp_lt_exp.mpr (by omega)

private theorem vle_one_exp {x : v.adicCompletion ℚ} (hx : Valued.v x ≤ 1) : Valued.v x ≤ WithZero.exp 0 := by
  rwa [WithZero.exp_zero]

private theorem vone : Valued.v (1 : v.adicCompletion ℚ) ≤ WithZero.exp 0 := by
  rw [map_one, WithZero.exp_zero]

private theorem vle_add {x y : v.adicCompletion ℚ} {C : WithZero (Multiplicative ℤ)} (hx : Valued.v x ≤ C)
    (hy : Valued.v y ≤ C) : Valued.v (x + y) ≤ C :=
  (Valuation.map_add _ _ _).trans (max_le hx hy)

private theorem vle_sub {x y : v.adicCompletion ℚ} {C : WithZero (Multiplicative ℤ)} (hx : Valued.v x ≤ C)
    (hy : Valued.v y ≤ C) : Valued.v (x - y) ≤ C :=
  (Valuation.map_sub _ _ _).trans (max_le hx hy)

private theorem vle_neg {x : v.adicCompletion ℚ} {C : WithZero (Multiplicative ℤ)} (hx : Valued.v x ≤ C) :
    Valued.v (-x) ≤ C := by
  rwa [Valuation.map_neg]

private theorem vle_mul_exp {x y : v.adicCompletion ℚ} {a b : ℤ} (hx : Valued.v x ≤ WithZero.exp a)
    (hy : Valued.v y ≤ WithZero.exp b) : Valued.v (x * y) ≤ WithZero.exp (a + b) := by
  rw [map_mul, WithZero.exp_add]
  exact mul_le_mul' hx hy

private theorem vone_apply (i j : Fin 3) :
    Valued.v ((1 : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j) ≤ WithZero.exp 0 := by
  by_cases hij : i = j
  · subst hij
    rw [Matrix.one_apply_eq]
    exact vone
  · rw [Matrix.one_apply_ne hij, map_zero]
    exact zero_le'

private theorem valued_eq_one_of_add_add_eq_one {x y z : v.adicCompletion ℚ} (hx : Valued.v x < 1)
    (hy : Valued.v y < 1) (h : x + y + z = 1) : Valued.v z = 1 := by
  have hz : z = 1 - (x + y) := by linear_combination h
  rw [hz]
  exact Valuation.map_one_sub_of_lt _ (Valuation.map_add_lt _ hx hy)

private theorem eq_one_of_mul_eq_one_of_le {a b : WithZero (Multiplicative ℤ)} (ha : a ≤ 1) (hb : b ≤ 1)
    (hab : a * b = 1) : b = 1 := by
  have hb0 : b ≠ 0 := by
    rintro rfl
    simp at hab
  have hinv : a = b⁻¹ := eq_inv_of_mul_eq_one_left hab
  refine le_antisymm hb ((inv_le_one₀ (zero_lt_iff.mpr hb0)).mp ?_)
  rw [← hinv]
  exact ha

end Helpers
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_mirabolicSeries_eq_dual_of_radicalCoefficient_eq.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_mirabolicSeries_eq_dual_of_radicalCoefficient_eq.LanglandsTunnell.CubicInduction"

section Matrices

variable (X : LocalGL3 v)

private theorem coeInv_mul_coe : ((X⁻¹ : LocalGL3 v) : Mat v) * (X : Mat v) = 1 := by
  rw [← Units.val_mul, inv_mul_cancel, Units.val_one]

private theorem coe_mul_coeInv : (X : Mat v) * ((X⁻¹ : LocalGL3 v) : Mat v) = 1 := by
  rw [← Units.val_mul, mul_inv_cancel, Units.val_one]

private theorem coeInv_mul_coe_apply (i j : Fin 3) :
    ((X⁻¹ : LocalGL3 v) : Mat v) i 0 * (X : Mat v) 0 j + ((X⁻¹ : LocalGL3 v) : Mat v) i 1 * (X : Mat v) 1 j +
      ((X⁻¹ : LocalGL3 v) : Mat v) i 2 * (X : Mat v) 2 j = (1 : Mat v) i j := by
  have h := congrFun (congrFun (coeInv_mul_coe X) i) j
  rwa [Matrix.mul_apply, Fin.sum_univ_three] at h

private theorem coe_mul_coeInv_apply (i j : Fin 3) :
    (X : Mat v) i 0 * ((X⁻¹ : LocalGL3 v) : Mat v) 0 j + (X : Mat v) i 1 * ((X⁻¹ : LocalGL3 v) : Mat v) 1 j +
      (X : Mat v) i 2 * ((X⁻¹ : LocalGL3 v) : Mat v) 2 j = (1 : Mat v) i j := by
  have h := congrFun (congrFun (coe_mul_coeInv X) i) j
  rwa [Matrix.mul_apply, Fin.sum_univ_three] at h

private theorem conj_apply (t : v.adicCompletion ℚ) (i j : Fin 3) :
    (((X⁻¹ : LocalGL3 v) : Mat v) * (upperUnipotent3 0 t 0 : LocalGL3 v) * (X : Mat v)) i j =
      (1 : Mat v) i j + t * ((X⁻¹ : LocalGL3 v) : Mat v) i 1 * (X : Mat v) 2 j := by
  have h := coeInv_mul_coe_apply X i j
  simp only [Matrix.mul_apply, Fin.sum_univ_three, upperUnipotent3_coe, Matrix.of_apply, Matrix.cons_val',
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_fin_one,
    Matrix.empty_val', Matrix.head_cons, Matrix.tail_cons, Matrix.head_fin_const]
  linear_combination h

private theorem upperUnipotent3_zero_inv (y z : v.adicCompletion ℚ) :
    (upperUnipotent3 0 y z : LocalGL3 v)⁻¹ = upperUnipotent3 0 (-y) (-z) := by
  refine inv_eq_of_mul_eq_one_right ?_
  ext i j
  rw [Units.val_mul, upperUnipotent3_coe, upperUnipotent3_coe, Units.val_one]
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]

private theorem det_upperUnipotent3_zero (y z : v.adicCompletion ℚ) :
    ((upperUnipotent3 0 y z : LocalGL3 v) : Mat v).det = 1 := by
  rw [upperUnipotent3_coe]
  simp [Matrix.det_fin_three]

private theorem unipotentCorrection_coe (t : v.adicCompletion ℚ) :
    (unipotentCorrection X t : Mat v) =
      ((upperUnipotent3 0 (-(t * mixUnit X)) (-(t * mixShift X)) : LocalGL3 v) : Mat v) *
        (((X⁻¹ : LocalGL3 v) : Mat v) * (upperUnipotent3 0 t 0 : LocalGL3 v) * (X : Mat v)) := by
  rw [unipotentCorrection, mul_inv_rev, upperUnipotent3_zero_inv, Units.val_mul, Units.val_mul, Units.val_mul]
  simp only [Matrix.mul_assoc]

private theorem unipotentCorrection_apply_two (t : v.adicCompletion ℚ) (j : Fin 3) :
    (unipotentCorrection X t : Mat v) 2 j =
      (1 : Mat v) 2 j + t * ((X⁻¹ : LocalGL3 v) : Mat v) 2 1 * (X : Mat v) 2 j := by
  rw [unipotentCorrection_coe, Matrix.mul_apply, Fin.sum_univ_three, conj_apply, conj_apply, conj_apply,
    upperUnipotent3_coe]
  simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_fin_one, Matrix.empty_val', Matrix.head_cons, Matrix.tail_cons, Matrix.head_fin_const]
  ring

private theorem unipotentCorrection_apply_zero (t : v.adicCompletion ℚ) (j : Fin 3) :
    (unipotentCorrection X t : Mat v) 0 j =
      (1 : Mat v) 0 j + t * ((X⁻¹ : LocalGL3 v) : Mat v) 0 1 * (X : Mat v) 2 j -
        t * mixShift X * ((1 : Mat v) 2 j + t * ((X⁻¹ : LocalGL3 v) : Mat v) 2 1 * (X : Mat v) 2 j) := by
  rw [unipotentCorrection_coe, Matrix.mul_apply, Fin.sum_univ_three, conj_apply, conj_apply, conj_apply,
    upperUnipotent3_coe]
  simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_fin_one, Matrix.empty_val', Matrix.head_cons, Matrix.tail_cons, Matrix.head_fin_const]
  ring

private theorem unipotentCorrection_apply_one (t : v.adicCompletion ℚ) (j : Fin 3) :
    (unipotentCorrection X t : Mat v) 1 j =
      (1 : Mat v) 1 j + t * ((X⁻¹ : LocalGL3 v) : Mat v) 1 1 * (X : Mat v) 2 j -
        t * mixUnit X * ((1 : Mat v) 2 j + t * ((X⁻¹ : LocalGL3 v) : Mat v) 2 1 * (X : Mat v) 2 j) := by
  rw [unipotentCorrection_coe, Matrix.mul_apply, Fin.sum_univ_three, conj_apply, conj_apply, conj_apply,
    upperUnipotent3_coe]
  simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_fin_one, Matrix.empty_val', Matrix.head_cons, Matrix.tail_cons, Matrix.head_fin_const]
  ring

private theorem unipotentCorrection_apply_one_two (t : v.adicCompletion ℚ) :
    (unipotentCorrection X t : Mat v) 1 2 =
      -(t * t * mixUnit X * (((X⁻¹ : LocalGL3 v) : Mat v) 2 1 * (X : Mat v) 2 2)) := by
  rw [unipotentCorrection_apply_one, Matrix.one_apply_ne (by decide), Matrix.one_apply_eq, mixUnit]
  ring

private theorem valued_det_unipotentCorrection (t : v.adicCompletion ℚ) :
    Valued.v (unipotentCorrection X t : Mat v).det = 1 := by
  rw [unipotentCorrection_coe, Matrix.det_mul, Matrix.det_mul, Matrix.det_mul, det_upperUnipotent3_zero,
    det_upperUnipotent3_zero, one_mul, mul_one, ← Matrix.det_mul, coeInv_mul_coe, Matrix.det_one, map_one]

private theorem mem_localMaximalCompact3_of_forall_le {k : LocalGL3 v}
    (hk : ∀ i j, Valued.v ((k : Mat v) i j) ≤ 1) (hdet : Valued.v (k : Mat v).det = 1) :
    k ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v := by
  refine ⟨hk, fun i j => ?_⟩
  rw [Matrix.GeneralLinearGroup.coe_inv, Matrix.inv_def, Matrix.smul_apply, smul_eq_mul, map_mul,
    Ring.inverse_eq_inv, map_inv₀, hdet, inv_one, one_mul, Matrix.adjugate_apply]
  refine valued_det_le_one_of_forall_le fun i' j' => ?_
  rw [Matrix.updateRow_apply]
  split_ifs
  · by_cases hji : j' = i
    · rw [hji, Pi.single_eq_same, map_one]
    · rw [Pi.single_eq_of_ne hji, map_zero]
      exact zero_le'
  · exact hk i' j'

end Matrices
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_mirabolicSeries_eq_dual_of_radicalCoefficient_eq.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_mirabolicSeries_eq_dual_of_radicalCoefficient_eq.LanglandsTunnell.CubicInduction"

private theorem upperUnipotent3_mul_eq_mul_unipotentCorrection (X : LocalGL3 v) (t : v.adicCompletion ℚ) :
    upperUnipotent3 0 t 0 * X =
      X * upperUnipotent3 0 (t * mixUnit X) (t * mixShift X) * unipotentCorrection X t := by
  rw [unipotentCorrection, mul_inv_cancel_left]

private theorem valued_mixUnit_eq_one {a : ℕ} (ha : 1 ≤ a) {X : LocalGL3 v} (hX : X ∈ converseCongruenceSet3 v a) :
    Valued.v (mixUnit X) = 1 := by
  obtain ⟨hXK, hX01, hX20, hX21⟩ := hX
  obtain ⟨hA, hB⟩ :
    (∀ i j, Valued.v ((X : Mat v) i j) ≤ 1) ∧ ∀ i j, Valued.v (((X⁻¹ : LocalGL3 v) : Mat v) i j) ≤ 1 := hXK
  have ha1 : WithZero.exp (-(a : ℤ)) < 1 := exp_neg_lt_one (by omega)
  have ha2 : WithZero.exp (-(2 * (a : ℤ))) < 1 := exp_neg_lt_one (by omega)
  have h22 := coe_mul_coeInv_apply X 2 2
  rw [Matrix.one_apply_eq] at h22
  have hu22 : Valued.v ((X : Mat v) 2 2 * ((X⁻¹ : LocalGL3 v) : Mat v) 2 2) = 1 := by
    refine valued_eq_one_of_add_add_eq_one ?_ ?_ h22
    · rw [map_mul]
      exact (valued_mul_le_of_le_one_right hX20 (hB 0 2)).trans_lt ha1
    · rw [map_mul]
      exact (valued_mul_le_of_le_one_right hX21 (hB 1 2)).trans_lt ha2
  have hA22 : Valued.v ((X : Mat v) 2 2) = 1 :=
    eq_one_of_mul_eq_one_of_le (hB 2 2) (hA 2 2) (by rwa [map_mul, mul_comm] at hu22)
  have h11 := coeInv_mul_coe_apply X 1 1
  rw [Matrix.one_apply_eq] at h11
  have h11' : ((X⁻¹ : LocalGL3 v) : Mat v) 1 0 * (X : Mat v) 0 1 + ((X⁻¹ : LocalGL3 v) : Mat v) 1 2 * (X : Mat v) 2 1 +
      ((X⁻¹ : LocalGL3 v) : Mat v) 1 1 * (X : Mat v) 1 1 = 1 := by
    linear_combination h11
  have hu11 : Valued.v (((X⁻¹ : LocalGL3 v) : Mat v) 1 1 * (X : Mat v) 1 1) = 1 := by
    refine valued_eq_one_of_add_add_eq_one ?_ ?_ h11'
    · rw [map_mul]
      exact (valued_mul_le_of_le_one_left (hB 1 0) hX01).trans_lt ha1
    · rw [map_mul]
      exact (valued_mul_le_of_le_one_left (hB 1 2) hX21).trans_lt ha2
  have hB11 : Valued.v (((X⁻¹ : LocalGL3 v) : Mat v) 1 1) = 1 :=
    eq_one_of_mul_eq_one_of_le (hA 1 1) (hB 1 1) (by rwa [map_mul, mul_comm] at hu11)
  rw [mixUnit, map_mul, hB11, hA22, one_mul]

private theorem valued_mixShift_le {a : ℕ} {X : LocalGL3 v} (hX : X ∈ converseCongruenceSet3 v a) :
    Valued.v (mixShift X) ≤ WithZero.exp (-(a : ℤ)) := by
  obtain ⟨-, hB01, -, -⟩ := inv_mem_converseCongruenceSet3 hX
  obtain ⟨hXK, -, -, -⟩ := hX
  obtain ⟨hA, -⟩ :
    (∀ i j, Valued.v ((X : Mat v) i j) ≤ 1) ∧ ∀ i j, Valued.v (((X⁻¹ : LocalGL3 v) : Mat v) i j) ≤ 1 := hXK
  rw [mixShift, map_mul]
  exact valued_mul_le_of_le_one_right hB01 (hA 2 2)

private theorem unipotentCorrection_mem_converseCongruenceSet3 {a : ℕ} (ha : 1 ≤ a) {X : LocalGL3 v}
    (hX : X ∈ converseCongruenceSet3 v a) {t : v.adicCompletion ℚ} (ht : Valued.v t ≤ WithZero.exp (1 : ℤ)) :
    unipotentCorrection X t ∈ converseCongruenceSet3 v a := by
  have hm : Valued.v (mixUnit X) ≤ WithZero.exp 0 := by rw [valued_mixUnit_eq_one ha hX, WithZero.exp_zero]
  have hz : Valued.v (mixShift X) ≤ WithZero.exp (-(a : ℤ)) := valued_mixShift_le hX
  obtain ⟨-, hB01, hB20, hB21⟩ := inv_mem_converseCongruenceSet3 hX
  obtain ⟨hXK, hX01, hX20, hX21⟩ := hX
  obtain ⟨hA, hB⟩ :
    (∀ i j, Valued.v ((X : Mat v) i j) ≤ 1) ∧ ∀ i j, Valued.v (((X⁻¹ : LocalGL3 v) : Mat v) i j) ≤ 1 := hXK
  have hA0 : ∀ i j, Valued.v ((X : Mat v) i j) ≤ WithZero.exp 0 := fun i j => vle_one_exp (hA i j)
  have hB0 : ∀ i j, Valued.v (((X⁻¹ : LocalGL3 v) : Mat v) i j) ≤ WithZero.exp 0 := fun i j => vle_one_exp (hB i j)

  have hrow : ∀ j, Valued.v (t * ((X⁻¹ : LocalGL3 v) : Mat v) 2 1 * (X : Mat v) 2 j)
      ≤ WithZero.exp (1 - 2 * (a : ℤ)) :=
    fun j => (vle_mul_exp (vle_mul_exp ht hB21) (hA0 2 j)).trans (exp_mono (by omega))
  have hrow0 : Valued.v (t * ((X⁻¹ : LocalGL3 v) : Mat v) 2 1 * (X : Mat v) 2 0) ≤ WithZero.exp (1 - 3 * (a : ℤ)) :=
    (vle_mul_exp (vle_mul_exp ht hB21) hX20).trans (exp_mono (by omega))
  have hrow1 : Valued.v (t * ((X⁻¹ : LocalGL3 v) : Mat v) 2 1 * (X : Mat v) 2 1) ≤ WithZero.exp (1 - 4 * (a : ℤ)) :=
    (vle_mul_exp (vle_mul_exp ht hB21) hX21).trans (exp_mono (by omega))
  have hfac : ∀ j, Valued.v ((1 : Mat v) 2 j + t * ((X⁻¹ : LocalGL3 v) : Mat v) 2 1 * (X : Mat v) 2 j) ≤
      WithZero.exp 0 := fun j => vle_add (vone_apply 2 j) ((hrow j).trans (exp_mono (by omega)))

  have hint : ∀ i j, Valued.v ((unipotentCorrection X t : Mat v) i j) ≤ 1 := by
    intro i j
    rw [← WithZero.exp_zero]
    fin_cases i
    · rw [Fin.zero_eta, unipotentCorrection_apply_zero]
      exact vle_sub
        (vle_add (vone_apply 0 j) ((vle_mul_exp (vle_mul_exp ht hB01) (hA0 2 j)).trans (exp_mono (by omega))))
        ((vle_mul_exp (vle_mul_exp ht hz) (hfac j)).trans (exp_mono (by omega)))
    · fin_cases j
      · rw [Fin.mk_one, Fin.zero_eta, unipotentCorrection_apply_one,
          Matrix.one_apply_ne (show (2 : Fin 3) ≠ 0 by decide), zero_add]
        exact vle_sub
          (vle_add (vone_apply 1 0) ((vle_mul_exp (vle_mul_exp ht (hB0 1 1)) hX20).trans (exp_mono (by omega))))
          ((vle_mul_exp (vle_mul_exp ht hm) hrow0).trans (exp_mono (by omega)))
      · rw [Fin.mk_one, unipotentCorrection_apply_one, Matrix.one_apply_ne (show (2 : Fin 3) ≠ 1 by decide),
          zero_add]
        exact vle_sub
          (vle_add (vone_apply 1 1) ((vle_mul_exp (vle_mul_exp ht (hB0 1 1)) hX21).trans (exp_mono (by omega))))
          ((vle_mul_exp (vle_mul_exp ht hm) hrow1).trans (exp_mono (by omega)))
      · show Valued.v ((unipotentCorrection X t : Mat v) 1 2) ≤ WithZero.exp 0
        rw [unipotentCorrection_apply_one_two]
        exact vle_neg ((vle_mul_exp (vle_mul_exp (vle_mul_exp ht ht) hm) (vle_mul_exp hB21 (hA0 2 2))).trans
          (exp_mono (by omega)))
    · show Valued.v ((unipotentCorrection X t : Mat v) 2 j) ≤ WithZero.exp 0
      rw [unipotentCorrection_apply_two]
      exact hfac j
  refine ⟨mem_localMaximalCompact3_of_forall_le hint (valued_det_unipotentCorrection X t), ?_, ?_, ?_⟩
  · rw [unipotentCorrection_apply_zero, Matrix.one_apply_ne (show (0 : Fin 3) ≠ 1 by decide),
      Matrix.one_apply_ne (show (2 : Fin 3) ≠ 1 by decide), zero_add, zero_add]
    exact vle_sub ((vle_mul_exp (vle_mul_exp ht hB01) hX21).trans (exp_mono (by omega)))
      ((vle_mul_exp (vle_mul_exp ht hz) hrow1).trans (exp_mono (by omega)))
  · rw [unipotentCorrection_apply_two, Matrix.one_apply_ne (show (2 : Fin 3) ≠ 0 by decide), zero_add]
    exact hrow0.trans (exp_mono (by omega))
  · rw [unipotentCorrection_apply_two, Matrix.one_apply_ne (show (2 : Fin 3) ≠ 1 by decide), zero_add]
    exact hrow1.trans (exp_mono (by omega))

private theorem valued_unipotentCorrection_sub_one_le {a : ℕ} (ha : 1 ≤ a) {X : LocalGL3 v}
    (hX : X ∈ converseCongruenceSet3 v a) {t : v.adicCompletion ℚ} (ht : Valued.v t ≤ WithZero.exp (1 : ℤ)) :
    Valued.v ((unipotentCorrection X t : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 2 2 - 1) ≤
      WithZero.exp (-((2 * a - 1 : ℕ) : ℤ)) := by
  obtain ⟨-, -, -, hB21⟩ := inv_mem_converseCongruenceSet3 hX
  obtain ⟨hXK, -, -, -⟩ := hX
  obtain ⟨hA, -⟩ :
    (∀ i j, Valued.v ((X : Mat v) i j) ≤ 1) ∧ ∀ i j, Valued.v (((X⁻¹ : LocalGL3 v) : Mat v) i j) ≤ 1 := hXK
  rw [unipotentCorrection_apply_two, Matrix.one_apply_eq, add_sub_cancel_left]
  exact (vle_mul_exp (vle_mul_exp ht hB21) (vle_one_exp (hA 2 2))).trans (exp_mono (by omega))

private theorem upperUnipotent3_mem_converseCongruenceSet3 (n : ℕ) {y z : v.adicCompletion ℚ} (hy : Valued.v y ≤ 1)
    (hz : Valued.v z ≤ 1) : upperUnipotent3 0 y z ∈ converseCongruenceSet3 v n := by
  refine ⟨⟨?_, ?_⟩, ?_, ?_, ?_⟩
  · intro i j
    rw [upperUnipotent3_coe]
    fin_cases i <;> fin_cases j <;> simp [hy, hz]
  · intro i j
    rw [upperUnipotent3_zero_inv, upperUnipotent3_coe]
    fin_cases i <;> fin_cases j <;> simp [Valuation.map_neg, hy, hz]
  · rw [upperUnipotent3_coe]
    simp
  · rw [upperUnipotent3_coe]
    simp
  · rw [upperUnipotent3_coe]
    simp
end
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_mirabolicSeries_eq_dual_of_radicalCoefficient_eq.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_mirabolicSeries_eq_dual_of_radicalCoefficient_eq.LanglandsTunnell.CubicInduction"
end LanglandsTunnell.CubicInduction
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_mirabolicSeries_eq_dual_of_radicalCoefficient_eq.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_mirabolicSeries_eq_dual_of_radicalCoefficient_eq.LanglandsTunnell.CubicInduction"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_mirabolicSeries_eq_dual_of_radicalCoefficient_eq.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_mirabolicSeries_eq_dual_of_radicalCoefficient_eq.LanglandsTunnell.CubicInduction"

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "Converse.IsAdmissibleTwist TateLocal.addCharLevel TateLocal.localBorel TateLocal.borelSpace_localBorel TateLocal.integersPositiveCompacts TateLocal.coe_integersPositiveCompacts TateLocal.selfDualHaarAt TateLocal.higherUnitsAt TateLocal.forall_eq_one_and_exists_ne_one_of_addCharLevel"
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "matrixFin_ext matrixAdele_ext localMatN mapMatrix_localMatN_self mapMatrix_localMatN_of_ne finMatN mapMatrix_arch_finMatN mapMatrix_fin_finMatN localToAdelic3 converseCongruenceSet3 HasVanishingUnipotentIntegralAlong IsCongruenceEquivariantAlong lowerUnipotent21 longWeyl3 longWeyl3_coe dualWhittakerFn3 dualWhittakerFn3_apply weylPrime3 weylPrime3_coe weylPrime3_mul_self transposeInv3_weylPrime3 weylPrime3_mul_transposeInv3_radicalP21_mul_weylPrime3 IsGL3PsiWhittakerFn transposeInv3 IsCuspidalAlongP21 psiLoc mirabolicTranslate AdelicGL globalPointsGL centralScalarGL upperUnipotent3 upperUnipotent3_coe upperUnipotent3_zero radicalP21 radicalP21_zero radicalP21_coe radicalP21_add embedMat2 iotaGL coe_iotaGL iota MirabolicIndex mirabolicRep mirabolicRep_spec mirabolic_mk_unipotent_mul localMaximalCompact3 componentAtN archComponentN componentAt3 archComponent3 LocalGL3 cosetSum IsCosetEigenfunction IsRightInvariant diagUnitGL2 diagHom diagHom_apply isCuspidalAlongP21_mirabolicSeries"
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"
section
open IsDedekindDomain NumberField MeasureTheory
open scoped NNReal ENNReal

variable {v : HeightOneSpectrum (𝓞 ℚ)}

private theorem sum_eq_zero_of_setIntegral_eq_zero_core [MeasurableSpace (v.adicCompletion ℚ)]
    [BorelSpace (v.adicCompletion ℚ)] (μ : Measure (v.adicCompletion ℚ)) (K : Set (v.adicCompletion ℚ))
    (hKmem : ∀ x : v.adicCompletion ℚ, x ∈ K ↔ Valued.v x ≤ 1) (hKopen : IsOpen K)
    (hKtrans : ∀ t : v.adicCompletion ℚ, μ ((fun x => x - t) ⁻¹' K) = μ K) (hKfin : μ K ≠ ⊤)
    (hK0 : μ.real K ≠ 0) (f : v.adicCompletion ℚ → ℂ)
    (hf : ∀ x o : v.adicCompletion ℚ, Valued.v o ≤ 1 → f (x + o) = f x)
    (hint : (∫ x in {x : v.adicCompletion ℚ | Valued.v x ≤ WithZero.exp (1 : ℤ)}, f x ∂μ) = 0)
    (R : Finset (v.adicCompletion ℚ)) (hR : ∀ t ∈ R, Valued.v t ≤ WithZero.exp (1 : ℤ))
    (hcov : ∀ x : v.adicCompletion ℚ, Valued.v x ≤ WithZero.exp (1 : ℤ) → ∃ t ∈ R, Valued.v (x - t) ≤ 1)
    (hsep : ∀ t ∈ R, ∀ t' ∈ R, Valued.v (t - t') ≤ 1 → t = t') :
    ∑ t ∈ R, f t = 0 := by
  classical

  obtain ⟨ball, hball⟩ : ∃ ball : v.adicCompletion ℚ → Set (v.adicCompletion ℚ),
      ∀ t, ball t = (fun x => x - t) ⁻¹' K := ⟨_, fun _ => rfl⟩
  have hball_mem : ∀ t x, x ∈ ball t ↔ Valued.v (x - t) ≤ 1 := fun t x => by
    rw [hball, Set.mem_preimage]; exact hKmem (x - t)
  have hball_meas : ∀ t, MeasurableSet (ball t) := fun t => by
    rw [hball]
    first
      | exact (hKopen.preimage (continuous_id.sub continuous_const)).measurableSet
      | exact (hKopen.preimage (continuous_sub_right t)).measurableSet
      | exact hKopen.measurableSet.preimage (measurable_sub_const t)
  have hball_measure : ∀ t, μ (ball t) = μ K := fun t => by rw [hball]; exact hKtrans t
  have hone : (1 : WithZero (Multiplicative ℤ)) ≤ WithZero.exp (1 : ℤ) := by
    first
      | exact (WithZero.exp_le_exp.mpr (zero_le_one : (0 : ℤ) ≤ 1) :
          WithZero.exp (0 : ℤ) ≤ WithZero.exp (1 : ℤ))
      | (rw [← WithZero.exp_zero]; exact WithZero.exp_le_exp.mpr zero_le_one)
      | simp

  have hS : {x : v.adicCompletion ℚ | Valued.v x ≤ WithZero.exp (1 : ℤ)} = ⋃ t ∈ R, ball t := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, exists_prop]
    constructor
    · intro hx
      obtain ⟨t, ht, hxt⟩ := hcov x hx
      exact ⟨t, ht, (hball_mem t x).mpr hxt⟩
    · rintro ⟨t, ht, hxt⟩
      rw [hball_mem] at hxt
      calc Valued.v x = Valued.v ((x - t) + t) := by rw [sub_add_cancel]
        _ ≤ max (Valued.v (x - t)) (Valued.v t) := Valuation.map_add _ _ _
        _ ≤ WithZero.exp (1 : ℤ) := max_le (hxt.trans hone) (hR t ht)
  have hdisj : Set.Pairwise (↑R : Set (v.adicCompletion ℚ)) (Function.onFun Disjoint ball) := by
    intro t ht t' ht' hne
    show Disjoint (ball t) (ball t')
    refine Set.disjoint_left.mpr fun x hx hx' => hne (hsep t ht t' ht' ?_)
    rw [hball_mem] at hx hx'
    calc Valued.v (t - t') = Valued.v ((t - x) + (x - t')) := by rw [sub_add_sub_cancel]
      _ ≤ max (Valued.v (t - x)) (Valued.v (x - t')) := Valuation.map_add _ _ _
      _ ≤ 1 := max_le (by rw [Valuation.map_sub_swap]; exact hx) hx'

  have hconst : ∀ t, Set.EqOn f (fun _ => f t) (ball t) := fun t x hx => by
    rw [hball_mem] at hx
    calc f x = f (t + (x - t)) := by rw [add_sub_cancel]
      _ = f t := hf t (x - t) hx
  have hfin : ∀ t, μ (ball t) ≠ ⊤ := fun t => by rw [hball_measure]; exact hKfin
  have hintOn : ∀ t ∈ R, IntegrableOn f (ball t) μ := fun t _ => by
    first
      | exact (integrableOn_const (hs := hfin t)).congr_fun (hconst t).symm (hball_meas t)
      | exact (integrableOn_const (hs := hfin t) (hC := enorm_ne_top)).congr_fun (hconst t).symm (hball_meas t)
  have hvol : ∀ t, μ.real (ball t) = μ.real K := fun t => by
    rw [measureReal_def, measureReal_def, hball_measure]

  have heach : ∀ t ∈ R, (∫ x in ball t, f x ∂μ) = μ.real K • f t := fun t _ => by
    first
      | rw [setIntegral_congr_fun (hball_meas t) (hconst t)]
      | rw [setIntegral_congr_fun₀ (hball_meas t).nullMeasurableSet (hconst t)]
    rw [← hvol t]
    exact setIntegral_const (f t)
  have hsum₀ : ∑ t ∈ R, (∫ x in ball t, f x ∂μ) = 0 :=
    (integral_biUnion_finset R (fun t _ => hball_meas t) hdisj hintOn).symm.trans (by
      first
        | (rw [← hS]; exact hint)
        | exact hS ▸ hint)
  have hsum : μ.real K • ∑ t ∈ R, f t = 0 :=
    (Finset.smul_sum (r := μ.real K) (f := f) (s := R)).trans
      ((Finset.sum_congr rfl fun t ht => (heach t ht).symm).trans hsum₀)
  first
    | exact (smul_eq_zero.mp hsum).resolve_left hK0
    | exact (mul_eq_zero.mp ((Complex.real_smul (x := μ.real K)).symm.trans hsum)).resolve_left
        (Complex.ofReal_ne_zero.mpr hK0)

private theorem sum_eq_zero_of_setIntegral_eq_zero_of_forall_add_eq (f : v.adicCompletion ℚ → ℂ)
    (hf : ∀ x o : v.adicCompletion ℚ, Valued.v o ≤ 1 → f (x + o) = f x)
    (hint : (letI := LanglandsTunnell.TateLocal.localBorel ℚ v;
      (∫ x in {x : v.adicCompletion ℚ | Valued.v x ≤ WithZero.exp (1 : ℤ)}, f x
        ∂(LanglandsTunnell.TateLocal.selfDualHaarAt ℚ v)) = 0))
    (R : Finset (v.adicCompletion ℚ)) (hR : ∀ t ∈ R, Valued.v t ≤ WithZero.exp (1 : ℤ))
    (hcov : ∀ x : v.adicCompletion ℚ, Valued.v x ≤ WithZero.exp (1 : ℤ) → ∃ t ∈ R, Valued.v (x - t) ≤ 1)
    (hsep : ∀ t ∈ R, ∀ t' ∈ R, Valued.v (t - t') ≤ 1 → t = t') :
    ∑ t ∈ R, f t = 0 := by
  classical
  letI := LanglandsTunnell.TateLocal.localBorel ℚ v
  haveI : BorelSpace (v.adicCompletion ℚ) := LanglandsTunnell.TateLocal.borelSpace_localBorel ℚ v

  obtain ⟨c, hc, hμ⟩ : ∃ c : ℝ≥0, 0 < c ∧ LanglandsTunnell.TateLocal.selfDualHaarAt ℚ v =
      c • Measure.addHaarMeasure (LanglandsTunnell.TateLocal.integersPositiveCompacts ℚ v) := by
    refine ⟨_, NNReal.rpow_pos ?_, rfl⟩
    exact_mod_cast Nat.pos_of_ne_zero (mt Ideal.absNorm_eq_zero_iff.mp v.ne_bot)
  have hint' : (∫ x in {x : v.adicCompletion ℚ | Valued.v x ≤ WithZero.exp (1 : ℤ)}, f x
      ∂(c • Measure.addHaarMeasure (LanglandsTunnell.TateLocal.integersPositiveCompacts ℚ v))) = 0 := by
    rw [← hμ]; exact hint

  have hKmem : ∀ x : v.adicCompletion ℚ,
      x ∈ (LanglandsTunnell.TateLocal.integersPositiveCompacts ℚ v : Set (v.adicCompletion ℚ)) ↔
        Valued.v x ≤ 1 := fun x => by
    rw [LanglandsTunnell.TateLocal.coe_integersPositiveCompacts]
    first
      | exact Iff.rfl
      | exact HeightOneSpectrum.mem_adicCompletionIntegers ℚ v
      | exact HeightOneSpectrum.mem_adicCompletionIntegers
      | exact SetLike.mem_coe.trans (HeightOneSpectrum.mem_adicCompletionIntegers ℚ v)
  have hKopen :
      IsOpen (LanglandsTunnell.TateLocal.integersPositiveCompacts ℚ v : Set (v.adicCompletion ℚ)) := by
    rw [LanglandsTunnell.TateLocal.coe_integersPositiveCompacts]
    exact Valued.isOpen_valuationSubring _
  have hKtrans : ∀ t : v.adicCompletion ℚ,
      (c • Measure.addHaarMeasure (LanglandsTunnell.TateLocal.integersPositiveCompacts ℚ v))
          ((fun x => x - t) ⁻¹'
            (LanglandsTunnell.TateLocal.integersPositiveCompacts ℚ v : Set (v.adicCompletion ℚ))) =
        (c • Measure.addHaarMeasure (LanglandsTunnell.TateLocal.integersPositiveCompacts ℚ v))
          (LanglandsTunnell.TateLocal.integersPositiveCompacts ℚ v : Set (v.adicCompletion ℚ)) := by
    intro t
    have hset : ((fun x => x - t) ⁻¹'
          (LanglandsTunnell.TateLocal.integersPositiveCompacts ℚ v : Set (v.adicCompletion ℚ))) =
        (fun x => -t + x) ⁻¹'
          (LanglandsTunnell.TateLocal.integersPositiveCompacts ℚ v : Set (v.adicCompletion ℚ)) := by
      ext x
      first
        | (rw [Set.mem_preimage, Set.mem_preimage, sub_eq_neg_add])
        | simp [sub_eq_neg_add]
    rw [hset]
    first
      | exact measure_preimage_add _ (-t) _
      | exact Measure.measure_preimage_add _ (-t) _
      | exact MeasureTheory.measure_preimage_add _ (-t) _
  have hvolK : (c • Measure.addHaarMeasure (LanglandsTunnell.TateLocal.integersPositiveCompacts ℚ v))
      (LanglandsTunnell.TateLocal.integersPositiveCompacts ℚ v : Set (v.adicCompletion ℚ)) = (c : ℝ≥0∞) := by
    rw [Measure.smul_apply, Measure.addHaarMeasure_self]
    first
      | exact ENNReal.smul_one c
      | (rw [ENNReal.smul_def, smul_eq_mul, mul_one])
      | simp
  have hKfin : (c • Measure.addHaarMeasure (LanglandsTunnell.TateLocal.integersPositiveCompacts ℚ v))
      (LanglandsTunnell.TateLocal.integersPositiveCompacts ℚ v : Set (v.adicCompletion ℚ)) ≠ ⊤ := by
    rw [hvolK]; exact ENNReal.coe_ne_top
  have hK0 : (c • Measure.addHaarMeasure (LanglandsTunnell.TateLocal.integersPositiveCompacts ℚ v)).real
      (LanglandsTunnell.TateLocal.integersPositiveCompacts ℚ v : Set (v.adicCompletion ℚ)) ≠ 0 := by
    rw [measureReal_def, hvolK, ENNReal.coe_toReal]
    first
      | exact_mod_cast hc.ne'
      | exact NNReal.coe_ne_zero.mpr hc.ne'
      | positivity
  exact sum_eq_zero_of_setIntegral_eq_zero_core _ _ hKmem hKopen hKtrans hKfin hK0 f hf hint' R hR hcov hsep
end
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_mirabolicSeries_eq_dual_of_radicalCoefficient_eq.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_mirabolicSeries_eq_dual_of_radicalCoefficient_eq.LanglandsTunnell.CubicInduction"
end LanglandsTunnell.CubicInduction
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_mirabolicSeries_eq_dual_of_radicalCoefficient_eq.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_mirabolicSeries_eq_dual_of_radicalCoefficient_eq.LanglandsTunnell.CubicInduction"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_mirabolicSeries_eq_dual_of_radicalCoefficient_eq.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_mirabolicSeries_eq_dual_of_radicalCoefficient_eq.LanglandsTunnell.CubicInduction"

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "Converse.IsAdmissibleTwist TateLocal.addCharLevel TateLocal.localBorel TateLocal.borelSpace_localBorel TateLocal.integersPositiveCompacts TateLocal.coe_integersPositiveCompacts TateLocal.selfDualHaarAt TateLocal.higherUnitsAt TateLocal.forall_eq_one_and_exists_ne_one_of_addCharLevel"
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "matrixFin_ext matrixAdele_ext localMatN mapMatrix_localMatN_self mapMatrix_localMatN_of_ne finMatN mapMatrix_arch_finMatN mapMatrix_fin_finMatN localToAdelic3 converseCongruenceSet3 HasVanishingUnipotentIntegralAlong IsCongruenceEquivariantAlong lowerUnipotent21 longWeyl3 longWeyl3_coe dualWhittakerFn3 dualWhittakerFn3_apply weylPrime3 weylPrime3_coe weylPrime3_mul_self transposeInv3_weylPrime3 weylPrime3_mul_transposeInv3_radicalP21_mul_weylPrime3 IsGL3PsiWhittakerFn transposeInv3 IsCuspidalAlongP21 psiLoc mirabolicTranslate AdelicGL globalPointsGL centralScalarGL upperUnipotent3 upperUnipotent3_coe upperUnipotent3_zero radicalP21 radicalP21_zero radicalP21_coe radicalP21_add embedMat2 iotaGL coe_iotaGL iota MirabolicIndex mirabolicRep mirabolicRep_spec mirabolic_mk_unipotent_mul localMaximalCompact3 componentAtN archComponentN componentAt3 archComponent3 LocalGL3 cosetSum IsCosetEigenfunction IsRightInvariant diagUnitGL2 diagHom diagHom_apply isCuspidalAlongP21_mirabolicSeries"
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"
section
open IsDedekindDomain NumberField NumberField.StandardAddChar MeasureTheory

variable {v : HeightOneSpectrum (𝓞 ℚ)}

section Algebra

variable {A : Type*} [CommRing A]

private theorem transposeInv3_mul_aux22 (g h : GL (Fin 3) A) :
    transposeInv3 (g * h) = transposeInv3 g * transposeInv3 h := by
  refine Units.ext ?_
  change Matrix.transpose ((((g * h)⁻¹ : GL (Fin 3) A)) : Matrix (Fin 3) (Fin 3) A) = _
  rw [_root_.mul_inv_rev, Units.val_mul, Matrix.transpose_mul]
  rfl

private theorem transposeInv3_transposeInv3_aux22 (g : GL (Fin 3) A) : transposeInv3 (transposeInv3 g) = g := by
  refine Units.ext ?_
  change Matrix.transpose ((((transposeInv3 g)⁻¹ : GL (Fin 3) A)) : Matrix (Fin 3) (Fin 3) A) = _
  have h : ((((transposeInv3 g)⁻¹ : GL (Fin 3) A)) : Matrix (Fin 3) (Fin 3) A) =
      Matrix.transpose ((g : GL (Fin 3) A) : Matrix (Fin 3) (Fin 3) A) := rfl
  rw [h, Matrix.transpose_transpose]

private theorem upperUnipotent3_zero_add_zero (x o : A) :
    (upperUnipotent3 0 (x + o) 0 : GL (Fin 3) A) = upperUnipotent3 0 x 0 * upperUnipotent3 0 o 0 := by
  ext i j
  rw [Units.val_mul, upperUnipotent3_coe, upperUnipotent3_coe, upperUnipotent3_coe]
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three, add_comm]

private theorem upperUnipotent3_zero_eq_mul (y z : A) :
    (upperUnipotent3 0 y z : GL (Fin 3) A) = upperUnipotent3 0 y 0 * upperUnipotent3 0 0 z := by
  ext i j
  rw [Units.val_mul, upperUnipotent3_coe, upperUnipotent3_coe, upperUnipotent3_coe]
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]

private theorem upperUnipotent3_apply_two_two (x y z : A) :
    ((upperUnipotent3 x y z : GL (Fin 3) A) : Matrix (Fin 3) (Fin 3) A) 2 2 = 1 := by
  rw [upperUnipotent3_coe]
  rfl

private theorem radicalP21_zero_left (s : A) : radicalP21 ![(0 : A), s] = upperUnipotent3 0 s 0 := by
  ext i j
  simp [radicalP21]

private theorem vecTwo_add_snd (z y s : A) : ![z, y + s] = ![z, y] + ![0, s] := by
  ext i
  fin_cases i <;> simp

end Algebra
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_mirabolicSeries_eq_dual_of_radicalCoefficient_eq.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_mirabolicSeries_eq_dual_of_radicalCoefficient_eq.LanglandsTunnell.CubicInduction"

section Local

variable {v : HeightOneSpectrum (𝓞 ℚ)}

private theorem ne_zero_of_valued_eq_one' {x : v.adicCompletion ℚ} (hx : Valued.v x = 1) : x ≠ 0 := by
  intro h
  rw [h, map_zero] at hx
  exact zero_ne_one hx

private theorem valued_zero_le_one : Valued.v (0 : v.adicCompletion ℚ) ≤ 1 := by
  rw [map_zero]
  exact zero_le'

private theorem image_mul_representatives {m : v.adicCompletion ℚ} (hm : Valued.v m = 1)
    (R : Finset (v.adicCompletion ℚ)) (hR : ∀ t ∈ R, Valued.v t ≤ WithZero.exp (1 : ℤ))
    (hcov : ∀ x : v.adicCompletion ℚ, Valued.v x ≤ WithZero.exp (1 : ℤ) → ∃ t ∈ R, Valued.v (x - t) ≤ 1)
    (hsep : ∀ t ∈ R, ∀ t' ∈ R, Valued.v (t - t') ≤ 1 → t = t') [DecidableEq (v.adicCompletion ℚ)] :
    (∀ s ∈ R.image (· * m), Valued.v s ≤ WithZero.exp (1 : ℤ)) ∧
      (∀ x : v.adicCompletion ℚ, Valued.v x ≤ WithZero.exp (1 : ℤ) →
        ∃ s ∈ R.image (· * m), Valued.v (x - s) ≤ 1) ∧
      ∀ s ∈ R.image (· * m), ∀ s' ∈ R.image (· * m), Valued.v (s - s') ≤ 1 → s = s' := by
  have hm0 : m ≠ 0 := ne_zero_of_valued_eq_one' hm
  refine ⟨fun s hs => ?_, fun x hx => ?_, fun s hs s' hs' hss' => ?_⟩
  · obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hs
    rw [map_mul, hm, mul_one]
    exact hR t ht
  · obtain ⟨t, ht, hxt⟩ := hcov (x * m⁻¹) (by rw [map_mul, map_inv₀, hm, inv_one, mul_one]; exact hx)
    refine ⟨t * m, Finset.mem_image.mpr ⟨t, ht, rfl⟩, ?_⟩
    have hx' : x - t * m = (x * m⁻¹ - t) * m := by field_simp
    rw [hx', map_mul, hm, mul_one]
    exact hxt
  · obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hs
    obtain ⟨t', ht', rfl⟩ := Finset.mem_image.mp hs'
    rw [← sub_mul, map_mul, hm, mul_one] at hss'
    rw [hsep t ht t' ht' hss']

end Local
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_mirabolicSeries_eq_dual_of_radicalCoefficient_eq.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_mirabolicSeries_eq_dual_of_radicalCoefficient_eq.LanglandsTunnell.CubicInduction"

section Average

variable {v : HeightOneSpectrum (𝓞 ℚ)}

private theorem sum_apply_mul_localToAdelic3_upperUnipotent3_eq_zero {a : ℕ} {χ : (v.adicCompletion ℚ)ˣ →* ℂˣ}
    {W : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ} (hWK : IsCongruenceEquivariantAlong v a χ W)
    (hWl : HasVanishingUnipotentIntegralAlong v W)
    (R : Finset (v.adicCompletion ℚ)) (hR : ∀ t ∈ R, Valued.v t ≤ WithZero.exp (1 : ℤ))
    (hcov : ∀ x : v.adicCompletion ℚ, Valued.v x ≤ WithZero.exp (1 : ℤ) → ∃ t ∈ R, Valued.v (x - t) ≤ 1)
    (hsep : ∀ t ∈ R, ∀ t' ∈ R, Valued.v (t - t') ≤ 1 → t = t') (h : AdelicGL 3 (𝓞 ℚ) ℚ) :
    ∑ t ∈ R, W (h * localToAdelic3 v (upperUnipotent3 0 t 0)) = 0 := by
  refine sum_eq_zero_of_setIntegral_eq_zero_of_forall_add_eq
    (fun x => W (h * localToAdelic3 v (upperUnipotent3 0 x 0))) (fun x o ho => ?_) (hWl h) R hR hcov hsep
  show W (h * localToAdelic3 v (upperUnipotent3 0 (x + o) 0)) = W (h * localToAdelic3 v (upperUnipotent3 0 x 0))
  rw [upperUnipotent3_zero_add_zero, map_mul, ← mul_assoc,
    hWK (upperUnipotent3 0 o 0) (upperUnipotent3_mem_converseCongruenceSet3 a ho valued_zero_le_one) 1
      (by rw [Units.val_one, upperUnipotent3_apply_two_two]) (h * localToAdelic3 v (upperUnipotent3 0 x 0)),
    map_one, Units.val_one, one_mul]

private theorem sum_radicalDifference_add_adeleSingleAt_eq_zero {a : ℕ} (ha : 1 ≤ a) {χ : (v.adicCompletion ℚ)ˣ →* ℂˣ}
    (hχ : ∀ u ∈ LanglandsTunnell.TateLocal.higherUnitsAt ℚ v (2 * a - 1), χ u = 1)
    {W : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ} (hWK : IsCongruenceEquivariantAlong v a χ W)
    (hWl : HasVanishingUnipotentIntegralAlong v W)
    (hsum : ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ, Summable fun i : MirabolicIndex ℚ => W (mirabolicTranslate i * g))
    (hsum' : ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ,
      Summable fun i : MirabolicIndex ℚ => dualWhittakerFn3 W (mirabolicTranslate i * g))
    (g : AdelicGL 3 (𝓞 ℚ) ℚ) (hg : componentAt3 (𝓞 ℚ) ℚ v g ∈ converseCongruenceSet3 v a)
    (R : Finset (v.adicCompletion ℚ)) (hR : ∀ t ∈ R, Valued.v t ≤ WithZero.exp (1 : ℤ))
    (hcov : ∀ x : v.adicCompletion ℚ, Valued.v x ≤ WithZero.exp (1 : ℤ) → ∃ t ∈ R, Valued.v (x - t) ≤ 1)
    (hsep : ∀ t ∈ R, ∀ t' ∈ R, Valued.v (t - t') ≤ 1 → t = t') (z y : AdeleRing (𝓞 ℚ) ℚ) :
    ∑ t ∈ R, radicalDifference W g z (y + adeleSingleAt ℚ v t) = 0 := by
  classical

  have hm : Valued.v (mixUnit (componentAt3 (𝓞 ℚ) ℚ v g)) = 1 := valued_mixUnit_eq_one ha hg

  have hk : ∀ t : v.adicCompletion ℚ, Valued.v t ≤ WithZero.exp (1 : ℤ) →
      unipotentCorrection (componentAt3 (𝓞 ℚ) ℚ v g) t ∈ converseCongruenceSet3 v a := fun t ht =>
    unipotentCorrection_mem_converseCongruenceSet3 ha hg ht
  have hχk : ∀ t : v.adicCompletion ℚ, ∀ ht : Valued.v t ≤ WithZero.exp (1 : ℤ),
      ∃ u : (v.adicCompletion ℚ)ˣ, (u : v.adicCompletion ℚ) =
        (unipotentCorrection (componentAt3 (𝓞 ℚ) ℚ v g) t :
          Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 2 2 ∧ χ u = 1 := fun t ht => by
    have h1 : Valued.v ((unipotentCorrection (componentAt3 (𝓞 ℚ) ℚ v g) t :
        Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 2 2) = 1 :=
      valued_apply_two_two_eq_one_of_mem_of_pos ha (hk t ht)
    refine ⟨Units.mk0 _ (ne_zero_of_valued_eq_one' h1), Units.val_mk0 _, hχ _ ⟨h1, Or.inr ?_⟩⟩
    exact valued_unipotentCorrection_sub_one_le ha hg ht
  have hsh : ∀ t : v.adicCompletion ℚ, Valued.v t ≤ WithZero.exp (1 : ℤ) →
      upperUnipotent3 0 0 (t * mixShift (componentAt3 (𝓞 ℚ) ℚ v g)) ∈ converseCongruenceSet3 v a := fun t ht => by
    refine upperUnipotent3_mem_converseCongruenceSet3 a valued_zero_le_one ?_
    rw [map_mul, ← WithZero.exp_zero]
    refine (mul_le_mul' ht (valued_mixShift_le hg)).trans ?_
    rw [← WithZero.exp_add]
    exact WithZero.exp_le_exp.mpr (by omega)
  have hone : ∀ s : v.adicCompletion ℚ,
      ((1 : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) =
        ((upperUnipotent3 0 0 s : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 2 2 :=
    fun s => by rw [Units.val_one, upperUnipotent3_apply_two_two]

  have hpt : ∀ t : v.adicCompletion ℚ, radicalP21 ![z, y + adeleSingleAt ℚ v t] * g =
      radicalP21 ![z, y] * g *
        localToAdelic3 v (upperUnipotent3 0 (t * mixUnit (componentAt3 (𝓞 ℚ) ℚ v g)) 0) *
        localToAdelic3 v (upperUnipotent3 0 0 (t * mixShift (componentAt3 (𝓞 ℚ) ℚ v g))) *
        localToAdelic3 v (unipotentCorrection (componentAt3 (𝓞 ℚ) ℚ v g) t) := fun t => by
    have hconj : (componentAt3 (𝓞 ℚ) ℚ v g)⁻¹ * upperUnipotent3 0 t 0 * componentAt3 (𝓞 ℚ) ℚ v g =
        upperUnipotent3 0 (t * mixUnit (componentAt3 (𝓞 ℚ) ℚ v g)) 0 *
          upperUnipotent3 0 0 (t * mixShift (componentAt3 (𝓞 ℚ) ℚ v g)) *
          unipotentCorrection (componentAt3 (𝓞 ℚ) ℚ v g) t := by
      rw [mul_assoc, upperUnipotent3_mul_eq_mul_unipotentCorrection (componentAt3 (𝓞 ℚ) ℚ v g) t, mul_assoc,
        inv_mul_cancel_left, upperUnipotent3_zero_eq_mul]
    rw [vecTwo_add_snd, radicalP21_add, radicalP21_zero_left, upperUnipotent3_zero_adeleSingleAt_zero, mul_assoc,
      localToAdelic3_mul_eq_mul_localToAdelic3, hconj, map_mul, map_mul]
    simp only [mul_assoc]

  have hA : ∀ t : v.adicCompletion ℚ, Valued.v t ≤ WithZero.exp (1 : ℤ) →
      (∑' i : MirabolicIndex ℚ, W (mirabolicTranslate i * (radicalP21 ![z, y + adeleSingleAt ℚ v t] * g))) =
        ∑' i : MirabolicIndex ℚ, W (mirabolicTranslate i * (radicalP21 ![z, y] * g *
          localToAdelic3 v (upperUnipotent3 0 (t * mixUnit (componentAt3 (𝓞 ℚ) ℚ v g)) 0))) := by
    intro t ht
    obtain ⟨u, hu, hχu⟩ := hχk t ht
    rw [hpt t, mirabolicSeries_mul_localToAdelic3 hWK (hk t ht) u hu, hχu, Units.val_one, one_mul,
      mirabolicSeries_mul_localToAdelic3 hWK (hsh t ht) 1 (hone _), map_one, Units.val_one, one_mul]

  have hB : ∀ t : v.adicCompletion ℚ, Valued.v t ≤ WithZero.exp (1 : ℤ) →
      (∑' i : MirabolicIndex ℚ, dualWhittakerFn3 W (mirabolicTranslate i *
          (weylPrime3 * transposeInv3 (radicalP21 ![z, y + adeleSingleAt ℚ v t] * g)))) =
        ∑' i : MirabolicIndex ℚ, dualWhittakerFn3 W (mirabolicTranslate i *
          (weylPrime3 * transposeInv3 (radicalP21 ![z, y] * g *
            localToAdelic3 v (upperUnipotent3 0 (t * mixUnit (componentAt3 (𝓞 ℚ) ℚ v g)) 0)))) := by
    intro t ht
    obtain ⟨u, hu, hχu⟩ := hχk t ht
    rw [hpt t, dualMirabolicSeries_mul_localToAdelic3 hWK (hk t ht) u hu, hχu, Units.val_one, one_mul,
      dualMirabolicSeries_mul_localToAdelic3 hWK (hsh t ht) 1 (hone _), map_one, Units.val_one, one_mul]

  have himg := image_mul_representatives hm R hR hcov hsep
  obtain ⟨hR', hcov', hsep'⟩ := himg
  have hinj : Set.InjOn (fun t => t * mixUnit (componentAt3 (𝓞 ℚ) ℚ v g)) R := fun t _ t' _ h =>
    mul_right_cancel₀ (ne_zero_of_valued_eq_one' hm) h
  have hsumA : ∑ t ∈ R, ∑' i : MirabolicIndex ℚ, W (mirabolicTranslate i * (radicalP21 ![z, y] * g *
      localToAdelic3 v (upperUnipotent3 0 (t * mixUnit (componentAt3 (𝓞 ℚ) ℚ v g)) 0))) = 0 := by
    rw [← Finset.sum_image (f := fun s => ∑' i : MirabolicIndex ℚ, W (mirabolicTranslate i *
      (radicalP21 ![z, y] * g * localToAdelic3 v (upperUnipotent3 0 s 0)))) hinj,
      ← Summable.tsum_finsetSum fun s _ => hsum _]
    refine (tsum_congr fun i => ?_).trans tsum_zero
    simp_rw [← mul_assoc (mirabolicTranslate i) (radicalP21 ![z, y] * g)]
    exact sum_apply_mul_localToAdelic3_upperUnipotent3_eq_zero hWK hWl _ hR' hcov' hsep' _
  have hsumB : ∑ t ∈ R, ∑' i : MirabolicIndex ℚ, dualWhittakerFn3 W (mirabolicTranslate i *
      (weylPrime3 * transposeInv3 (radicalP21 ![z, y] * g *
        localToAdelic3 v (upperUnipotent3 0 (t * mixUnit (componentAt3 (𝓞 ℚ) ℚ v g)) 0)))) = 0 := by
    rw [← Finset.sum_image (f := fun s => ∑' i : MirabolicIndex ℚ, dualWhittakerFn3 W (mirabolicTranslate i *
      (weylPrime3 * transposeInv3 (radicalP21 ![z, y] * g * localToAdelic3 v (upperUnipotent3 0 s 0)))))
      hinj, ← Summable.tsum_finsetSum fun s _ => hsum' _]
    have hq : ∀ (i : MirabolicIndex ℚ) (s : v.adicCompletion ℚ),
        dualWhittakerFn3 W (mirabolicTranslate i * (weylPrime3 * transposeInv3 (radicalP21 ![z, y] * g *
          localToAdelic3 v (upperUnipotent3 0 s 0)))) =
        W (longWeyl3 * transposeInv3 (mirabolicTranslate i) * transposeInv3 weylPrime3 *
          (radicalP21 ![z, y] * g) * localToAdelic3 v (upperUnipotent3 0 s 0)) := fun i s => by
      rw [dualWhittakerFn3_apply, transposeInv3_mul_aux22, transposeInv3_mul_aux22, transposeInv3_transposeInv3_aux22]
      simp only [mul_assoc]
    refine (tsum_congr fun i => ?_).trans tsum_zero
    simp_rw [hq]
    exact sum_apply_mul_localToAdelic3_upperUnipotent3_eq_zero hWK hWl _ hR' hcov' hsep' _

  calc ∑ t ∈ R, radicalDifference W g z (y + adeleSingleAt ℚ v t)
      = ∑ t ∈ R, ((∑' i : MirabolicIndex ℚ, W (mirabolicTranslate i * (radicalP21 ![z, y] * g *
            localToAdelic3 v (upperUnipotent3 0 (t * mixUnit (componentAt3 (𝓞 ℚ) ℚ v g)) 0)))) -
          ∑' i : MirabolicIndex ℚ, dualWhittakerFn3 W (mirabolicTranslate i *
            (weylPrime3 * transposeInv3 (radicalP21 ![z, y] * g *
              localToAdelic3 v (upperUnipotent3 0 (t * mixUnit (componentAt3 (𝓞 ℚ) ℚ v g)) 0))))) := by
        refine Finset.sum_congr rfl fun t ht => ?_
        rw [radicalDifference, hA t (hR t ht), hB t (hR t ht)]
    _ = 0 := by rw [Finset.sum_sub_distrib, hsumA, hsumB, sub_zero]

end Average
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_mirabolicSeries_eq_dual_of_radicalCoefficient_eq.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_mirabolicSeries_eq_dual_of_radicalCoefficient_eq.LanglandsTunnell.CubicInduction"
end
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_mirabolicSeries_eq_dual_of_radicalCoefficient_eq.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_mirabolicSeries_eq_dual_of_radicalCoefficient_eq.LanglandsTunnell.CubicInduction"
end LanglandsTunnell.CubicInduction
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_mirabolicSeries_eq_dual_of_radicalCoefficient_eq.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_mirabolicSeries_eq_dual_of_radicalCoefficient_eq.LanglandsTunnell.CubicInduction"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_mirabolicSeries_eq_dual_of_radicalCoefficient_eq.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_mirabolicSeries_eq_dual_of_radicalCoefficient_eq.LanglandsTunnell.CubicInduction"

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "Converse.IsAdmissibleTwist TateLocal.addCharLevel TateLocal.localBorel TateLocal.borelSpace_localBorel TateLocal.integersPositiveCompacts TateLocal.coe_integersPositiveCompacts TateLocal.selfDualHaarAt TateLocal.higherUnitsAt TateLocal.forall_eq_one_and_exists_ne_one_of_addCharLevel"
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "matrixFin_ext matrixAdele_ext localMatN mapMatrix_localMatN_self mapMatrix_localMatN_of_ne finMatN mapMatrix_arch_finMatN mapMatrix_fin_finMatN localToAdelic3 converseCongruenceSet3 HasVanishingUnipotentIntegralAlong IsCongruenceEquivariantAlong lowerUnipotent21 longWeyl3 longWeyl3_coe dualWhittakerFn3 dualWhittakerFn3_apply weylPrime3 weylPrime3_coe weylPrime3_mul_self transposeInv3_weylPrime3 weylPrime3_mul_transposeInv3_radicalP21_mul_weylPrime3 IsGL3PsiWhittakerFn transposeInv3 IsCuspidalAlongP21 psiLoc mirabolicTranslate AdelicGL globalPointsGL centralScalarGL upperUnipotent3 upperUnipotent3_coe upperUnipotent3_zero radicalP21 radicalP21_zero radicalP21_coe radicalP21_add embedMat2 iotaGL coe_iotaGL iota MirabolicIndex mirabolicRep mirabolicRep_spec mirabolic_mk_unipotent_mul localMaximalCompact3 componentAtN archComponentN componentAt3 archComponent3 LocalGL3 cosetSum IsCosetEigenfunction IsRightInvariant diagUnitGL2 diagHom diagHom_apply isCuspidalAlongP21_mirabolicSeries"
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"
section
open IsDedekindDomain NumberField

variable {v : HeightOneSpectrum (𝓞 ℚ)}

private theorem ne_zero_of_valued_eq_one {β : v.adicCompletion ℚ} (hβ : Valued.v β = 1) : β ≠ 0 := by
  intro h
  rw [h, map_zero] at hβ
  exact zero_ne_one hβ

private noncomputable def mixGL3 (α β : v.adicCompletion ℚ) (hβ : β ≠ 0) : LocalGL3 v :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![1, 0, 0; α, β, 0; 0, 0, 1]
    (by simpa [Matrix.det_fin_three] using hβ)

private theorem mixGL3_coe (α β : v.adicCompletion ℚ) (hβ : β ≠ 0) :
    (mixGL3 α β hβ : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) = !![1, 0, 0; α, β, 0; 0, 0, 1] :=
  rfl

private theorem mixGL3_inv_coe (α β : v.adicCompletion ℚ) (hβ : β ≠ 0) :
    (((mixGL3 α β hβ)⁻¹ : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) =
      !![1, 0, 0; -(β⁻¹ * α), β⁻¹, 0; 0, 0, 1] := by
  rw [Matrix.GeneralLinearGroup.coe_inv, mixGL3_coe]
  refine Matrix.inv_eq_left_inv ?_
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three, hβ]

private theorem mixGL3_mem_converseCongruenceSet3 (n : ℕ) (α β : v.adicCompletion ℚ) (hα : Valued.v α ≤ 1)
    (hβ : Valued.v β = 1) :
    mixGL3 α β (ne_zero_of_valued_eq_one hβ) ∈ converseCongruenceSet3 v n := by
  have hβ0 : β ≠ 0 := ne_zero_of_valued_eq_one hβ
  refine ⟨⟨?_, ?_⟩, ?_, ?_, ?_⟩
  · intro i j
    rw [mixGL3_coe]
    fin_cases i <;> fin_cases j <;> simp [hα, hβ.le]
  · intro i j
    rw [mixGL3_inv_coe]
    fin_cases i <;> fin_cases j <;> simp [Valuation.map_neg, map_inv₀, hα, hβ]
  · rw [mixGL3_coe]
    simp
  · rw [mixGL3_coe]
    simp
  · rw [mixGL3_coe]
    simp
end
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_mirabolicSeries_eq_dual_of_radicalCoefficient_eq.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_mirabolicSeries_eq_dual_of_radicalCoefficient_eq.LanglandsTunnell.CubicInduction"
end LanglandsTunnell.CubicInduction
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_mirabolicSeries_eq_dual_of_radicalCoefficient_eq.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_mirabolicSeries_eq_dual_of_radicalCoefficient_eq.LanglandsTunnell.CubicInduction"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_mirabolicSeries_eq_dual_of_radicalCoefficient_eq.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_mirabolicSeries_eq_dual_of_radicalCoefficient_eq.LanglandsTunnell.CubicInduction"

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "Converse.IsAdmissibleTwist TateLocal.addCharLevel TateLocal.localBorel TateLocal.borelSpace_localBorel TateLocal.integersPositiveCompacts TateLocal.coe_integersPositiveCompacts TateLocal.selfDualHaarAt TateLocal.higherUnitsAt TateLocal.forall_eq_one_and_exists_ne_one_of_addCharLevel"
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "matrixFin_ext matrixAdele_ext localMatN mapMatrix_localMatN_self mapMatrix_localMatN_of_ne finMatN mapMatrix_arch_finMatN mapMatrix_fin_finMatN localToAdelic3 converseCongruenceSet3 HasVanishingUnipotentIntegralAlong IsCongruenceEquivariantAlong lowerUnipotent21 longWeyl3 longWeyl3_coe dualWhittakerFn3 dualWhittakerFn3_apply weylPrime3 weylPrime3_coe weylPrime3_mul_self transposeInv3_weylPrime3 weylPrime3_mul_transposeInv3_radicalP21_mul_weylPrime3 IsGL3PsiWhittakerFn transposeInv3 IsCuspidalAlongP21 psiLoc mirabolicTranslate AdelicGL globalPointsGL centralScalarGL upperUnipotent3 upperUnipotent3_coe upperUnipotent3_zero radicalP21 radicalP21_zero radicalP21_coe radicalP21_add embedMat2 iotaGL coe_iotaGL iota MirabolicIndex mirabolicRep mirabolicRep_spec mirabolic_mk_unipotent_mul localMaximalCompact3 componentAtN archComponentN componentAt3 archComponent3 LocalGL3 cosetSum IsCosetEigenfunction IsRightInvariant diagUnitGL2 diagHom diagHom_apply isCuspidalAlongP21_mirabolicSeries"
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"
section
open IsDedekindDomain NumberField

variable {v : HeightOneSpectrum (𝓞 ℚ)}

private def repRegion (v : HeightOneSpectrum (𝓞 ℚ)) : Set (v.adicCompletion ℚ) :=
  {x | Valued.v x ≤ WithZero.exp (1 : ℤ)}

private def repBall (t : v.adicCompletion ℚ) : Set (v.adicCompletion ℚ) :=
  (fun x => x - t) ⁻¹' (v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ))

private theorem mem_repBall {t x : v.adicCompletion ℚ} : x ∈ repBall t ↔ Valued.v (x - t) ≤ 1 :=
  Iff.rfl

private theorem isOpen_repBall (t : v.adicCompletion ℚ) : IsOpen (repBall t) := by
  have h : IsOpen (v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ)) := Valued.isOpen_valuationSubring _
  exact h.preimage (continuous_id.sub continuous_const)

private theorem exists_valued_eq_exp_neg_one (v : HeightOneSpectrum (𝓞 ℚ)) :
    ∃ ϖ : v.adicCompletion ℚ, Valued.v ϖ = WithZero.exp (-1 : ℤ) := by
  obtain ⟨π, hπ⟩ := v.valuation_exists_uniformizer ℚ
  exact ⟨_, (v.valuedAdicCompletion_eq_valuation' π).trans hπ⟩

private theorem isCompact_repRegion (v : HeightOneSpectrum (𝓞 ℚ)) : IsCompact (repRegion v) := by
  obtain ⟨ϖ, hπv⟩ := exists_valued_eq_exp_neg_one v
  have hπ0 : ϖ ≠ 0 := by
    intro h
    rw [h, map_zero] at hπv
    exact WithZero.exp_ne_zero hπv.symm
  have hc : IsCompact (v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ)) :=
    isCompact_iff_compactSpace.mpr (show CompactSpace (v.adicCompletionIntegers ℚ) from inferInstance)
  have himage : repRegion v =
      (fun y => ϖ⁻¹ * y) '' (v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ)) := by
    ext x
    constructor
    · intro hx
      have hx' : Valued.v x ≤ WithZero.exp (1 : ℤ) := hx
      refine ⟨ϖ * x, ?_, inv_mul_cancel_left₀ hπ0 x⟩
      show Valued.v (ϖ * x) ≤ 1
      rw [map_mul, hπv]
      calc WithZero.exp (-1 : ℤ) * Valued.v x ≤ WithZero.exp (-1 : ℤ) * WithZero.exp (1 : ℤ) := mul_le_mul' le_rfl hx'
        _ = 1 := by rw [← WithZero.exp_add, neg_add_cancel, WithZero.exp_zero]
    · rintro ⟨y, hy, rfl⟩
      have hy' : Valued.v y ≤ 1 := hy
      show Valued.v (ϖ⁻¹ * y) ≤ WithZero.exp (1 : ℤ)
      rw [map_mul, map_inv₀, hπv]
      calc (WithZero.exp (-1 : ℤ))⁻¹ * Valued.v y ≤ (WithZero.exp (-1 : ℤ))⁻¹ * 1 := mul_le_mul' le_rfl hy'
        _ = WithZero.exp (1 : ℤ) := by rw [mul_one, WithZero.exp_neg, inv_inv]
  rw [himage]
  exact hc.image (continuous_const.mul continuous_id)

private noncomputable def repPick (C : Finset (v.adicCompletion ℚ)) : v.adicCompletion ℚ :=
  if h : C.Nonempty then h.choose else 0

private theorem repPick_mem {C : Finset (v.adicCompletion ℚ)} (h : C.Nonempty) : repPick C ∈ C := by
  rw [repPick, dif_pos h]
  exact h.choose_spec

private noncomputable def repClass (T : Finset (v.adicCompletion ℚ)) (t : v.adicCompletion ℚ) :
    Finset (v.adicCompletion ℚ) :=
  T.filter fun t' => Valued.v (t' - t) ≤ 1

private theorem near_trans {x y z : v.adicCompletion ℚ} (hxy : Valued.v (x - y) ≤ 1) (hyz : Valued.v (y - z) ≤ 1) :
    Valued.v (x - z) ≤ 1 := by
  have h : x - z = (x - y) + (y - z) := by ring
  rw [h]
  exact Valuation.map_add_le _ hxy hyz

private theorem near_symm {x y : v.adicCompletion ℚ} (hxy : Valued.v (x - y) ≤ 1) : Valued.v (y - x) ≤ 1 := by
  rwa [Valuation.map_sub_swap]

private theorem repClass_nonempty {T : Finset (v.adicCompletion ℚ)} {t : v.adicCompletion ℚ} (ht : t ∈ T) :
    (repClass T t).Nonempty := by
  refine ⟨t, ?_⟩
  unfold repClass
  exact Finset.mem_filter.mpr ⟨ht, by simp⟩

private theorem repClass_eq_of_near (T : Finset (v.adicCompletion ℚ)) {t t' : v.adicCompletion ℚ}
    (h : Valued.v (t - t') ≤ 1) : repClass T t = repClass T t' := by
  ext s
  simp only [repClass, Finset.mem_filter]
  constructor
  · rintro ⟨hs, hst⟩
    exact ⟨hs, near_trans hst h⟩
  · rintro ⟨hs, hst'⟩
    exact ⟨hs, near_trans hst' (near_symm h)⟩

private theorem exists_finset_representatives (v : HeightOneSpectrum (𝓞 ℚ)) :
    ∃ R : Finset (v.adicCompletion ℚ), (∀ t ∈ R, Valued.v t ≤ WithZero.exp (1 : ℤ)) ∧
      (∀ x : v.adicCompletion ℚ, Valued.v x ≤ WithZero.exp (1 : ℤ) → ∃ t ∈ R, Valued.v (x - t) ≤ 1) ∧
        ∀ t ∈ R, ∀ t' ∈ R, Valued.v (t - t') ≤ 1 → t = t' := by
  obtain ⟨T₀, hT₀, hfin, hcover⟩ := (isCompact_repRegion v).elim_finite_subcover_image (b := repRegion v)
    (c := repBall) (fun t _ => isOpen_repBall t) (fun x hx => Set.mem_iUnion₂.mpr ⟨x, hx, by simp [mem_repBall]⟩)
  classical
  set T : Finset (v.adicCompletion ℚ) := hfin.toFinset
  have hmemT : ∀ {t : v.adicCompletion ℚ}, t ∈ T → Valued.v t ≤ WithZero.exp (1 : ℤ) :=
    fun ht => hT₀ (hfin.mem_toFinset.mp ht)
  have hrep_mem : ∀ {t : v.adicCompletion ℚ},
      t ∈ T → repPick (repClass T t) ∈ T ∧ Valued.v (repPick (repClass T t) - t) ≤ 1 := by
    intro t ht
    have h := repPick_mem (repClass_nonempty ht)
    unfold repClass at h
    exact Finset.mem_filter.mp h
  refine ⟨T.image fun t => repPick (repClass T t), ?_, ?_, ?_⟩
  · intro r hr
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hr
    exact hmemT (hrep_mem ht).1
  · intro x hx
    obtain ⟨t, ht₀, hxt⟩ := Set.mem_iUnion₂.mp (hcover (show x ∈ repRegion v from hx))
    have ht : t ∈ T := hfin.mem_toFinset.mpr ht₀
    refine ⟨repPick (repClass T t), Finset.mem_image_of_mem _ ht, ?_⟩
    exact near_trans (mem_repBall.mp hxt) (near_symm (hrep_mem ht).2)
  · intro r hr r' hr' hrr'
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hr
    obtain ⟨t', ht', rfl⟩ := Finset.mem_image.mp hr'
    have htt' : Valued.v (t - t') ≤ 1 :=
      near_trans (near_symm (hrep_mem ht).2) (near_trans hrr' (hrep_mem ht').2)
    show repPick (repClass T t) = repPick (repClass T t')
    rw [repClass_eq_of_near T htt']
end
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_mirabolicSeries_eq_dual_of_radicalCoefficient_eq.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_mirabolicSeries_eq_dual_of_radicalCoefficient_eq.LanglandsTunnell.CubicInduction"
end LanglandsTunnell.CubicInduction
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_mirabolicSeries_eq_dual_of_radicalCoefficient_eq.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_mirabolicSeries_eq_dual_of_radicalCoefficient_eq.LanglandsTunnell.CubicInduction"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_mirabolicSeries_eq_dual_of_radicalCoefficient_eq.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_mirabolicSeries_eq_dual_of_radicalCoefficient_eq.LanglandsTunnell.CubicInduction"

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "Converse.IsAdmissibleTwist TateLocal.addCharLevel TateLocal.localBorel TateLocal.borelSpace_localBorel TateLocal.integersPositiveCompacts TateLocal.coe_integersPositiveCompacts TateLocal.selfDualHaarAt TateLocal.higherUnitsAt TateLocal.forall_eq_one_and_exists_ne_one_of_addCharLevel"
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "matrixFin_ext matrixAdele_ext localMatN mapMatrix_localMatN_self mapMatrix_localMatN_of_ne finMatN mapMatrix_arch_finMatN mapMatrix_fin_finMatN localToAdelic3 converseCongruenceSet3 HasVanishingUnipotentIntegralAlong IsCongruenceEquivariantAlong lowerUnipotent21 longWeyl3 longWeyl3_coe dualWhittakerFn3 dualWhittakerFn3_apply weylPrime3 weylPrime3_coe weylPrime3_mul_self transposeInv3_weylPrime3 weylPrime3_mul_transposeInv3_radicalP21_mul_weylPrime3 IsGL3PsiWhittakerFn transposeInv3 IsCuspidalAlongP21 psiLoc mirabolicTranslate AdelicGL globalPointsGL centralScalarGL upperUnipotent3 upperUnipotent3_coe upperUnipotent3_zero radicalP21 radicalP21_zero radicalP21_coe radicalP21_add embedMat2 iotaGL coe_iotaGL iota MirabolicIndex mirabolicRep mirabolicRep_spec mirabolic_mk_unipotent_mul localMaximalCompact3 componentAtN archComponentN componentAt3 archComponent3 LocalGL3 cosetSum IsCosetEigenfunction IsRightInvariant diagUnitGL2 diagHom diagHom_apply isCuspidalAlongP21_mirabolicSeries"
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"
section
open IsDedekindDomain NumberField NumberField.TateGlobal NumberField.StandardAddChar AutomorphicForm LanglandsTunnell.Converse

section Trichotomy

variable {v : HeightOneSpectrum (𝓞 ℚ)}

private theorem valued_eq_one_of_le_one_of_not_le_exp_neg_one {x : v.adicCompletion ℚ} (h1 : Valued.v x ≤ 1)
    (h2 : ¬ Valued.v x ≤ WithZero.exp (-1 : ℤ)) : Valued.v x = 1 := by
  have h0 : Valued.v x ≠ 0 := fun h => h2 (by rw [h]; exact zero_le')
  have hn : Valued.v x = WithZero.exp (WithZero.log (Valued.v x)) := (WithZero.exp_log h0).symm
  have hlt : WithZero.exp (-1 : ℤ) < Valued.v x := not_le.mp h2
  rw [hn] at h1 hlt ⊢
  rw [← WithZero.exp_zero] at h1 ⊢
  have hlt' := WithZero.exp_lt_exp.mp hlt
  have h1' := WithZero.exp_le_exp.mp h1
  exact le_antisymm (WithZero.exp_le_exp.mpr h1') (WithZero.exp_le_exp.mpr (by omega))

end Trichotomy
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_mirabolicSeries_eq_dual_of_radicalCoefficient_eq.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_mirabolicSeries_eq_dual_of_radicalCoefficient_eq.LanglandsTunnell.CubicInduction"

section Assembly

private theorem radicalCoefficient_eq_zero_of_forall_mem_converseCongruenceSet3
    (ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ) (_hψ : IsGlobalAddChar ℚ ψ)
    (S : Finset (HeightOneSpectrum (𝓞 ℚ)))
    (_hψS : ∀ v ∈ S, LanglandsTunnell.TateLocal.addCharLevel (psiLoc ψ v) = 0)
    (a : HeightOneSpectrum (𝓞 ℚ) → ℕ) (_ha : ∀ v ∈ S, 1 ≤ a v)
    (ω : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (_hω : IsAdmissibleTwist ℚ ω)
    (_hωa : ∀ v ∈ S, ∀ u ∈ LanglandsTunnell.TateLocal.higherUnitsAt ℚ v (2 * a v - 1), localChar ω v u = 1)
    (W : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)
    (_hW : IsGL3PsiWhittakerFn ψ W)
    (_hWω : ∀ (z : (AdeleRing (𝓞 ℚ) ℚ)ˣ) (g : AdelicGL 3 (𝓞 ℚ) ℚ),
      W (centralScalarGL 3 (𝓞 ℚ) ℚ z * g) = (ω z : ℂ) * W g)
    (_hWK : ∀ v ∈ S, IsCongruenceEquivariantAlong v (a v) (localChar ω v) W)
    (_hWl : ∀ v ∈ S, HasVanishingUnipotentIntegralAlong v W)
    (_hsum : ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ, Summable fun i : MirabolicIndex ℚ => W (mirabolicTranslate i * g))
    (_hsum' : ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ,
      Summable fun i : MirabolicIndex ℚ => dualWhittakerFn3 W (mirabolicTranslate i * g))
    (_hcont' : Continuous fun g => ∑' i : MirabolicIndex ℚ, dualWhittakerFn3 W (mirabolicTranslate i * g))
    (_hV : ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ,
      (∀ v ∈ S, componentAt3 (𝓞 ℚ) ℚ v g ∈ converseCongruenceSet3 v (a v)) →
      (∫ z : AdeleRing (𝓞 ℚ) ℚ, ∫ y : AdeleRing (𝓞 ℚ) ℚ,
          (∑' i : MirabolicIndex ℚ, W (mirabolicTranslate i * (radicalP21 ![z, y] * g))) * ψ (-y)
        ∂(ProbabilityTheory.cond (NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ) (AdelicBox.adelicBox ℚ))
        ∂(ProbabilityTheory.cond (NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ) (AdelicBox.adelicBox ℚ))) =
      ∫ z : AdeleRing (𝓞 ℚ) ℚ, ∫ y : AdeleRing (𝓞 ℚ) ℚ,
          (∑' i : MirabolicIndex ℚ, dualWhittakerFn3 W (mirabolicTranslate i *
            (weylPrime3 * transposeInv3 (radicalP21 ![z, y] * g)))) * ψ (-y)
        ∂(ProbabilityTheory.cond (NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ) (AdelicBox.adelicBox ℚ))
        ∂(ProbabilityTheory.cond (NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ) (AdelicBox.adelicBox ℚ)))
    (g : AdelicGL 3 (𝓞 ℚ) ℚ) (hg : ∀ v ∈ S, componentAt3 (𝓞 ℚ) ℚ v g ∈ converseCongruenceSet3 v (a v))
    (α β : ℚ) : radicalCoefficient ψ W g α β = 0 := by
  classical
  have hper₁ := radicalDifference_fst_periodic ψ _hψ ω _hω W _hW _hWω g
  have hper₂ := radicalDifference_snd_periodic ψ _hψ ω _hω W _hW _hWω g
  by_cases hβ0 : β = 0
  · subst hβ0
    by_cases hα0 : α = 0
    · subst hα0
      exact radicalCoefficient_zero_zero_eq_zero ψ _hψ W _hW _hsum _hsum' _hcont' ∅ (fun _ => ⊥) (fun _ => 1)
        (isCuspidalAlongP21_mirabolicSeries ψ _hψ W _hW ∅ (fun _ => ⊥) (fun _ => 1)) g
    · exact radicalCoefficient_zero_right_eq_zero ψ _hψ ω _hω W _hW _hWω _hsum _hsum' _hcont' g α hα0

  by_cases hM1 : ∃ v ∈ S, ¬ Valued.v (algebraMap ℚ (v.adicCompletion ℚ) β) ≤ 1
  · obtain ⟨v, hv, hβv⟩ := hM1
    obtain ⟨ℓ, hℓ, hβt⟩ :=
      exists_valued_le_one_and_addChar_algebraMap_mul_adeleSingleAt_ne_one ψ _hψ v (_hψS v hv) β hβv
    exact boxCoefficient_eq_zero_of_snd_invariant _hψ (radicalDifference W g) hper₂ (adeleSingleAt ℚ v ℓ)
      (fun z y => radicalDifference_add_adeleSingleAt_snd (_hWK v hv) (_ha v hv) (hg v hv) hℓ z y) α β hβt
  have hint : ∀ v ∈ S, Valued.v (algebraMap ℚ (v.adicCompletion ℚ) β) ≤ 1 := fun v hv =>
    not_not.mp fun h => hM1 ⟨v, hv, h⟩

  by_cases hM1' : ∃ v ∈ S, ¬ Valued.v (algebraMap ℚ (v.adicCompletion ℚ) α) ≤ 1
  · obtain ⟨v, hv, hαv⟩ := hM1'
    obtain ⟨ℓ, hℓ, hαt⟩ :=
      exists_valued_le_one_and_addChar_algebraMap_mul_adeleSingleAt_ne_one ψ _hψ v (_hψS v hv) α hαv
    exact boxCoefficient_eq_zero_of_fst_invariant _hψ (radicalDifference W g) hper₁ (adeleSingleAt ℚ v ℓ)
      (fun z y => radicalDifference_add_adeleSingleAt_fst (_hWK v hv) (_ha v hv) (hg v hv) hℓ z y) α β hαt
  have hint' : ∀ v ∈ S, Valued.v (algebraMap ℚ (v.adicCompletion ℚ) α) ≤ 1 := fun v hv =>
    not_not.mp fun h => hM1' ⟨v, hv, h⟩

  by_cases hM2 : ∃ v ∈ S, Valued.v (algebraMap ℚ (v.adicCompletion ℚ) β) ≤ WithZero.exp (-1 : ℤ)
  · obtain ⟨v, hv, hβv⟩ := hM2
    obtain ⟨R, hR, hcov, hsep⟩ := exists_finset_representatives v
    obtain ⟨t₀, ht₀, -⟩ := hcov 0 (by rw [map_zero]; exact zero_le')
    exact boxCoefficient_eq_zero_of_sum_translates_eq_zero _hψ (radicalDifference W g)
      (continuous_radicalDifference ψ _hψ W _hW _hsum _hcont' g) hper₂ R ⟨t₀, ht₀⟩ (⇑(adeleSingleAt ℚ v)) α β
      (fun t ht =>
        addChar_algebraMap_mul_adeleSingleAt_eq_one_of_valued_le ψ _hψ v (_hψS v hv) β hβv t (hR t ht))
      (fun z y => sum_radicalDifference_add_adeleSingleAt_eq_zero (_ha v hv) (_hωa v hv) (_hWK v hv)
        (_hWl v hv) _hsum _hsum' g (hg v hv) R hR hcov hsep z y)

  have hunit : ∀ v ∈ S, Valued.v (algebraMap ℚ (v.adicCompletion ℚ) β) = 1 := fun v hv =>
    valued_eq_one_of_le_one_of_not_le_exp_neg_one (hint v hv) fun h => hM2 ⟨v, hv, h⟩
  rw [radicalCoefficient_eq_zero_one_iotaGL_lowerRat_mul ψ _hψ ω _hω W _hW _hWω g α β hβ0]
  refine radicalCoefficient_zero_one_eq_zero_of_locus ψ _hψ S a W _hW _hsum _hcont' _hV _ fun v hv => ?_
  rw [map_mul]
  refine mul_mem_converseCongruenceSet3 ?_ (hg v hv)
  have hβv0 : algebraMap ℚ (v.adicCompletion ℚ) β ≠ 0 := ne_zero_of_valued_eq_one (hunit v hv)
  have hid : componentAt3 (𝓞 ℚ) ℚ v (iotaGL (globalPoints (𝓞 ℚ) ℚ (lowerRat α (Units.mk0 β hβ0)))) =
      mixGL3 (algebraMap ℚ (v.adicCompletion ℚ) α) (algebraMap ℚ (v.adicCompletion ℚ) β) hβv0 := by
    refine Matrix.GeneralLinearGroup.ext fun i j => ?_
    rw [coe_componentAt3_iotaGL_globalPoints, mixGL3_coe]
    fin_cases i <;> fin_cases j <;> simp
  rw [hid]
  exact mixGL3_mem_converseCongruenceSet3 (a v) _ _ (hint' v hv) (hunit v hv)

end Assembly
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_mirabolicSeries_eq_dual_of_radicalCoefficient_eq.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_mirabolicSeries_eq_dual_of_radicalCoefficient_eq.LanglandsTunnell.CubicInduction"
end
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_mirabolicSeries_eq_dual_of_radicalCoefficient_eq.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_mirabolicSeries_eq_dual_of_radicalCoefficient_eq.LanglandsTunnell.CubicInduction"
end LanglandsTunnell.CubicInduction
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_mirabolicSeries_eq_dual_of_radicalCoefficient_eq.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_mirabolicSeries_eq_dual_of_radicalCoefficient_eq.LanglandsTunnell.CubicInduction"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_mirabolicSeries_eq_dual_of_radicalCoefficient_eq.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_mirabolicSeries_eq_dual_of_radicalCoefficient_eq.LanglandsTunnell.CubicInduction"

p2m_open "IsDedekindDomain NumberField NumberField.TateGlobal AutomorphicForm LanglandsTunnell.Converse LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_mirabolicSeries_eq_dual_of_radicalCoefficient_eq.LanglandsTunnell.CubicInduction"

attribute [local instance] NumberField.Idele.ideleBorel NumberField.AdelicHaar.adeleBorel in
open _root_.LanglandsTunnell.CubicInduction _root_.P2MW.S_LanglandsTunnell_CubicInduction_mirabolicSeries_eq_dual_of_radicalCoefficient_eq.LanglandsTunnell.CubicInduction _root_.LanglandsTunnell _root_.P2MW.S_LanglandsTunnell_CubicInduction_mirabolicSeries_eq_dual_of_radicalCoefficient_eq.LanglandsTunnell in
theorem solution
    (ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ) (_hψ : IsGlobalAddChar ℚ ψ)
    (S : Finset (HeightOneSpectrum (𝓞 ℚ)))
    (_hψS : ∀ v ∈ S, LanglandsTunnell.TateLocal.addCharLevel (psiLoc ψ v) = 0)
    (a : HeightOneSpectrum (𝓞 ℚ) → ℕ) (_ha : ∀ v ∈ S, 1 ≤ a v)
    (ω : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (_hω : IsAdmissibleTwist ℚ ω)
    (_hωa : ∀ v ∈ S, ∀ u ∈ LanglandsTunnell.TateLocal.higherUnitsAt ℚ v (2 * a v - 1), localChar ω v u = 1)
    (W : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)
    (_hW : IsGL3PsiWhittakerFn ψ W)
    (_hWω : ∀ (z : (AdeleRing (𝓞 ℚ) ℚ)ˣ) (g : AdelicGL 3 (𝓞 ℚ) ℚ),
      W (centralScalarGL 3 (𝓞 ℚ) ℚ z * g) = (ω z : ℂ) * W g)
    (_hWK : ∀ v ∈ S, IsCongruenceEquivariantAlong v (a v) (localChar ω v) W)
    (_hWl : ∀ v ∈ S, HasVanishingUnipotentIntegralAlong v W)
    (_hsum : ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ, Summable fun i : MirabolicIndex ℚ => W (mirabolicTranslate i * g))
    (_hsum' : ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ,
      Summable fun i : MirabolicIndex ℚ => dualWhittakerFn3 W (mirabolicTranslate i * g))
    (_hcont' : Continuous fun g => ∑' i : MirabolicIndex ℚ, dualWhittakerFn3 W (mirabolicTranslate i * g))
    (_hV : ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ,
      (∀ v ∈ S, componentAt3 (𝓞 ℚ) ℚ v g ∈ converseCongruenceSet3 v (a v)) →
      (∫ z : AdeleRing (𝓞 ℚ) ℚ, ∫ y : AdeleRing (𝓞 ℚ) ℚ,
          (∑' i : MirabolicIndex ℚ, W (mirabolicTranslate i * (radicalP21 ![z, y] * g))) * ψ (-y)
        ∂(ProbabilityTheory.cond (NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ) (AdelicBox.adelicBox ℚ))
        ∂(ProbabilityTheory.cond (NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ) (AdelicBox.adelicBox ℚ))) =
      ∫ z : AdeleRing (𝓞 ℚ) ℚ, ∫ y : AdeleRing (𝓞 ℚ) ℚ,
          (∑' i : MirabolicIndex ℚ, dualWhittakerFn3 W (mirabolicTranslate i *
            (weylPrime3 * transposeInv3 (radicalP21 ![z, y] * g)))) * ψ (-y)
        ∂(ProbabilityTheory.cond (NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ) (AdelicBox.adelicBox ℚ))
        ∂(ProbabilityTheory.cond (NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ) (AdelicBox.adelicBox ℚ))) :
    ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ,
      (∀ v ∈ S, componentAt3 (𝓞 ℚ) ℚ v g ∈ converseCongruenceSet3 v (a v)) →
      (∑' i : MirabolicIndex ℚ, W (mirabolicTranslate i * g)) =
        ∑' i : MirabolicIndex ℚ, dualWhittakerFn3 W (mirabolicTranslate i * (weylPrime3 * transposeInv3 g)) := by
  intro g hg
  exact LanglandsTunnell.CubicInduction.mirabolicSeries_eq_dualSeries_of_forall_radicalCoefficient_eq_zero ψ _hψ ω
    _hω W _hW _hWω _hsum _hcont' g
    (LanglandsTunnell.CubicInduction.radicalCoefficient_eq_zero_of_forall_mem_converseCongruenceSet3 ψ _hψ S _hψS
      a _ha ω _hω _hωa W _hW _hWω _hWK _hWl _hsum _hsum' _hcont' _hV g hg)

#print axioms solution

end S_LanglandsTunnell_CubicInduction_mirabolicSeries_eq_dual_of_radicalCoefficient_eq
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_mirabolicSeries_eq_dual_of_radicalCoefficient_eq (solution)
