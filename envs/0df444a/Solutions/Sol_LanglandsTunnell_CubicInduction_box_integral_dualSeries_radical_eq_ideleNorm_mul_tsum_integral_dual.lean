-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.box_integral_dualSeries_radical_eq_ideleNorm_mul_tsum_integral_dual
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/ca740703-f0d4-5104-9a7f-6d9298bde0e7

import Definitions.Def_LanglandsTunnell_CubicInduction_AutomorphyDatum31
import Theorems.Thm_NumberField_AdelicFourier_norm_apply_eq_one_of_isGlobalAddChar
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_CubicInduction_box_integral_dualSeries_radical_eq_ideleNorm_mul_tsum_integral_dual

set_option autoImplicit false

open IsDedekindDomain NumberField NumberField.AdelicHaar AutomorphicForm Matrix MeasureTheory
open scoped NNReal ENNReal Pointwise ProbabilityTheory

attribute [local instance] NumberField.Idele.ideleBorel NumberField.AdelicHaar.adeleBorel

local notation "μbox" =>
  ProbabilityTheory.cond (NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ) (AdelicBox.adelicBox ℚ)

namespace LanglandsTunnell
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "lowerUnipotent21 longWeyl3 longWeyl3_coe dualWhittakerFn3 dualWhittakerFn3_apply weylPrime3 weylPrime3_mul_self transposeInv3_weylPrime3 weylPrime3_mul_transposeInv3_radicalP21_mul_weylPrime3 IsGL3PsiWhittakerFn transposeInv3 mirabolicTranslate AdelicGL upperUnipotent3 upperUnipotent3_coe radicalP21 embedMat2 iotaGL coe_iotaGL MirabolicIndex mirabolicRep mirabolicRep_spec mirabolic_mk_unipotent_mul diagUnitGL2 diagHom diagHom_apply"
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

section TransposeDual

variable {A : Type*} [CommRing A]

private theorem transposeInv3_mul (g h : GL (Fin 3) A) :
    transposeInv3 (g * h) = transposeInv3 g * transposeInv3 h := by
  refine Units.ext ?_
  change ((((g * h)⁻¹ : GL (Fin 3) A)) : Matrix (Fin 3) (Fin 3) A)ᵀ = _
  rw [_root_.mul_inv_rev, Units.val_mul, Matrix.transpose_mul]
  rfl

private theorem transposeInv3_one : transposeInv3 (1 : GL (Fin 3) A) = 1 := by
  refine Units.ext ?_
  change ((((1 : GL (Fin 3) A))⁻¹ : GL (Fin 3) A) : Matrix (Fin 3) (Fin 3) A)ᵀ = 1
  rw [inv_one, Units.val_one, Matrix.transpose_one]

private theorem transposeInv3_transposeInv3 (g : GL (Fin 3) A) : transposeInv3 (transposeInv3 g) = g := by
  refine Units.ext ?_
  change ((((transposeInv3 g)⁻¹ : GL (Fin 3) A)) : Matrix (Fin 3) (Fin 3) A)ᵀ = _
  have h : ((((transposeInv3 g)⁻¹ : GL (Fin 3) A)) : Matrix (Fin 3) (Fin 3) A) =
      ((g : GL (Fin 3) A) : Matrix (Fin 3) (Fin 3) A)ᵀ := rfl
  rw [h, Matrix.transpose_transpose]

private theorem transposeInv3_longWeyl3 : transposeInv3 (longWeyl3 : GL (Fin 3) A) = longWeyl3 := by
  refine Units.ext ?_
  change ((((longWeyl3 : GL (Fin 3) A))⁻¹ : GL (Fin 3) A) : Matrix (Fin 3) (Fin 3) A)ᵀ = _
  have h : ((((longWeyl3 : GL (Fin 3) A))⁻¹ : GL (Fin 3) A) : Matrix (Fin 3) (Fin 3) A) =
      !![0, 0, 1; 0, 1, 0; 1, 0, 0] := rfl
  rw [h, longWeyl3_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.transpose_apply]

private theorem longWeyl3_mul_self : (longWeyl3 : GL (Fin 3) A) * longWeyl3 = 1 := by
  refine Units.ext ?_
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_three]

private theorem longWeyl3_mul_transposeInv3_upperUnipotent3_mul_longWeyl3 (x y z : A) :
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

private theorem longWeyl3_mul_transposeInv3_upperUnipotent3 (x y z : A) :
    (longWeyl3 * transposeInv3 (upperUnipotent3 x y z) : GL (Fin 3) A) =
      upperUnipotent3 (-y) (-x) (x * y - z) * longWeyl3 := by
  rw [← longWeyl3_mul_transposeInv3_upperUnipotent3_mul_longWeyl3, mul_assoc, longWeyl3_mul_self, mul_one]

private theorem isGL3PsiWhittakerFn_dualWhittakerFn3 {R : Type*} [CommRing R] (ψ : AddChar A R)
    {W : GL (Fin 3) A → R} (hW : IsGL3PsiWhittakerFn ψ W) :
    IsGL3PsiWhittakerFn ψ⁻¹ (dualWhittakerFn3 W) := by
  intro x y z g
  rw [dualWhittakerFn3_apply, dualWhittakerFn3_apply, transposeInv3_mul, ← mul_assoc,
    AddChar.inv_apply, longWeyl3_mul_transposeInv3_upperUnipotent3, mul_assoc,
    hW (-y) (-x) (x * y - z) (longWeyl3 * transposeInv3 g), show -y + -x = -(x + y) by ring]

private theorem dualWhittakerFn3_dualWhittakerFn3 {R : Type*} (W : GL (Fin 3) A → R) :
    dualWhittakerFn3 (dualWhittakerFn3 W) = W := by
  funext g
  rw [dualWhittakerFn3_apply, dualWhittakerFn3_apply, transposeInv3_mul, transposeInv3_longWeyl3,
    transposeInv3_transposeInv3, ← mul_assoc, longWeyl3_mul_self, one_mul]

private theorem dualWhittakerFn3_apply_mul_weylPrime3_mul_transposeInv3 {R : Type*} (W : GL (Fin 3) A → R)
    (h g : GL (Fin 3) A) :
    dualWhittakerFn3 W (h * (weylPrime3 * transposeInv3 g)) =
      W (longWeyl3 * transposeInv3 h * weylPrime3 * g) := by
  rw [dualWhittakerFn3_apply, transposeInv3_mul, transposeInv3_mul, transposeInv3_weylPrime3,
    transposeInv3_transposeInv3, ← mul_assoc, ← mul_assoc]

end TransposeDual

section Transport

variable {A : Type*} [CommRing A]

private theorem iotaGL_mul_upperUnipotent3_zero (h : GL (Fin 2) A) (y z : A) :
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
  simpa using iotaGL_mul_upperUnipotent3_zero h t 0

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

private theorem weylPrime3_mul_transposeInv3_radicalP21_mul_weylPrime3_eq (v : Fin 2 → A) :
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
  have h5 := weylPrime3_mul_transposeInv3_radicalP21_mul_weylPrime3_eq (A := A) ![z, y]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h5
  have hww : ∀ X : GL (Fin 3) A, weylPrime3 * (weylPrime3 * X) = X := fun X => by
    rw [← mul_assoc, weylPrime3_mul_self, one_mul]
  rw [transposeInv3_mul, transposeInv3_mul, transposeInv3_iotaGL_diagUnitGL2, ← h5]
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
  have hdual := isGL3PsiWhittakerFn_dualWhittakerFn3 ψ hW
  rw [weylPrime3_mul_transposeInv3_radicalP21_mul_diag_mul, lowerUnipotent21_mul_upperUnipotent3_comm, mul_assoc]
  show dualWhittakerFn3 W (iotaGL (globalPoints (𝓞 ℚ) ℚ (mirabolicRep ℚ i)) * _) =
    _ * dualWhittakerFn3 W (iotaGL (globalPoints (𝓞 ℚ) ℚ (mirabolicRep ℚ i)) * _)
  rw [whittaker_iotaGL_mul_upperUnipotent3_mul ψ⁻¹ hdual, AddChar.inv_apply, mul_neg, neg_neg]

end Terms

section YStep

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

private theorem setIntegral_adelicBox_addChar_mul_eq_zero {ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ}
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

private theorem integral_box_phase_eq_zero {ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ} (hψ : IsGlobalAddChar ℚ ψ)
    {β : ℚ} (hβ : β ≠ 0) :
    ∫ y, ψ (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) β * y) ∂μbox = 0 := by
  rw [ProbabilityTheory.cond, integral_smul_measure, setIntegral_adelicBox_addChar_mul_eq_zero hψ hβ, smul_zero]

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

section Fibre

variable {K : Type*} [Field K]

private def mirabolicMat (α : Kˣ) (c : K) : GL (Fin 2) K where
  val := !![(α : K), 0; c, 1]
  inv := !![((α⁻¹ : Kˣ) : K), 0; -(c * ((α⁻¹ : Kˣ) : K)), 1]
  val_inv := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, mul_left_comm, α.ne_zero]
  inv_val := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, mul_comm, mul_left_comm, α.ne_zero]

@[scoped simp] private theorem mirabolicMat_coe (α : Kˣ) (c : K) :
    ((mirabolicMat α c : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = !![(α : K), 0; c, 1] :=
  rfl

private theorem unipotentGL2_mul_apply_one (x : K) (g : GL (Fin 2) K) (j : Fin 2) :
    ((AutomorphicForm.unipotentGL2 x * g : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 1 j =
      (g : Matrix (Fin 2) (Fin 2) K) 1 j := by
  fin_cases j <;> simp [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two]

private theorem eq_unipotentGL2_mul_mirabolicMat (g : GL (Fin 2) K) (hg : (g : Matrix (Fin 2) (Fin 2) K) 1 1 = 1) :
    g = AutomorphicForm.unipotentGL2 ((g : Matrix (Fin 2) (Fin 2) K) 0 1) *
      mirabolicMat (Matrix.GeneralLinearGroup.det g) ((g : Matrix (Fin 2) (Fin 2) K) 1 0) := by
  refine Units.ext ?_
  have hdet : ((Matrix.GeneralLinearGroup.det g : Kˣ) : K) =
      (g : Matrix (Fin 2) (Fin 2) K) 0 0 -
        (g : Matrix (Fin 2) (Fin 2) K) 0 1 * (g : Matrix (Fin 2) (Fin 2) K) 1 0 := by
    rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two, hg, mul_one]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two, hdet, hg]

private def mirabolicIdx (α : Kˣ) (c : K) : MirabolicIndex K :=
  Quotient.mk _ (mirabolicMat α c)

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

private theorem mirabolicRep_mirabolicIdx_apply_one_one (α : Kˣ) (c : K) :
    ((mirabolicRep K (mirabolicIdx α c) : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 1 1 = 1 := by
  obtain ⟨x, hx⟩ := exists_mirabolicRep_mk_eq (mirabolicMat α c)
  rw [mirabolicIdx, hx, unipotentGL2_mul_apply_one, mirabolicMat_coe]
  simp

private theorem mirabolicRep_mirabolicIdx_apply_one_zero (α : Kˣ) (c : K) :
    ((mirabolicRep K (mirabolicIdx α c) : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 1 0 = c := by
  obtain ⟨x, hx⟩ := exists_mirabolicRep_mk_eq (mirabolicMat α c)
  rw [mirabolicIdx, hx, unipotentGL2_mul_apply_one, mirabolicMat_coe]
  simp

private theorem det_mirabolicRep_mirabolicIdx (α : Kˣ) (c : K) :
    Matrix.GeneralLinearGroup.det (mirabolicRep K (mirabolicIdx α c)) = α := by
  obtain ⟨x, hx⟩ := exists_mirabolicRep_mk_eq (mirabolicMat α c)
  refine Units.ext ?_
  rw [mirabolicIdx, hx, Matrix.GeneralLinearGroup.val_det_apply, Units.val_mul, Matrix.det_mul,
    Matrix.det_fin_two, Matrix.det_fin_two]
  simp

private noncomputable def mirabolicFibreEquiv :
    {i : MirabolicIndex K // ((mirabolicRep K i : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 1 1 = 1} ≃ Kˣ × K where
  toFun i := (Matrix.GeneralLinearGroup.det (mirabolicRep K i.1),
    ((mirabolicRep K i.1 : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 1 0)
  invFun p := ⟨mirabolicIdx p.1 p.2, mirabolicRep_mirabolicIdx_apply_one_one p.1 p.2⟩
  left_inv i := by
    apply Subtype.ext
    change mirabolicIdx _ _ = i.1
    rw [mirabolicIdx]
    conv_rhs => rw [← mirabolicRep_spec K i.1, eq_unipotentGL2_mul_mirabolicMat (mirabolicRep K i.1) i.2,
      mirabolic_mk_unipotent_mul]
  right_inv p := by
    ext
    · exact congrArg Units.val (det_mirabolicRep_mirabolicIdx p.1 p.2)
    · exact mirabolicRep_mirabolicIdx_apply_one_zero p.1 p.2

private theorem tsum_fibre_eq_tsum_prod (f : MirabolicIndex K → ℂ) :
    ∑' i : {i : MirabolicIndex K // ((mirabolicRep K i : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 1 1 = 1}, f i.1 =
      ∑' p : Kˣ × K, f (mirabolicIdx p.1 p.2) :=
  (Equiv.tsum_eq (mirabolicFibreEquiv (K := K)).symm fun i => f i.1).symm

end Fibre

section Reindex

private theorem tsum_ite_rep_eq_tsum_prod (F : MirabolicIndex ℚ → ℂ) :
    (∑' i : MirabolicIndex ℚ,
        if ((mirabolicRep ℚ i : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) 1 1 = 1 then F i else 0) =
      ∑' p : ℚˣ × ℚ, F (mirabolicIdx p.1 p.2) := by
  have h := tsum_subtype
    {i : MirabolicIndex ℚ | ((mirabolicRep ℚ i : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) 1 1 = 1} F
  simp only [Set.indicator_apply, Set.mem_setOf_eq] at h
  rw [← h]
  exact tsum_fibre_eq_tsum_prod F

private theorem iotaGL_globalPoints_unipotentGL2 (x : ℚ) :
    iotaGL (globalPoints (𝓞 ℚ) ℚ (AutomorphicForm.unipotentGL2 x)) =
      upperUnipotent3 (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) x) 0 0 := by
  refine Units.ext ?_
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [coe_iotaGL, embedMat2, globalPoints, Matrix.GeneralLinearGroup.map_apply]

private theorem iotaGL_globalPoints_mirabolicMat_mul (α : ℚˣ) (c : ℚ) (z : AdeleRing (𝓞 ℚ) ℚ)
    (a : (AdeleRing (𝓞 ℚ) ℚ)ˣ) :
    iotaGL (globalPoints (𝓞 ℚ) ℚ (mirabolicMat α c)) * lowerUnipotent21 (-z) * iotaGL (diagUnitGL2 a⁻¹) =
      iotaGL (diagUnitGL2 (Units.map (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ)) α * a⁻¹)) *
        lowerUnipotent21 ((algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) c - z) *
          ((a⁻¹ : (AdeleRing (𝓞 ℚ) ℚ)ˣ) : AdeleRing (𝓞 ℚ) ℚ)) := by
  refine Units.ext ?_
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_three, coe_iotaGL, embedMat2, globalPoints,
      Matrix.GeneralLinearGroup.map_apply, Algebra.smul_def, Matrix.vecHead, Matrix.vecTail, Pi.mul_apply,
      Pi.algebraMap_apply, sub_eq_neg_add, add_comm]

private theorem class_term_eq {ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ} (hψ : IsGlobalAddChar ℚ ψ)
    {W : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ} (hW : IsGL3PsiWhittakerFn ψ W) (α : ℚˣ) (c : ℚ) (z : AdeleRing (𝓞 ℚ) ℚ)
    (a : (AdeleRing (𝓞 ℚ) ℚ)ˣ) (Y : AdelicGL 3 (𝓞 ℚ) ℚ) :
    dualWhittakerFn3 W (mirabolicTranslate (mirabolicIdx α c) *
      (lowerUnipotent21 (-z) * (iotaGL (diagUnitGL2 a⁻¹) * Y))) =
      dualWhittakerFn3 W (iotaGL (diagUnitGL2 (Units.map (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ)) α * a⁻¹)) *
        lowerUnipotent21 ((algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) c - z) *
          ((a⁻¹ : (AdeleRing (𝓞 ℚ) ℚ)ˣ) : AdeleRing (𝓞 ℚ) ℚ)) * Y) := by
  have hdual := isGL3PsiWhittakerFn_dualWhittakerFn3 ψ hW
  obtain ⟨x, hx⟩ := exists_mirabolicRep_mk_eq (mirabolicMat α c)
  show dualWhittakerFn3 W (iotaGL (globalPoints (𝓞 ℚ) ℚ (mirabolicRep ℚ (mirabolicIdx α c))) * _) = _
  rw [mirabolicIdx, hx, map_mul, map_mul, iotaGL_globalPoints_unipotentGL2, mul_assoc, hdual, add_zero,
    AddChar.inv_apply, ← map_neg, hψ.principalInvariant, one_mul, ← mul_assoc, ← mul_assoc,
    iotaGL_globalPoints_mirabolicMat_mul]

private theorem tsum_ite_rep_eq {ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ} (hψ : IsGlobalAddChar ℚ ψ)
    {W : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ} (hW : IsGL3PsiWhittakerFn ψ W) (g : AdelicGL 3 (𝓞 ℚ) ℚ)
    (a : (AdeleRing (𝓞 ℚ) ℚ)ˣ) (z : AdeleRing (𝓞 ℚ) ℚ) :
    (∑' i : MirabolicIndex ℚ,
        if ((mirabolicRep ℚ i : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) 1 1 = 1 then
          dualWhittakerFn3 W (mirabolicTranslate i *
            (lowerUnipotent21 (-z) * (iotaGL (diagUnitGL2 a⁻¹) * (weylPrime3 * transposeInv3 g))))
        else 0) =
      ∑' p : ℚˣ × ℚ,
        dualWhittakerFn3 W (iotaGL (diagUnitGL2 (Units.map (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ)) p.1 * a⁻¹)) *
          lowerUnipotent21 ((algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) p.2 - z) *
            ((a⁻¹ : (AdeleRing (𝓞 ℚ) ℚ)ˣ) : AdeleRing (𝓞 ℚ) ℚ)) *
          (weylPrime3 * transposeInv3 g)) := by
  rw [tsum_ite_rep_eq_tsum_prod]
  exact tsum_congr fun p => class_term_eq hψ hW p.1 p.2 z a _

end Reindex

section Measure

private theorem regular_adelicAddHaar_rat' : (adelicAddHaar (𝓞 ℚ) ℚ).Regular := by
  haveI := borelSpace_adeleBorel (𝓞 ℚ) ℚ
  exact Measure.regular_addHaarMeasure

private theorem map_inv_smul_adelicAddHaar_rat' (b : (AdeleRing (𝓞 ℚ) ℚ)ˣ) :
    (adelicAddHaar (𝓞 ℚ) ℚ).map (fun x : AdeleRing (𝓞 ℚ) ℚ => b⁻¹ • x) =
      (distribHaarChar (AdeleRing (𝓞 ℚ) ℚ) b : ℝ≥0) • adelicAddHaar (𝓞 ℚ) ℚ := by
  haveI := borelSpace_adeleBorel (𝓞 ℚ) ℚ
  haveI := isAddHaarMeasure_adelicAddHaar (𝓞 ℚ) ℚ
  haveI := regular_adelicAddHaar_rat'
  have hm : Measurable (fun x : AdeleRing (𝓞 ℚ) ℚ => b⁻¹ • x) := (continuous_const_smul _).measurable
  ext s hs
  rw [Measure.map_apply hm hs]
  simp only [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul]
  rw [distribHaarChar_mul (adelicAddHaar (𝓞 ℚ) ℚ) b s]
  congr 1
  ext x
  simp [Set.mem_smul_set_iff_inv_smul_mem]

private theorem integral_comp_inv_smul' (b : (AdeleRing (𝓞 ℚ) ℚ)ˣ) (f : AdeleRing (𝓞 ℚ) ℚ → ℂ) :
    ∫ x, f (b⁻¹ • x) ∂adelicAddHaar (𝓞 ℚ) ℚ =
      (TateGlobal.ideleNorm ℚ b : ℂ) * ∫ x, f x ∂adelicAddHaar (𝓞 ℚ) ℚ := by
  haveI := borelSpace_adeleBorel (𝓞 ℚ) ℚ
  have h := integral_map_equiv (MeasurableEquiv.smul (b⁻¹ : (AdeleRing (𝓞 ℚ) ℚ)ˣ)) f (μ := adelicAddHaar (𝓞 ℚ) ℚ)
  have hcoe : (⇑(MeasurableEquiv.smul (b⁻¹ : (AdeleRing (𝓞 ℚ) ℚ)ˣ) : AdeleRing (𝓞 ℚ) ℚ ≃ᵐ AdeleRing (𝓞 ℚ) ℚ)) =
      fun x : AdeleRing (𝓞 ℚ) ℚ => b⁻¹ • x := by
    funext x
    simp
  rw [hcoe, map_inv_smul_adelicAddHaar_rat', integral_smul_nnreal_measure, NNReal.smul_def,
    Complex.real_smul] at h
  rw [← h]
  rfl

private theorem lintegral_comp_inv_smul' (b : (AdeleRing (𝓞 ℚ) ℚ)ˣ) (F : AdeleRing (𝓞 ℚ) ℚ → ℝ≥0∞) :
    ∫⁻ x, F (b⁻¹ • x) ∂adelicAddHaar (𝓞 ℚ) ℚ =
      (distribHaarChar (AdeleRing (𝓞 ℚ) ℚ) b : ℝ≥0∞) * ∫⁻ x, F x ∂adelicAddHaar (𝓞 ℚ) ℚ := by
  haveI := borelSpace_adeleBorel (𝓞 ℚ) ℚ
  have h := lintegral_map_equiv F (MeasurableEquiv.smul (b⁻¹ : (AdeleRing (𝓞 ℚ) ℚ)ˣ)) (μ := adelicAddHaar (𝓞 ℚ) ℚ)
  have hcoe : (⇑(MeasurableEquiv.smul (b⁻¹ : (AdeleRing (𝓞 ℚ) ℚ)ˣ) : AdeleRing (𝓞 ℚ) ℚ ≃ᵐ AdeleRing (𝓞 ℚ) ℚ)) =
      fun x : AdeleRing (𝓞 ℚ) ℚ => b⁻¹ • x := by
    funext x
    simp
  rw [hcoe, map_inv_smul_adelicAddHaar_rat', ENNReal.smul_def, lintegral_smul_measure] at h
  exact h.symm

private theorem distribHaarChar_neg (a : (AdeleRing (𝓞 ℚ) ℚ)ˣ) :
    distribHaarChar (AdeleRing (𝓞 ℚ) ℚ) (-a) = distribHaarChar (AdeleRing (𝓞 ℚ) ℚ) a := by
  have hsq : distribHaarChar (AdeleRing (𝓞 ℚ) ℚ) (-1 : (AdeleRing (𝓞 ℚ) ℚ)ˣ) *
      distribHaarChar (AdeleRing (𝓞 ℚ) ℚ) (-1 : (AdeleRing (𝓞 ℚ) ℚ)ˣ) = 1 := by
    rw [← map_mul, neg_one_mul, neg_neg, map_one]
  have h1 : distribHaarChar (AdeleRing (𝓞 ℚ) ℚ) (-1 : (AdeleRing (𝓞 ℚ) ℚ)ˣ) = 1 := by
    have h' : ((distribHaarChar (AdeleRing (𝓞 ℚ) ℚ) (-1 : (AdeleRing (𝓞 ℚ) ℚ)ˣ) : ℝ≥0) : ℝ) *
        ((distribHaarChar (AdeleRing (𝓞 ℚ) ℚ) (-1 : (AdeleRing (𝓞 ℚ) ℚ)ˣ) : ℝ≥0) : ℝ) = 1 := by
      exact_mod_cast hsq
    rcases mul_self_eq_one_iff.mp h' with h | h
    · exact_mod_cast h
    · exfalso
      have := (distribHaarChar (AdeleRing (𝓞 ℚ) ℚ) (-1 : (AdeleRing (𝓞 ℚ) ℚ)ˣ)).coe_nonneg
      linarith
  have hneg : -a = (-1 : (AdeleRing (𝓞 ℚ) ℚ)ˣ) * a := (neg_one_mul a).symm
  rw [hneg, map_mul, h1, one_mul]

private theorem ideleNorm_neg (a : (AdeleRing (𝓞 ℚ) ℚ)ˣ) : TateGlobal.ideleNorm ℚ (-a) = TateGlobal.ideleNorm ℚ a := by
  unfold TateGlobal.ideleNorm
  rw [distribHaarChar_neg]

private theorem neg_mul_inv_eq_smul (a : (AdeleRing (𝓞 ℚ) ℚ)ˣ) (t : AdeleRing (𝓞 ℚ) ℚ) :
    -t * ((a⁻¹ : (AdeleRing (𝓞 ℚ) ℚ)ˣ) : AdeleRing (𝓞 ℚ) ℚ) = (-a)⁻¹ • t := by
  have hinv : (-a)⁻¹ = -a⁻¹ := inv_eq_of_mul_eq_one_right (by rw [neg_mul_neg, mul_inv_cancel])
  rw [Units.smul_def, hinv, Units.val_neg]
  ring

private theorem integral_comp_neg_mul_inv (a : (AdeleRing (𝓞 ℚ) ℚ)ˣ) (f : AdeleRing (𝓞 ℚ) ℚ → ℂ) :
    ∫ t, f (-t * ((a⁻¹ : (AdeleRing (𝓞 ℚ) ℚ)ˣ) : AdeleRing (𝓞 ℚ) ℚ)) ∂adelicAddHaar (𝓞 ℚ) ℚ =
      (TateGlobal.ideleNorm ℚ a : ℂ) * ∫ x, f x ∂adelicAddHaar (𝓞 ℚ) ℚ := by
  simp_rw [neg_mul_inv_eq_smul]
  rw [integral_comp_inv_smul' (-a) f, ideleNorm_neg]

private theorem lintegral_comp_neg_mul_inv (a : (AdeleRing (𝓞 ℚ) ℚ)ˣ) (F : AdeleRing (𝓞 ℚ) ℚ → ℝ≥0∞) :
    ∫⁻ t, F (-t * ((a⁻¹ : (AdeleRing (𝓞 ℚ) ℚ)ˣ) : AdeleRing (𝓞 ℚ) ℚ)) ∂adelicAddHaar (𝓞 ℚ) ℚ =
      (distribHaarChar (AdeleRing (𝓞 ℚ) ℚ) a : ℝ≥0∞) * ∫⁻ x, F x ∂adelicAddHaar (𝓞 ℚ) ℚ := by
  simp_rw [neg_mul_inv_eq_smul]
  rw [lintegral_comp_inv_smul' (-a) F, distribHaarChar_neg]

private noncomputable def principalEquiv : ℚ ≃ AdeleRing.principalSubgroup (𝓞 ℚ) ℚ :=
  Equiv.ofBijective (fun k => ⟨algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) k, RingHom.mem_range_self _ k⟩)
    ⟨fun k l h => AdeleRing.algebraMap_injective (𝓞 ℚ) ℚ (congrArg Subtype.val h),
      fun x => by
        obtain ⟨k, hk⟩ := RingHom.mem_range.mp x.2
        exact ⟨k, Subtype.ext hk⟩⟩

private theorem coe_principalEquiv (k : ℚ) :
    ((principalEquiv k : AdeleRing.principalSubgroup (𝓞 ℚ) ℚ)
      : AdeleRing (𝓞 ℚ) ℚ) = algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) k :=
  rfl

private scoped instance : Countable (AdeleRing.principalSubgroup (𝓞 ℚ) ℚ) := Countable.of_equiv ℚ principalEquiv

private scoped instance : VAddInvariantMeasure (AdeleRing.principalSubgroup (𝓞 ℚ) ℚ) (AdeleRing (𝓞 ℚ) ℚ)
    (adelicAddHaar (𝓞 ℚ) ℚ) where
  measure_preimage_vadd c s _ := by
    haveI := borelSpace_adeleBorel (𝓞 ℚ) ℚ
    haveI := isAddHaarMeasure_adelicAddHaar (𝓞 ℚ) ℚ
    show adelicAddHaar (𝓞 ℚ) ℚ ((fun x : AdeleRing (𝓞 ℚ) ℚ => (c : AdeleRing (𝓞 ℚ) ℚ) + x) ⁻¹' s) = _
    exact measure_preimage_add _ _ _

private scoped instance : Countable ℚˣ :=
  Function.Injective.countable
    (fun a b (h : (a : ℚ) = (b : ℚ)) => Units.ext h : Function.Injective (Units.val : ℚˣ → ℚ))

private scoped instance : MeasurableConstVAdd (AdeleRing.principalSubgroup (𝓞 ℚ) ℚ) (AdeleRing (𝓞 ℚ) ℚ) where
  measurable_const_vadd c := by
    haveI := borelSpace_adeleBorel (𝓞 ℚ) ℚ
    show Measurable fun x : AdeleRing (𝓞 ℚ) ℚ => (c : AdeleRing (𝓞 ℚ) ℚ) + x
    exact measurable_const_add _

private theorem tsum_setLIntegral_box_sub (F : AdeleRing (𝓞 ℚ) ℚ → ℝ≥0∞) :
    ∑' c : ℚ, ∫⁻ z in AdelicBox.adelicBox ℚ, F (z - algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) c) ∂adelicAddHaar (𝓞 ℚ) ℚ =
      ∫⁻ z, F z ∂adelicAddHaar (𝓞 ℚ) ℚ := by
  rw [(AdelicBox.isAddFundamentalDomain_adelicBox ℚ (adelicAddHaar (𝓞 ℚ) ℚ)).lintegral_eq_tsum' F,
    ← principalEquiv.tsum_eq]
  refine tsum_congr fun c => ?_
  congr 1
  funext z
  show F (z - algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) c) =
    F (((-principalEquiv c : AdeleRing.principalSubgroup (𝓞 ℚ) ℚ) : AdeleRing (𝓞 ℚ) ℚ) + z)
  rw [AddSubgroup.coe_neg, coe_principalEquiv, neg_add_eq_sub]

private theorem tsum_setIntegral_box_sub {H : AdeleRing (𝓞 ℚ) ℚ → ℂ} (hH : Integrable H (adelicAddHaar (𝓞 ℚ) ℚ)) :
    ∑' c : ℚ, ∫ z in AdelicBox.adelicBox ℚ, H (z - algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) c) ∂adelicAddHaar (𝓞 ℚ) ℚ =
      ∫ z, H z ∂adelicAddHaar (𝓞 ℚ) ℚ := by
  rw [(AdelicBox.isAddFundamentalDomain_adelicBox ℚ (adelicAddHaar (𝓞 ℚ) ℚ)).integral_eq_tsum' H hH,
    ← principalEquiv.tsum_eq]
  refine tsum_congr fun c => ?_
  congr 1
  funext z
  show H (z - algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) c) =
    H (((-principalEquiv c : AdeleRing.principalSubgroup (𝓞 ℚ) ℚ) : AdeleRing (𝓞 ℚ) ℚ) + z)
  rw [AddSubgroup.coe_neg, coe_principalEquiv, neg_add_eq_sub]

private theorem integral_cond_box (f : AdeleRing (𝓞 ℚ) ℚ → ℂ) :
    ∫ z, f z ∂μbox =
      ((adelicAddHaar (𝓞 ℚ) ℚ (AdelicBox.adelicBox ℚ)).toReal)⁻¹ •
        ∫ z in AdelicBox.adelicBox ℚ, f z ∂adelicAddHaar (𝓞 ℚ) ℚ := by
  rw [ProbabilityTheory.cond, integral_smul_measure, ENNReal.toReal_inv]

end Measure

section Continuity

variable {A : Type*} [CommRing A] [TopologicalSpace A]

private theorem continuous_transposeInv3' : Continuous (transposeInv3 : GL (Fin 3) A → GL (Fin 3) A) := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · show Continuous fun g : GL (Fin 3) A => (((g⁻¹ : GL (Fin 3) A)) : Matrix (Fin 3) (Fin 3) A)ᵀ
    exact Units.continuous_coe_inv.matrix_transpose
  · show Continuous fun g : GL (Fin 3) A => (((g : GL (Fin 3) A)) : Matrix (Fin 3) (Fin 3) A)ᵀ
    exact Units.continuous_val.matrix_transpose

variable [IsTopologicalRing A]

private theorem continuous_lowerUnipotent21 : Continuous (lowerUnipotent21 : A → GL (Fin 3) A) := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · show Continuous fun x : A => (!![1, 0, 0; x, 1, 0; 0, 0, 1] : Matrix (Fin 3) (Fin 3) A)
    refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp <;> fun_prop
  · show Continuous fun x : A => (!![1, 0, 0; -x, 1, 0; 0, 0, 1] : Matrix (Fin 3) (Fin 3) A)
    refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp <;> fun_prop

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

private theorem continuous_radicalP21_left (y : A) : Continuous fun z : A => radicalP21 ![z, y] := by
  show Continuous fun z : A => upperUnipotent3 0 y z
  exact continuous_upperUnipotent3_of continuous_const continuous_const continuous_id

private theorem continuous_radicalP21_right (z : A) : Continuous fun y : A => radicalP21 ![z, y] := by
  show Continuous fun y : A => upperUnipotent3 0 y z
  exact continuous_upperUnipotent3_of continuous_const continuous_id continuous_const

private theorem continuous_dualWhittakerFn3' {R : Type*} [TopologicalSpace R] {W : GL (Fin 3) A → R}
    (hW : Continuous W) : Continuous (dualWhittakerFn3 W) := by
  show Continuous fun g : GL (Fin 3) A => W (longWeyl3 * transposeInv3 g)
  exact hW.comp ((continuous_const_mul (longWeyl3 : GL (Fin 3) A)).comp continuous_transposeInv3')

private theorem continuous_dual_diag_lowerUnipotent21 {R : Type*} [TopologicalSpace R] {W : GL (Fin 3) A → R}
    (hW : Continuous W) (b : Aˣ) (Y : GL (Fin 3) A) :
    Continuous fun x : A => dualWhittakerFn3 W (iotaGL (diagUnitGL2 b) * lowerUnipotent21 x * Y) :=
  (continuous_dualWhittakerFn3' hW).comp ((continuous_const.mul continuous_lowerUnipotent21).mul continuous_const)

private theorem continuous_dual_term_radical_left {R : Type*} [TopologicalSpace R] {W : GL (Fin 3) A → R}
    (hW : Continuous W) (m X : GL (Fin 3) A) (y : A) :
    Continuous fun z : A =>
      dualWhittakerFn3 W (m * (weylPrime3 * transposeInv3 (radicalP21 ![z, y] * X))) :=
  (continuous_dualWhittakerFn3' hW).comp (continuous_const.mul (continuous_const.mul
    (continuous_transposeInv3'.comp ((continuous_radicalP21_left y).mul continuous_const))))

private theorem continuous_dual_term_radical_right {R : Type*} [TopologicalSpace R] {W : GL (Fin 3) A → R}
    (hW : Continuous W) (m X : GL (Fin 3) A) (z : A) :
    Continuous fun y : A =>
      dualWhittakerFn3 W (m * (weylPrime3 * transposeInv3 (radicalP21 ![z, y] * X))) :=
  (continuous_dualWhittakerFn3' hW).comp (continuous_const.mul (continuous_const.mul
    (continuous_transposeInv3'.comp ((continuous_radicalP21_right z).mul continuous_const))))

end Continuity

section ZStep

variable (W : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (g : AdelicGL 3 (𝓞 ℚ) ℚ) (a : (AdeleRing (𝓞 ℚ) ℚ)ˣ)

private noncomputable def dualPoint (α : ℚˣ) (x : AdeleRing (𝓞 ℚ) ℚ) : ℂ :=
  dualWhittakerFn3 W (iotaGL (diagUnitGL2 (Units.map (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ)) α * a⁻¹)) *
    lowerUnipotent21 x * (weylPrime3 * transposeInv3 g))

variable {W}

private theorem continuous_dualPoint (hWc : Continuous W) (α : ℚˣ) : Continuous (dualPoint W g a α) :=
  (continuous_dualWhittakerFn3' hWc).comp ((continuous_const.mul continuous_lowerUnipotent21).mul continuous_const)

private theorem dualPoint_sub_mul (α : ℚˣ) (c : ℚ) (z : AdeleRing (𝓞 ℚ) ℚ) :
    dualPoint W g a α ((algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) c - z) * ((a⁻¹ : (AdeleRing (𝓞 ℚ) ℚ)ˣ) : AdeleRing (𝓞 ℚ) ℚ)) =
      dualPoint W g a α (-(z - algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) c) *
        ((a⁻¹ : (AdeleRing (𝓞 ℚ) ℚ)ˣ) : AdeleRing (𝓞 ℚ) ℚ)) := by
  rw [neg_sub]

variable {g a}

private theorem tsum_lintegral_unfolded_ne_top
    (hfin : (∑' α : ℚˣ, ∫⁻ x, (‖dualPoint W g a α x‖₊ : ℝ≥0∞) ∂adelicAddHaar (𝓞 ℚ) ℚ) < ⊤) :
    (∑' p : ℚˣ × ℚ, ∫⁻ z in AdelicBox.adelicBox ℚ,
        (‖dualPoint W g a p.1 (-(z - algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) p.2) *
          ((a⁻¹ : (AdeleRing (𝓞 ℚ) ℚ)ˣ) : AdeleRing (𝓞 ℚ) ℚ))‖₊ : ℝ≥0∞) ∂adelicAddHaar (𝓞 ℚ) ℚ) ≠ ⊤ := by
  have h : ∀ α : ℚˣ, (∑' c : ℚ, ∫⁻ z in AdelicBox.adelicBox ℚ,
      (‖dualPoint W g a α (-(z - algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) c) *
        ((a⁻¹ : (AdeleRing (𝓞 ℚ) ℚ)ˣ) : AdeleRing (𝓞 ℚ) ℚ))‖₊ : ℝ≥0∞) ∂adelicAddHaar (𝓞 ℚ) ℚ) =
      (distribHaarChar (AdeleRing (𝓞 ℚ) ℚ) a : ℝ≥0∞) *
        ∫⁻ x, (‖dualPoint W g a α x‖₊ : ℝ≥0∞) ∂adelicAddHaar (𝓞 ℚ) ℚ := by
    intro α
    rw [tsum_setLIntegral_box_sub (fun t => (‖dualPoint W g a α
      (-t * ((a⁻¹ : (AdeleRing (𝓞 ℚ) ℚ)ˣ) : AdeleRing (𝓞 ℚ) ℚ))‖₊ : ℝ≥0∞))]
    exact lintegral_comp_neg_mul_inv a fun x => (‖dualPoint W g a α x‖₊ : ℝ≥0∞)
  rw [ENNReal.tsum_prod']
  refine (tsum_congr fun α => h α).trans_ne ?_
  rw [ENNReal.tsum_mul_left]
  exact ENNReal.mul_ne_top ENNReal.coe_ne_top hfin.ne

private theorem integrable_unfolded (hWc : Continuous W)
    (hfin : (∑' α : ℚˣ, ∫⁻ x, (‖dualPoint W g a α x‖₊ : ℝ≥0∞) ∂adelicAddHaar (𝓞 ℚ) ℚ) < ⊤) (α : ℚˣ) :
    Integrable (fun t : AdeleRing (𝓞 ℚ) ℚ =>
      dualPoint W g a α (-t * ((a⁻¹ : (AdeleRing (𝓞 ℚ) ℚ)ˣ) : AdeleRing (𝓞 ℚ) ℚ))) (adelicAddHaar (𝓞 ℚ) ℚ) := by
  haveI := borelSpace_adeleBorel (𝓞 ℚ) ℚ
  refine ⟨((continuous_dualPoint g a hWc α).comp (continuous_neg.mul continuous_const)).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_enorm]
  simp_rw [enorm_eq_nnnorm]
  rw [lintegral_comp_neg_mul_inv a fun x => (‖dualPoint W g a α x‖₊ : ℝ≥0∞)]
  exact ENNReal.mul_lt_top ENNReal.coe_lt_top (ENNReal.lt_top_of_tsum_ne_top hfin.ne α)

private theorem integral_cond_tsum_unfolded (hWc : Continuous W)
    (hfin : (∑' α : ℚˣ, ∫⁻ x, (‖dualPoint W g a α x‖₊ : ℝ≥0∞) ∂adelicAddHaar (𝓞 ℚ) ℚ) < ⊤) :
    ∫ z, (∑' p : ℚˣ × ℚ, dualPoint W g a p.1
        ((algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) p.2 - z) * ((a⁻¹ : (AdeleRing (𝓞 ℚ) ℚ)ˣ) : AdeleRing (𝓞 ℚ) ℚ))) ∂μbox =
      ((adelicAddHaar (𝓞 ℚ) ℚ (AdelicBox.adelicBox ℚ)).toReal)⁻¹ •
        ((TateGlobal.ideleNorm ℚ a : ℂ) * ∑' α : ℚˣ, ∫ x, dualPoint W g a α x ∂adelicAddHaar (𝓞 ℚ) ℚ) := by
  haveI := borelSpace_adeleBorel (𝓞 ℚ) ℚ
  simp_rw [dualPoint_sub_mul]
  rw [integral_cond_box]
  congr 1
  have hmeas : ∀ p : ℚˣ × ℚ, AEStronglyMeasurable (fun z : AdeleRing (𝓞 ℚ) ℚ => dualPoint W g a p.1
      (-(z - algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) p.2) * ((a⁻¹ : (AdeleRing (𝓞 ℚ) ℚ)ˣ) : AdeleRing (𝓞 ℚ) ℚ)))
      ((adelicAddHaar (𝓞 ℚ) ℚ).restrict (AdelicBox.adelicBox ℚ)) := fun p =>
    ((continuous_dualPoint g a hWc p.1).comp ((continuous_id.sub continuous_const).neg.mul continuous_const))
      |>.aestronglyMeasurable
  rw [integral_tsum hmeas (tsum_lintegral_unfolded_ne_top hfin)]

  have hsumm : Summable fun p : ℚˣ × ℚ => ∫ z in AdelicBox.adelicBox ℚ, dualPoint W g a p.1
      (-(z - algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) p.2) * ((a⁻¹ : (AdeleRing (𝓞 ℚ) ℚ)ˣ) : AdeleRing (𝓞 ℚ) ℚ))
      ∂adelicAddHaar (𝓞 ℚ) ℚ := by
    refine Summable.of_norm_bounded (ENNReal.summable_toReal (tsum_lintegral_unfolded_ne_top hfin)) fun p => ?_
    refine (norm_integral_le_lintegral_norm
      (μ := (adelicAddHaar (𝓞 ℚ) ℚ).restrict (AdelicBox.adelicBox ℚ)) _).trans_eq ?_
    simp only [ofReal_norm, enorm_eq_nnnorm]
  rw [hsumm.tsum_prod, ← tsum_mul_left]
  exact tsum_congr fun α =>
    (tsum_setIntegral_box_sub
      (H := fun t => dualPoint W g a α (-t * ((a⁻¹ : (AdeleRing (𝓞 ℚ) ℚ)ˣ) : AdeleRing (𝓞 ℚ) ℚ)))
      (integrable_unfolded hWc hfin α)).trans (integral_comp_neg_mul_inv a (dualPoint W g a α))

end ZStep

section Main

private theorem box_integral_dualSeries_radical_eq_ideleNorm_mul_tsum_integral_dual'
    (ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ) (_hψ : IsGlobalAddChar ℚ ψ)
    (W : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (_hWc : Continuous W) (_hW : IsGL3PsiWhittakerFn ψ W)
    (_hsum' : ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ,
      Summable fun i : MirabolicIndex ℚ => dualWhittakerFn3 W (mirabolicTranslate i * g))
    (g : AdelicGL 3 (𝓞 ℚ) ℚ) (a : (AdeleRing (𝓞 ℚ) ℚ)ˣ)
    (_hfin : (∑' α : ℚˣ, ∫⁻ x : AdeleRing (𝓞 ℚ) ℚ,
        (‖dualWhittakerFn3 W (iotaGL (diagUnitGL2 (Units.map (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ)) α * a⁻¹)) *
            lowerUnipotent21 x * (weylPrime3 * transposeInv3 g))‖₊ : ENNReal)
          ∂(NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ)) < ⊤) :
    ((NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ (AdelicBox.adelicBox ℚ)).toReal : ℂ) *
      (∫ z : AdeleRing (𝓞 ℚ) ℚ, ∫ y : AdeleRing (𝓞 ℚ) ℚ,
          (∑' i : MirabolicIndex ℚ, dualWhittakerFn3 W (mirabolicTranslate i *
            (weylPrime3 * transposeInv3 (radicalP21 ![z, y] * (iotaGL (diagUnitGL2 a) * g))))) * ψ (-y)
        ∂(ProbabilityTheory.cond (NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ) (AdelicBox.adelicBox ℚ))
        ∂(ProbabilityTheory.cond (NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ) (AdelicBox.adelicBox ℚ))) =
    ((TateGlobal.ideleNorm ℚ a : ℝ) : ℂ) *
      ∑' α : ℚˣ, ∫ x : AdeleRing (𝓞 ℚ) ℚ,
        dualWhittakerFn3 W (iotaGL (diagUnitGL2 (Units.map (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ)) α * a⁻¹)) *
          lowerUnipotent21 x * (weylPrime3 * transposeInv3 g))
        ∂(NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ) := by
  have hy : ∀ z : AdeleRing (𝓞 ℚ) ℚ,
      (∫ y : AdeleRing (𝓞 ℚ) ℚ, (∑' i : MirabolicIndex ℚ, dualWhittakerFn3 W (mirabolicTranslate i *
          (weylPrime3 * transposeInv3 (radicalP21 ![z, y] * (iotaGL (diagUnitGL2 a) * g))))) * ψ (-y) ∂μbox) =
        ∑' p : ℚˣ × ℚ, dualPoint W g a p.1
          ((algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) p.2 - z) * ((a⁻¹ : (AdeleRing (𝓞 ℚ) ℚ)ˣ) : AdeleRing (𝓞 ℚ) ℚ)) :=
    fun z => (integral_box_dualSeries_radical _hψ _hW _hsum' g a z).trans (tsum_ite_rep_eq _hψ _hW g a z)
  have hfin' : (∑' α : ℚˣ, ∫⁻ x, (‖dualPoint W g a α x‖₊ : ℝ≥0∞) ∂adelicAddHaar (𝓞 ℚ) ℚ) < ⊤ := _hfin
  have hκ : (adelicAddHaar (𝓞 ℚ) ℚ (AdelicBox.adelicBox ℚ)).toReal ≠ 0 :=
    (ENNReal.toReal_pos (AdelicBox.adelicAddHaar_adelicBox_pos ℚ).ne'
      (AdelicBox.adelicAddHaar_adelicBox_lt_top ℚ).ne).ne'
  simp_rw [hy]
  rw [integral_cond_tsum_unfolded _hWc hfin', Complex.real_smul, Complex.ofReal_inv, mul_inv_cancel_left₀]
  · rfl
  · exact_mod_cast hκ

end Main

end LanglandsTunnell.CubicInduction
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_box_integral_dualSeries_radical_eq_ideleNorm_mul_tsum_integral_dual.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_box_integral_dualSeries_radical_eq_ideleNorm_mul_tsum_integral_dual.LanglandsTunnell.CubicInduction"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_box_integral_dualSeries_radical_eq_ideleNorm_mul_tsum_integral_dual.LanglandsTunnell"

p2m_open "IsDedekindDomain NumberField NumberField.TateGlobal AutomorphicForm LanglandsTunnell.Converse LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_box_integral_dualSeries_radical_eq_ideleNorm_mul_tsum_integral_dual.LanglandsTunnell.CubicInduction"

theorem solution
    (ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ) (_hψ : IsGlobalAddChar ℚ ψ)
    (W : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (_hWc : Continuous W) (_hW : IsGL3PsiWhittakerFn ψ W)
    (_hsum' : ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ,
      Summable fun i : MirabolicIndex ℚ => dualWhittakerFn3 W (mirabolicTranslate i * g))
    (g : AdelicGL 3 (𝓞 ℚ) ℚ) (a : (AdeleRing (𝓞 ℚ) ℚ)ˣ)
    (_hfin : (∑' α : ℚˣ, ∫⁻ x : AdeleRing (𝓞 ℚ) ℚ,
        (‖dualWhittakerFn3 W (iotaGL (diagUnitGL2 (Units.map (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ)) α * a⁻¹)) *
            lowerUnipotent21 x * (weylPrime3 * transposeInv3 g))‖₊ : ENNReal)
          ∂(NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ)) < ⊤) :
    ((NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ (AdelicBox.adelicBox ℚ)).toReal : ℂ) *
      (∫ z : AdeleRing (𝓞 ℚ) ℚ, ∫ y : AdeleRing (𝓞 ℚ) ℚ,
          (∑' i : MirabolicIndex ℚ, dualWhittakerFn3 W (mirabolicTranslate i *
            (weylPrime3 * transposeInv3 (radicalP21 ![z, y] * (iotaGL (diagUnitGL2 a) * g))))) * ψ (-y)
        ∂(ProbabilityTheory.cond (NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ) (AdelicBox.adelicBox ℚ))
        ∂(ProbabilityTheory.cond (NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ) (AdelicBox.adelicBox ℚ))) =
    ((TateGlobal.ideleNorm ℚ a : ℝ) : ℂ) *
      ∑' α : ℚˣ, ∫ x : AdeleRing (𝓞 ℚ) ℚ,
        dualWhittakerFn3 W (iotaGL (diagUnitGL2 (Units.map (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ)) α * a⁻¹)) *
          lowerUnipotent21 x * (weylPrime3 * transposeInv3 g))
        ∂(NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ) :=
  LanglandsTunnell.CubicInduction.box_integral_dualSeries_radical_eq_ideleNorm_mul_tsum_integral_dual'
    ψ _hψ W _hWc _hW _hsum' g a _hfin

#print axioms solution

end S_LanglandsTunnell_CubicInduction_box_integral_dualSeries_radical_eq_ideleNorm_mul_tsum_integral_dual
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_box_integral_dualSeries_radical_eq_ideleNorm_mul_tsum_integral_dual (solution)
