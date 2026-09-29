-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.SlabL2.hasDerivAt_integral_mul_comp_archRealLift3_smoothingKernel
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/ca7433fb-d148-5148-85b6-20798a390846

import Definitions.Def_LanglandsTunnell_CubicInduction_ArchCentre3
import Definitions.Def_LanglandsTunnell_CubicInduction_AutomorphyDatum31
import Definitions.Def_NumberField_StandardGlobalAddCharRat
import Definitions.Def_LanglandsTunnell_CubicInduction_SlabL2Cusp
import Definitions.Def_LanglandsTunnell_CubicInduction_ArchSmoothSpace3
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Theorems.Thm_LanglandsTunnell_CubicInduction_SlabL2_archDeriv_smoothingOperator
import Theorems.Thm_LanglandsTunnell_CubicInduction_SlabL2_continuous_and_isArchSmooth3_smoothingOperator
import Theorems.Thm_LanglandsTunnell_CubicInduction_WhittakerBlock_hasDerivAt_apply_mul_archRealLift3_of_isArchSmooth3
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_hasDerivAt_integral_mul_comp_archRealLift3_smoothingKernel
p2m_attr_erase "instance" "instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions"
p2m_attr_erase "simp" "ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply"

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm MeasureTheory
open LanglandsTunnell.CubicInduction LanglandsTunnell.CubicInduction.SlabL2

attribute [local instance] NumberField.AdelicHaar.glBorel

attribute [local instance] NumberField.AdelicHaar.borelSpace_glBorel

noncomputable section

namespace ADeriv

scoped instance : LocallyCompactSpace (Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) :=
  inferInstanceAs (LocallyCompactSpace (Fin 3 → Fin 3 → AdeleRing (𝓞 ℚ) ℚ))
scoped instance : T2Space (Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) :=
  inferInstanceAs (T2Space (Fin 3 → Fin 3 → AdeleRing (𝓞 ℚ) ℚ))
scoped instance : LocallyCompactSpace (AdelicGL 3 (𝓞 ℚ) ℚ) := inferInstance

def idArr : Fin 3 → Fin 3 → ℝ := fun a b => if a = b then (1 : ℝ) else 0

def elem (i j : Fin 3) : Fin 3 → Fin 3 → ℝ := fun a b => if a = i ∧ b = j then (1 : ℝ) else 0

theorem of_idArr : Matrix.of idArr = 1 := by
  ext a b; simp [idArr, Matrix.one_apply]

theorem det_idArr : (Matrix.of idArr).det ≠ 0 := by
  rw [of_idArr, Matrix.det_one]; exact one_ne_zero

theorem archRealLift3_idArr : WhittakerBlock.archRealLift3 idArr = 1 := by
  have h := LanglandsTunnell.CubicInduction.WhittakerBlock.archRealLift3_mul det_idArr det_idArr
  have hprod : (fun a b => (Matrix.of idArr * Matrix.of idArr) a b) = idArr := by
    funext a b; rw [of_idArr, Matrix.one_mul]; rfl
  rw [hprod] at h
  exact mul_left_cancel (a := WhittakerBlock.archRealLift3 idArr) (by rw [h, mul_one])

theorem direction_idArr (i j : Fin 3) :
    (fun a b : Fin 3 => if b = j then idArr a i else 0) = elem i j := by
  funext a b
  simp only [idArr, elem]
  by_cases ha : a = i <;> by_cases hb : b = j <;> simp [ha, hb]

theorem isOpen_invertible : IsOpen {e : Fin 3 → Fin 3 → ℝ | (Matrix.of e).det ≠ 0} :=
  isOpen_ne.preimage (Continuous.matrix_det (continuous_matrix fun a b =>
    (continuous_apply b).comp (continuous_apply a)))

theorem archDeriv_eq_fderiv_one {F : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ} (hF : WhittakerBlock.IsArchSmooth3 F)
    (i j : Fin 3) (k : AdelicGL 3 (𝓞 ℚ) ℚ) :
    WhittakerBlock.archDeriv i j F k =
      fderiv ℝ (fun e => F (k * WhittakerBlock.archRealLift3 e)) idArr (elem i j) := by
  have h := LanglandsTunnell.CubicInduction.WhittakerBlock.archDeriv_eq_fderiv hF i j k det_idArr
  rw [archRealLift3_idArr, mul_one, direction_idArr] at h
  exact h

def rotArr (c₁ c₂ : Fin 3) (s : ℝ) : Fin 3 → Fin 3 → ℝ := fun i j =>
  if i = c₁ ∧ j = c₁ then Real.cos s else if i = c₂ ∧ j = c₂ then Real.cos s else
  if i = c₁ ∧ j = c₂ then - Real.sin s else if i = c₂ ∧ j = c₁ then Real.sin s else
  if i = j then 1 else 0

def rotArr' (c₁ c₂ : Fin 3) (s : ℝ) : Fin 3 → Fin 3 → ℝ := fun i j =>
  if i = c₁ ∧ j = c₁ then - Real.sin s else if i = c₂ ∧ j = c₂ then - Real.sin s else
  if i = c₁ ∧ j = c₂ then - Real.cos s else if i = c₂ ∧ j = c₁ then Real.cos s else 0

theorem hasDerivAt_rotArr (c₁ c₂ : Fin 3) (s : ℝ) :
    HasDerivAt (rotArr c₁ c₂) (rotArr' c₁ c₂ s) s := by
  refine hasDerivAt_pi.2 fun a => hasDerivAt_pi.2 fun b => ?_
  simp only [rotArr, rotArr']
  by_cases h1 : a = c₁ ∧ b = c₁
  · simp only [h1, and_self, if_true]; exact Real.hasDerivAt_cos s
  · simp only [h1, if_false]
    by_cases h2 : a = c₂ ∧ b = c₂
    · simp only [h2, if_true]; exact Real.hasDerivAt_cos s
    · simp only [h2, if_false]
      by_cases h3 : a = c₁ ∧ b = c₂
      · simp only [h3]; exact (Real.hasDerivAt_sin s).neg
      · simp only [h3, if_false]
        by_cases h4 : a = c₂ ∧ b = c₁
        · simp only [h4]; exact Real.hasDerivAt_sin s
        · simp only [h4, if_false]; exact hasDerivAt_const s _

theorem rotArr_zero {c₁ c₂ : Fin 3} : rotArr c₁ c₂ 0 = idArr := by
  funext a b
  fin_cases c₁ <;> fin_cases c₂ <;> fin_cases a <;> fin_cases b <;> simp [rotArr, idArr]

theorem rotArr'_zero {c₁ c₂ : Fin 3} (hne : c₁ ≠ c₂) : rotArr' c₁ c₂ 0 = elem c₂ c₁ - elem c₁ c₂ := by
  funext a b
  fin_cases c₁ <;> fin_cases c₂ <;> simp at hne <;> fin_cases a <;> fin_cases b <;> simp [rotArr', elem]

end ADeriv
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_hasDerivAt_integral_mul_comp_archRealLift3_smoothingKernel.ADeriv"

open ADeriv in
theorem solution
    (c : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hc : Continuous c) (φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hφ : IsSmoothingKernel φ) (k : AdelicGL 3 (𝓞 ℚ) ℚ) :
    (∀ i j : Fin 3,
      HasDerivAt
        (fun s : ℝ => ∫ h, φ h * c (k * WhittakerBlock.archRealLift3 (fun a b =>
            (if a = b then (1 : ℝ) else 0) + if a = i ∧ b = j then s else 0) * h) ∂(NumberField.AdelicHaar.adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ))
        (∫ h, (fun y => -deriv (fun s : ℝ => φ (WhittakerBlock.archRealLift3 (fun a b =>
            (if a = b then (1 : ℝ) else 0) + if a = i ∧ b = j then s else 0) * y)) 0) h * c (k * h) ∂(NumberField.AdelicHaar.adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ)) 0) ∧
    (∀ c₁ c₂ : Fin 3, c₁ < c₂ →
      HasDerivAt
        (fun s : ℝ => ∫ h, φ h * c (k * WhittakerBlock.archRealLift3 (fun i j =>
            if i = c₁ ∧ j = c₁ then Real.cos s else if i = c₂ ∧ j = c₂ then Real.cos s else
            if i = c₁ ∧ j = c₂ then - Real.sin s else if i = c₂ ∧ j = c₁ then Real.sin s else
            if i = j then 1 else 0) * h) ∂(NumberField.AdelicHaar.adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ))
        ((∫ h, (fun y => -deriv (fun s : ℝ => φ (WhittakerBlock.archRealLift3 (fun a b =>
            (if a = b then (1 : ℝ) else 0) + if a = c₂ ∧ b = c₁ then s else 0) * y)) 0) h * c (k * h) ∂(NumberField.AdelicHaar.adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ)) -
         (∫ h, (fun y => -deriv (fun s : ℝ => φ (WhittakerBlock.archRealLift3 (fun a b =>
            (if a = b then (1 : ℝ) else 0) + if a = c₁ ∧ b = c₂ then s else 0) * y)) 0) h * c (k * h) ∂(NumberField.AdelicHaar.adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ))) 0) := by
  classical
  haveI := NumberField.AdelicHaar.isHaarMeasure_adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ
  have hu : LocallyIntegrable c (NumberField.AdelicHaar.adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ) := hc.locallyIntegrable
  set F : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ := smoothingOperator φ c with hF
  obtain ⟨_, hsF⟩ := continuous_and_isArchSmooth3_smoothingOperator φ c hφ hu
  refine ⟨fun i j => ?_, fun c₁ c₂ hlt => ?_⟩
  ·
    obtain ⟨_, hD⟩ := archDeriv_smoothingOperator φ c hφ hu i j
    have h1 := WhittakerBlock.hasDerivAt_apply_mul_archRealLift3_of_isArchSmooth3 F hsF k i j 0 (by simp)
    have hid : (fun a b : Fin 3 => (if a = b then (1 : ℝ) else 0) + if a = i ∧ b = j then (0 : ℝ) else 0) = idArr := by
      funext a b; simp [idArr]
    simp only [hid, archRealLift3_idArr, mul_one] at h1
    have hone : ((((1 + (if i = j then (0 : ℝ) else 0))⁻¹ : ℝ)) : ℂ) = 1 := by simp
    rw [hone, one_mul, hD] at h1
    exact h1
  ·
    have hne : c₁ ≠ c₂ := ne_of_lt hlt
    obtain ⟨_, hD₂₁⟩ := archDeriv_smoothingOperator φ c hφ hu c₂ c₁
    obtain ⟨_, hD₁₂⟩ := archDeriv_smoothingOperator φ c hφ hu c₁ c₂
    set Φ : (Fin 3 → Fin 3 → ℝ) → ℂ := fun e => F (k * WhittakerBlock.archRealLift3 e) with hΦ
    have hΦs : ContDiffOn ℝ (⊤ : ℕ∞) Φ {e : Fin 3 → Fin 3 → ℝ | (Matrix.of e).det ≠ 0} := hsF k
    have hd : DifferentiableAt ℝ Φ idArr :=
      ((contDiffOn_infty_iff_fderiv_of_isOpen isOpen_invertible).1 hΦs).1.differentiableAt
        (isOpen_invertible.mem_nhds det_idArr)
    have key : HasDerivAt (fun s : ℝ => Φ (rotArr c₁ c₂ s)) (fderiv ℝ Φ idArr (rotArr' c₁ c₂ 0)) 0 :=
      hd.hasFDerivAt.comp_hasDerivAt_of_eq 0 (hasDerivAt_rotArr c₁ c₂ 0) rotArr_zero.symm
    rw [rotArr'_zero hne, map_sub, ← archDeriv_eq_fderiv_one hsF c₂ c₁ k, ← archDeriv_eq_fderiv_one hsF c₁ c₂ k,
      hD₂₁, hD₁₂] at key
    exact key

end
end S_LanglandsTunnell_CubicInduction_SlabL2_hasDerivAt_integral_mul_comp_archRealLift3_smoothingKernel
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_hasDerivAt_integral_mul_comp_archRealLift3_smoothingKernel (solution)
