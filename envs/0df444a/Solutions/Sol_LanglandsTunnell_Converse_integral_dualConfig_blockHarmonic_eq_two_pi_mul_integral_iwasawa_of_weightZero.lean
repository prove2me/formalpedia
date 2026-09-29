-- Prove2me | solution 1 for LanglandsTunnell.Converse.integral_dualConfig_blockHarmonic_eq_two_pi_mul_integral_iwasawa_of_weightZero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/4d593e2c-1f5e-5095-911c-eac150b0b773

import Definitions.Def_LanglandsTunnell_CubicInduction_JacquetVector3
import Definitions.Def_AutomorphicForm_ArchWeightChar
import Definitions.Def_LanglandsTunnell_ArchBaseChange
import Mathlib.Analysis.MellinTransform
import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne

import Mathlib
import Theorems.Thm_LanglandsTunnell_RankinSelberg_integral_matrixTwo_eq_setIntegral_iwasawaInv_unconditional
import Theorems.Thm_MeasureTheory_setIntegral_iwasawaRegion_eq_two_pi_mul_of_theta_free
import Theorems.Thm_LanglandsTunnell_Converse_ArchDatumR_W_diagOne_mul_iwasawa_eq_psi_mul_centralChar_mul_W_diagOne_of_weightZero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_Converse_integral_dualConfig_blockHarmonic_eq_two_pi_mul_integral_iwasawa_of_weightZero
p2m_attr_erase "instance" "LanglandsTunnell.CubicInduction.countable_GL2 LanglandsTunnell.CubicInduction.countable_mirabolicIndex M4aHerbrand.isMulCommutative_ideleClassGroup M4aHerbrand.isMulCommutative_sIdeleClassGroup"
p2m_attr_erase "simp" "LanglandsTunnell.CubicLambda.ResolventDatum.s3.injEq LanglandsTunnell.CubicLambda.ResolventDatum.s3.sizeOf_spec LanglandsTunnell.CubicLambda.ResolventDatum.cyclic.sizeOf_spec LanglandsTunnell.CubicLambda.ResolventDatum.cyclic.injEq LanglandsTunnell.RankinSelberg.mem_primeFibre LanglandsTunnell.CubicInduction.longWeyl3_coe LanglandsTunnell.CubicInduction.lowerUnipotent21_coe LanglandsTunnell.CubicInduction.weylPrime3_coe LanglandsTunnell.CubicInduction.gl3AmbientRightTranslate_apply LanglandsTunnell.CubicInduction.CubicInductionForm.mk.injEq LanglandsTunnell.CubicInduction.CubicInductionForm.mk.sizeOf_spec LanglandsTunnell.CubicInduction.coe_diagUnitGL2 LanglandsTunnell.CubicInduction.iotaTorusLocal_zero LanglandsTunnell.CubicInduction.coe_diagUnits2 UnramifiedWhittaker.ProductMeasureData.mk.injEq UnramifiedWhittaker.ProductMeasureData.mk.sizeOf_spec NumberField.AdeleRing.val_finiteUnitsComponent IsDedekindDomain.FiniteAdeleRing.val_unitsComponent NumberField.AdeleRing.val_finitePartUnits NumberField.AdeleRing.val_infiniteUnitsComponent M4aHerbrand.IdeleGaloisDescent.sClassAct_mk M4aHerbrand.SIdeleClassGroup.ofLE_mk M4aHerbrand.repHomOfMulEquivariant_hom_apply M4aHerbrand.coe_finPart_apply M4aHerbrand.SIdeleClassGroup.ofLE_toSIdeleClass M4aHerbrand.IdeleGaloisDescent.sClassAct_toSIdeleClass M4aHerbrand.coe_infPart_apply M4aHerbrand.toSIdeleClass_mk M4aHerbrand.IdeleGaloisDescent.classAct_mk M4aHerbrand.IdeleGaloisDescent.mk.sizeOf_spec M4aHerbrand.IdeleGaloisDescent.mk.injEq AutomorphicForm.ArchDir.E.sizeOf_spec AutomorphicForm.ArchDir.H.sizeOf_spec AutomorphicForm.ArchDir.Fm.sizeOf_spec LanglandsTunnell.deltaLiftSystem_level LanglandsTunnell.deltaLiftSystem_toRawCentral AutomorphicForm.productionPinsCompact_ν AutomorphicForm.productionPinsCompact_U AutomorphicForm.productionPinsCompact_D AutomorphicForm.productionPinsCompact_nS"
p2m_attr_erase "simp" "AutomorphicForm.productionPinsCompact_gen AutomorphicForm.productionPinsCompact_Z AutomorphicForm.productionPinsCompact_mS AutomorphicForm.productionPinsCompact_μ AutomorphicForm.productionPins_nS AutomorphicForm.productionPins_mS AutomorphicForm.productionPins_ν AutomorphicForm.productionPins_Z AutomorphicForm.productionPins_U AutomorphicForm.productionPins_μ AutomorphicForm.productionPins_gen AutomorphicForm.productionPins_D AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_zero AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_zero AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_one AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_one AutomorphicForm.gl2Weyl_val"

set_option autoImplicit false

open NumberField AutomorphicForm LanglandsTunnell LanglandsTunnell.Converse MeasureTheory

namespace DualIwasawaKit

noncomputable def eM (x y₁ y₂ θ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![Real.cos θ / y₁, -(x * Real.cos θ) / y₁ + Real.sin θ / y₂;
     -(Real.sin θ) / y₁, x * Real.sin θ / y₁ + Real.cos θ / y₂]

noncomputable def gM (x y₁ y₂ θ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![y₁ * Real.cos θ + x * y₂ * Real.sin θ, -(y₁ * Real.sin θ) + x * y₂ * Real.cos θ;
     y₂ * Real.sin θ, y₂ * Real.cos θ]

section
variable (x y₁ y₂ θ : ℝ)

theorem det_eM : (eM x y₁ y₂ θ).det = (y₁ * y₂)⁻¹ := by
  have h := Real.sin_sq_add_cos_sq θ
  rw [eM, Matrix.det_fin_two_of]
  linear_combination (y₁ * y₂)⁻¹ * h

theorem eM_mul_gM (hy₁ : y₁ ≠ 0) (hy₂ : y₂ ≠ 0) : eM x y₁ y₂ θ * gM x y₁ y₂ θ = 1 := by
  have h := Real.sin_sq_add_cos_sq θ
  have h1 : y₁ * y₁⁻¹ = 1 := mul_inv_cancel₀ hy₁
  have h2 : y₂ * y₂⁻¹ = 1 := mul_inv_cancel₀ hy₂
  rw [eM, gM]
  ext i j
  fin_cases i <;> fin_cases j
  · simp [Matrix.mul_apply, Fin.sum_univ_two]
    linear_combination (Real.cos θ ^ 2) * h1 + (Real.sin θ ^ 2) * h2 + h
  · simp [Matrix.mul_apply, Fin.sum_univ_two]
    linear_combination (-(Real.cos θ * Real.sin θ)) * h1 + (Real.cos θ * Real.sin θ) * h2
  · simp [Matrix.mul_apply, Fin.sum_univ_two]
    linear_combination (-(Real.sin θ * Real.cos θ)) * h1 + (Real.cos θ * Real.sin θ) * h2
  · simp [Matrix.mul_apply, Fin.sum_univ_two]
    linear_combination (Real.sin θ ^ 2) * h1 + (Real.cos θ ^ 2) * h2 + h

theorem inv_eM (hy₁ : y₁ ≠ 0) (hy₂ : y₂ ≠ 0) : (eM x y₁ y₂ θ)⁻¹ = gM x y₁ y₂ θ :=
  Matrix.inv_eq_right_inv (eM_mul_gM x y₁ y₂ θ hy₁ hy₂)

theorem gM_one_zero : gM x y₁ y₂ θ 1 0 = y₂ * Real.sin θ := by simp [gM]
theorem gM_one_one : gM x y₁ y₂ θ 1 1 = y₂ * Real.cos θ := by simp [gM]

theorem eM00 : eM x y₁ y₂ θ 0 0 = Real.cos θ / y₁ := by simp [eM]
theorem eM10 : eM x y₁ y₂ θ 1 0 = -(Real.sin θ) / y₁ := by simp [eM]
theorem eM01 : eM x y₁ y₂ θ 0 1 = -(x * Real.cos θ) / y₁ + Real.sin θ / y₂ := by simp [eM]
theorem eM11 : eM x y₁ y₂ θ 1 1 = x * Real.sin θ / y₁ + Real.cos θ / y₂ := by simp [eM]

theorem col0_sq (hy₁ : y₁ ≠ 0) : eM x y₁ y₂ θ 0 0 ^ 2 + eM x y₁ y₂ θ 1 0 ^ 2 = 1 / y₁ ^ 2 := by
  have h := Real.sin_sq_add_cos_sq θ
  rw [eM00, eM10]
  field_simp
  linear_combination h

theorem col1_sq (hy₁ : y₁ ≠ 0) (hy₂ : y₂ ≠ 0) :
    eM x y₁ y₂ θ 0 1 ^ 2 + eM x y₁ y₂ θ 1 1 ^ 2 = x ^ 2 / y₁ ^ 2 + 1 / y₂ ^ 2 := by
  have h := Real.sin_sq_add_cos_sq θ
  rw [eM01, eM11]
  field_simp
  linear_combination (x ^ 2 * y₂ ^ 2 + y₁ ^ 2) * h

theorem row1_sq (hy₁ : y₁ ≠ 0) (hy₂ : y₂ ≠ 0) :
    (eM x y₁ y₂ θ)⁻¹ 1 0 ^ 2 + (eM x y₁ y₂ θ)⁻¹ 1 1 ^ 2 = y₂ ^ 2 := by
  have h := Real.sin_sq_add_cos_sq θ
  rw [inv_eM x y₁ y₂ θ hy₁ hy₂, gM_one_zero, gM_one_one]
  linear_combination y₂ ^ 2 * h

theorem row1_pair (hy₁ : y₁ ≠ 0) (hy₂ : y₂ ≠ 0) :
    (eM x y₁ y₂ θ)⁻¹ 1 0 * eM x y₁ y₂ θ 1 0 - (eM x y₁ y₂ θ)⁻¹ 1 1 * eM x y₁ y₂ θ 0 0 = -(y₂ / y₁) := by
  have h := Real.sin_sq_add_cos_sq θ
  rw [inv_eM x y₁ y₂ θ hy₁ hy₂, gM_one_zero, gM_one_one, eM10, eM00]
  field_simp
  linear_combination (-1 : ℝ) * h

end

end DualIwasawaKit

open DualIwasawaKit in

theorem solution
    {P₂ : RealArchParam} (D : ArchDatumR P₂)
    (hDW0 : ∀ (r : rowIsometrySubgroup₀ ℝ) (x : GL (Fin 2) ℝ),
        D.W ((x * (r : GL (Fin 2) ℝ) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = D.W (x : Matrix (Fin 2) (Fin 2) ℝ))
    (a : ℝ) (ha : a ≠ 0) (u : ℂ) (a₀ : ZMod 2) (a₁ a₂ : ℝ) (ha₁ : a₁ ≠ 0) (ha₂ : 0 < a₂)
    (hInt : Integrable (fun q : ℝ × ℝ × ℝ =>
        ((Real.exp (-(Real.pi * (a₂⁻¹ ^ 2 * (q.1 ^ 2 / q.2.1 ^ 2 + 1 / q.2.2 ^ 2) + 1 / q.2.1 ^ 2))) : ℂ) *
            (((a₁ ^ 2 * |q.2.1 * q.2.2| : ℝ)) : ℂ) *
            (((q.2.1⁻¹ : ℝ) : ℂ) * ((a : ℂ) * (a₁ : ℂ) * (q.2.2 : ℂ) + (a₂⁻¹ : ℂ) * ((q.2.2⁻¹ : ℝ) : ℂ) + Complex.I * (a₂⁻¹ : ℂ) * (((q.1 / q.2.1 : ℝ)) : ℂ))) *
            (Real.exp (-(Real.pi * a ^ 2 * a₁ ^ 2 * q.2.2 ^ 2)) : ℂ)) *
          (ArchR.quasiChar u a₀ (q.2.1 * q.2.2)⁻¹ * (((|(q.2.1 * q.2.2)⁻¹| ^ 2)⁻¹ : ℝ) : ℂ)) *
          (ArchR.psi (a * q.1) * (ArchR.centralChar P₂ q.2.2 * ((|q.2.2| : ℝ) : ℂ)) * D.W (ArchR.diagOne (a * q.2.1 / q.2.2))) *
          ((q.2.2 ^ 2 * (|q.2.1 * q.2.2| ^ 4)⁻¹ : ℝ) : ℂ)) ((volume : Measure ℝ).prod ((volume : Measure ℝ).prod ((volume : Measure ℝ).restrict (Set.Ioi 0))))) :
    (∫ e : Fin 2 → Fin 2 → ℝ,
        ((((e 0 0 : ℝ) : ℂ) - Complex.I * ((e 1 0 : ℝ) : ℂ)) ^ 1 *
                    (Real.exp (-(Real.pi * (a₂⁻¹ ^ 2 * (e 0 1 ^ 2 + e 1 1 ^ 2) + (e 0 0 ^ 2 + e 1 0 ^ 2)))) : ℂ) *
                    (((a₁ ^ 2 * |(Matrix.of e).det|⁻¹ : ℝ)) : ℂ) *
                    (-Complex.I *
                      ((a : ℂ) * (a₁ : ℂ) * ((((Matrix.of e)⁻¹ 1 0 : ℝ) : ℂ) + Complex.I * (((Matrix.of e)⁻¹ 1 1 : ℝ) : ℂ)) +
                        (a₂⁻¹ : ℂ) * (((e 0 1 : ℝ) : ℂ) + Complex.I * ((e 1 1 : ℝ) : ℂ)))) *
                    (Real.exp (-(Real.pi * a ^ 2 * a₁ ^ 2 * (((Matrix.of e)⁻¹ 1 0) ^ 2 + ((Matrix.of e)⁻¹ 1 1) ^ 2))) : ℂ)) *
                        (ArchR.quasiChar u a₀ (Matrix.of e).det * (((|(Matrix.of e).det| ^ 2)⁻¹ : ℝ) : ℂ)) *
                        D.W (ArchR.diagOne a * (Matrix.of e)⁻¹)) =
      ((2 * Real.pi : ℝ) : ℂ) * ∫ y₁ : ℝ, ∫ y₂ in Set.Ioi (0 : ℝ), ∫ x : ℝ,
        ((Real.exp (-(Real.pi * (a₂⁻¹ ^ 2 * (x ^ 2 / y₁ ^ 2 + 1 / y₂ ^ 2) + 1 / y₁ ^ 2))) : ℂ) *
            (((a₁ ^ 2 * |y₁ * y₂| : ℝ)) : ℂ) *
            (((y₁⁻¹ : ℝ) : ℂ) * ((a : ℂ) * (a₁ : ℂ) * (y₂ : ℂ) + (a₂⁻¹ : ℂ) * ((y₂⁻¹ : ℝ) : ℂ) + Complex.I * (a₂⁻¹ : ℂ) * (((x / y₁ : ℝ)) : ℂ))) *
            (Real.exp (-(Real.pi * a ^ 2 * a₁ ^ 2 * y₂ ^ 2)) : ℂ)) *
          (ArchR.quasiChar u a₀ (y₁ * y₂)⁻¹ * (((|(y₁ * y₂)⁻¹| ^ 2)⁻¹ : ℝ) : ℂ)) *
          (ArchR.psi (a * x) * (ArchR.centralChar P₂ y₂ * ((|y₂| : ℝ) : ℂ)) * D.W (ArchR.diagOne (a * y₁ / y₂))) *
          ((y₂ ^ 2 * (|y₁ * y₂| ^ 4)⁻¹ : ℝ) : ℂ) := by

  set F : (Fin 2 → Fin 2 → ℝ) → ℂ := fun e =>
        ((((e 0 0 : ℝ) : ℂ) - Complex.I * ((e 1 0 : ℝ) : ℂ)) ^ 1 *
                    (Real.exp (-(Real.pi * (a₂⁻¹ ^ 2 * (e 0 1 ^ 2 + e 1 1 ^ 2) + (e 0 0 ^ 2 + e 1 0 ^ 2)))) : ℂ) *
                    (((a₁ ^ 2 * |(Matrix.of e).det|⁻¹ : ℝ)) : ℂ) *
                    (-Complex.I *
                      ((a : ℂ) * (a₁ : ℂ) * ((((Matrix.of e)⁻¹ 1 0 : ℝ) : ℂ) + Complex.I * (((Matrix.of e)⁻¹ 1 1 : ℝ) : ℂ)) +
                        (a₂⁻¹ : ℂ) * (((e 0 1 : ℝ) : ℂ) + Complex.I * ((e 1 1 : ℝ) : ℂ)))) *
                    (Real.exp (-(Real.pi * a ^ 2 * a₁ ^ 2 * (((Matrix.of e)⁻¹ 1 0) ^ 2 + ((Matrix.of e)⁻¹ 1 1) ^ 2))) : ℂ)) *
                        (ArchR.quasiChar u a₀ (Matrix.of e).det * (((|(Matrix.of e).det| ^ 2)⁻¹ : ℝ) : ℂ)) *
                        D.W (ArchR.diagOne a * (Matrix.of e)⁻¹) with hF

  set G : ℝ → ℝ → ℝ → ℂ := fun x y₁ y₂ =>
    ((Real.exp (-(Real.pi * (a₂⁻¹ ^ 2 * (x ^ 2 / y₁ ^ 2 + 1 / y₂ ^ 2) + 1 / y₁ ^ 2))) : ℂ) *
            (((a₁ ^ 2 * |y₁ * y₂| : ℝ)) : ℂ) *
            (((y₁⁻¹ : ℝ) : ℂ) * ((a : ℂ) * (a₁ : ℂ) * (y₂ : ℂ) + (a₂⁻¹ : ℂ) * ((y₂⁻¹ : ℝ) : ℂ) + Complex.I * (a₂⁻¹ : ℂ) * (((x / y₁ : ℝ)) : ℂ))) *
            (Real.exp (-(Real.pi * a ^ 2 * a₁ ^ 2 * y₂ ^ 2)) : ℂ)) *
          (ArchR.quasiChar u a₀ (y₁ * y₂)⁻¹ * (((|(y₁ * y₂)⁻¹| ^ 2)⁻¹ : ℝ) : ℂ)) *
          (ArchR.psi (a * x) * (ArchR.centralChar P₂ y₂ * ((|y₂| : ℝ) : ℂ)) * D.W (ArchR.diagOne (a * y₁ / y₂))) *
          ((y₂ ^ 2 * (|y₁ * y₂| ^ 4)⁻¹ : ℝ) : ℂ) with hG
  have hC : ∀ θ : ℝ, ((Real.cos θ : ℝ) : ℂ) ^ 2 + ((Real.sin θ : ℝ) : ℂ) ^ 2 = 1 := fun θ => by
    have h := Real.cos_sq_add_sin_sq θ
    exact_mod_cast h

  have key : ∀ (x y₁ y₂ θ : ℝ), y₁ ≠ 0 → 0 < y₂ → ∀ e : Fin 2 → Fin 2 → ℝ, Matrix.of e = eM x y₁ y₂ θ →
      F e * ((y₂ ^ 2 * (|y₁ * y₂| ^ 4)⁻¹ : ℝ) : ℂ) = G x y₁ y₂ := by
    intro x y₁ y₂ θ hy₁ hy₂ e he
    have hy₂' : y₂ ≠ 0 := hy₂.ne'
    have hee : ∀ i j, e i j = eM x y₁ y₂ θ i j := fun i j => by rw [← he]; rfl
    have hW : D.W (ArchR.diagOne a * (Matrix.of e)⁻¹) =
        ArchR.psi (a * x) * (ArchR.centralChar P₂ y₂ * ((|y₂| : ℝ) : ℂ)) * D.W (ArchR.diagOne (a * y₁ / y₂)) := by
      rw [he, inv_eM x y₁ y₂ θ hy₁ hy₂']
      exact LanglandsTunnell.Converse.ArchDatumR.W_diagOne_mul_iwasawa_eq_psi_mul_centralChar_mul_W_diagOne_of_weightZero
        D hDW0 ha x hy₁ hy₂ θ
    have hdet : (Matrix.of e).det = (y₁ * y₂)⁻¹ := by rw [he, det_eM]
    have hc0 : e 0 0 ^ 2 + e 1 0 ^ 2 = 1 / y₁ ^ 2 := by rw [hee, hee]; exact col0_sq x y₁ y₂ θ hy₁
    have hc1 : e 0 1 ^ 2 + e 1 1 ^ 2 = x ^ 2 / y₁ ^ 2 + 1 / y₂ ^ 2 := by rw [hee, hee]; exact col1_sq x y₁ y₂ θ hy₁ hy₂'
    have hr1 : (Matrix.of e)⁻¹ 1 0 ^ 2 + (Matrix.of e)⁻¹ 1 1 ^ 2 = y₂ ^ 2 := by rw [he]; exact row1_sq x y₁ y₂ θ hy₁ hy₂'
    have hi10 : (Matrix.of e)⁻¹ 1 0 = y₂ * Real.sin θ := by rw [he, inv_eM x y₁ y₂ θ hy₁ hy₂', gM_one_zero]
    have hi11 : (Matrix.of e)⁻¹ 1 1 = y₂ * Real.cos θ := by rw [he, inv_eM x y₁ y₂ θ hy₁ hy₂', gM_one_one]
    have habs : |(Matrix.of e).det|⁻¹ = |y₁ * y₂| := by rw [hdet, abs_inv, inv_inv]

    have hHB : (((e 0 0 : ℝ) : ℂ) - Complex.I * ((e 1 0 : ℝ) : ℂ)) ^ 1 *
        (-Complex.I * ((a : ℂ) * (a₁ : ℂ) * ((((Matrix.of e)⁻¹ 1 0 : ℝ) : ℂ) + Complex.I * (((Matrix.of e)⁻¹ 1 1 : ℝ) : ℂ)) +
          (a₂⁻¹ : ℂ) * (((e 0 1 : ℝ) : ℂ) + Complex.I * ((e 1 1 : ℝ) : ℂ))))
        = ((y₁⁻¹ : ℝ) : ℂ) * ((a : ℂ) * (a₁ : ℂ) * (y₂ : ℂ) + (a₂⁻¹ : ℂ) * ((y₂⁻¹ : ℝ) : ℂ) +
            Complex.I * (a₂⁻¹ : ℂ) * (((x / y₁ : ℝ)) : ℂ)) := by
      rw [hi10, hi11, hee 0 0, hee 1 0, hee 0 1, hee 1 1, eM00, eM10, eM01, eM11]
      push_cast
      have hC' := Complex.cos_sq_add_sin_sq (θ : ℂ)
      linear_combination
        ((y₁ : ℂ)⁻¹ * (((a : ℂ) * (a₁ : ℂ) * (y₂ : ℂ) + (a₂ : ℂ)⁻¹ * (y₂ : ℂ)⁻¹) +
          Complex.I * ((a₂ : ℂ)⁻¹ * ((x : ℂ) / (y₁ : ℂ))))) * hC' +
        ((y₁ : ℂ)⁻¹ * (-(Complex.cos (θ : ℂ) ^ 2 + Complex.sin (θ : ℂ) ^ 2) *
            ((a : ℂ) * (a₁ : ℂ) * (y₂ : ℂ) + (a₂ : ℂ)⁻¹ * (y₂ : ℂ)⁻¹) -
          Complex.I * Complex.sin (θ : ℂ) *
            ((a : ℂ) * (a₁ : ℂ) * (y₂ : ℂ) * Complex.cos (θ : ℂ) +
              (a₂ : ℂ)⁻¹ * ((x : ℂ) * Complex.sin (θ : ℂ) / (y₁ : ℂ) + Complex.cos (θ : ℂ) / (y₂ : ℂ))))) *
          Complex.I_mul_I
    simp only [hF, hG]
    rw [hW, hr1, hc0, hc1, habs, hdet]
    linear_combination
      ((Real.exp (-(Real.pi * (a₂⁻¹ ^ 2 * (x ^ 2 / y₁ ^ 2 + 1 / y₂ ^ 2) + 1 / y₁ ^ 2))) : ℂ) *
        (((a₁ ^ 2 * |y₁ * y₂| : ℝ)) : ℂ) *
        (Real.exp (-(Real.pi * a ^ 2 * a₁ ^ 2 * y₂ ^ 2)) : ℂ) *
        (ArchR.quasiChar u a₀ (y₁ * y₂)⁻¹ * (((|(y₁ * y₂)⁻¹| ^ 2)⁻¹ : ℝ) : ℂ)) *
        (ArchR.psi (a * x) * (ArchR.centralChar P₂ y₂ * ((|y₂| : ℝ) : ℂ)) * D.W (ArchR.diagOne (a * y₁ / y₂))) *
        ((y₂ ^ 2 * (|y₁ * y₂| ^ 4)⁻¹ : ℝ) : ℂ)) * hHB

  rw [show (∫ e : Fin 2 → Fin 2 → ℝ,
        ((((e 0 0 : ℝ) : ℂ) - Complex.I * ((e 1 0 : ℝ) : ℂ)) ^ 1 *
                    (Real.exp (-(Real.pi * (a₂⁻¹ ^ 2 * (e 0 1 ^ 2 + e 1 1 ^ 2) + (e 0 0 ^ 2 + e 1 0 ^ 2)))) : ℂ) *
                    (((a₁ ^ 2 * |(Matrix.of e).det|⁻¹ : ℝ)) : ℂ) *
                    (-Complex.I *
                      ((a : ℂ) * (a₁ : ℂ) * ((((Matrix.of e)⁻¹ 1 0 : ℝ) : ℂ) + Complex.I * (((Matrix.of e)⁻¹ 1 1 : ℝ) : ℂ)) +
                        (a₂⁻¹ : ℂ) * (((e 0 1 : ℝ) : ℂ) + Complex.I * ((e 1 1 : ℝ) : ℂ)))) *
                    (Real.exp (-(Real.pi * a ^ 2 * a₁ ^ 2 * (((Matrix.of e)⁻¹ 1 0) ^ 2 + ((Matrix.of e)⁻¹ 1 1) ^ 2))) : ℂ)) *
                        (ArchR.quasiChar u a₀ (Matrix.of e).det * (((|(Matrix.of e).det| ^ 2)⁻¹ : ℝ) : ℂ)) *
                        D.W (ArchR.diagOne a * (Matrix.of e)⁻¹)) = ∫ e : Fin 2 → Fin 2 → ℝ, F e from rfl,
    (LanglandsTunnell.RankinSelberg.integral_matrixTwo_eq_setIntegral_iwasawaInv_unconditional F).2]
  have h2 := MeasureTheory.setIntegral_iwasawaRegion_eq_two_pi_mul_of_theta_free
    (fun p : ℝ × ℝ × ℝ × ℝ =>
      F (fun i j => (!![Real.cos p.2.2.2 / p.2.1, -(p.1 * Real.cos p.2.2.2) / p.2.1 + Real.sin p.2.2.2 / p.2.2.1;
                        -(Real.sin p.2.2.2) / p.2.1, p.1 * Real.sin p.2.2.2 / p.2.1 + Real.cos p.2.2.2 / p.2.2.1] :
                          Matrix (Fin 2) (Fin 2) ℝ) i j) *
        ((p.2.2.1 ^ 2 * (|p.2.1 * p.2.2.1| ^ 4)⁻¹ : ℝ) : ℂ))
    G (fun x y₁ y₂ θ hy₁ hy₂ => key x y₁ y₂ θ hy₁ hy₂ _ rfl) (by simpa only [hG] using hInt)
  rw [h2]

end S_LanglandsTunnell_Converse_integral_dualConfig_blockHarmonic_eq_two_pi_mul_integral_iwasawa_of_weightZero
end P2MW
export P2MW.S_LanglandsTunnell_Converse_integral_dualConfig_blockHarmonic_eq_two_pi_mul_integral_iwasawa_of_weightZero (solution)
