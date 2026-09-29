-- Prove2me | solution 1 for LanglandsTunnell.RankinSelberg.exists_forall_iwasawaIntegral_eq_const_mul_oneSided_torusPair_add_mirror_of_discreteProfile_conjBlockHarmonic_colHarmonic
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/23f626e4-65d8-5c67-a2b6-0fa9ff45f8d1

import Mathlib
import Definitions.Def_LanglandsTunnell_JLConverse
import Definitions.Def_AutomorphicForm_ArchWeightChar
import Theorems.Thm_LanglandsTunnell_Converse_ArchDatumR_W_diagOne_mul_iwasawa_eq_psi_mul_centralChar_mul_archWeightChar_mul_W_diagOne
import Theorems.Thm_MeasureTheory_setIntegral_iwasawaRegion_eq_two_pi_mul_of_theta_free
import Theorems.Thm_LanglandsTunnell_Converse_exists_forall_integrable_thetaFree_iwasawaIntegrand_conjBlockPow_colHarmonic_of_oneSided_profile
import Theorems.Thm_LanglandsTunnell_Converse_exists_forall_integrable_xPowGaussian_psi_mul_torusPair_of_oneSided_profile
import Theorems.Thm_LanglandsTunnell_integral_ofReal_pow_mul_exp_neg_pi_mul_sq_mul_cexp_eq_iteratedDeriv
import Theorems.Thm_LanglandsTunnell_exp_neg_pi_mul_sq_mul_integral_sub_I_mul_pow_mul_exp_eq_iteratedDeriv
import Theorems.Thm_LanglandsTunnell_exists_forall_integrable_oneSided_torusPair_integrand_of_torusBound_of_polyBound
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_RankinSelberg_exists_forall_iwasawaIntegral_eq_const_mul_oneSided_torusPair_add_mirror_of_discreteProfile_conjBlockHarmonic_colHarmonic
p2m_attr_erase "instance" "LanglandsTunnell.CubicInduction.countable_GL2 LanglandsTunnell.CubicInduction.countable_mirabolicIndex M4aHerbrand.isMulCommutative_ideleClassGroup M4aHerbrand.isMulCommutative_sIdeleClassGroup"
p2m_attr_erase "simp" "LanglandsTunnell.CubicLambda.ResolventDatum.s3.injEq LanglandsTunnell.CubicLambda.ResolventDatum.s3.sizeOf_spec LanglandsTunnell.CubicLambda.ResolventDatum.cyclic.sizeOf_spec LanglandsTunnell.CubicLambda.ResolventDatum.cyclic.injEq LanglandsTunnell.RankinSelberg.mem_primeFibre LanglandsTunnell.CubicInduction.longWeyl3_coe LanglandsTunnell.CubicInduction.lowerUnipotent21_coe LanglandsTunnell.CubicInduction.weylPrime3_coe LanglandsTunnell.CubicInduction.gl3AmbientRightTranslate_apply LanglandsTunnell.CubicInduction.CubicInductionForm.mk.injEq LanglandsTunnell.CubicInduction.CubicInductionForm.mk.sizeOf_spec LanglandsTunnell.CubicInduction.coe_diagUnitGL2 LanglandsTunnell.CubicInduction.iotaTorusLocal_zero LanglandsTunnell.CubicInduction.coe_diagUnits2 UnramifiedWhittaker.ProductMeasureData.mk.injEq UnramifiedWhittaker.ProductMeasureData.mk.sizeOf_spec NumberField.AdeleRing.val_finiteUnitsComponent IsDedekindDomain.FiniteAdeleRing.val_unitsComponent NumberField.AdeleRing.val_finitePartUnits NumberField.AdeleRing.val_infiniteUnitsComponent M4aHerbrand.IdeleGaloisDescent.sClassAct_mk M4aHerbrand.SIdeleClassGroup.ofLE_mk M4aHerbrand.repHomOfMulEquivariant_hom_apply M4aHerbrand.coe_finPart_apply M4aHerbrand.SIdeleClassGroup.ofLE_toSIdeleClass M4aHerbrand.IdeleGaloisDescent.sClassAct_toSIdeleClass M4aHerbrand.coe_infPart_apply M4aHerbrand.toSIdeleClass_mk M4aHerbrand.IdeleGaloisDescent.classAct_mk M4aHerbrand.IdeleGaloisDescent.mk.sizeOf_spec M4aHerbrand.IdeleGaloisDescent.mk.injEq AutomorphicForm.ArchDir.E.sizeOf_spec AutomorphicForm.ArchDir.H.sizeOf_spec AutomorphicForm.ArchDir.Fm.sizeOf_spec LanglandsTunnell.deltaLiftSystem_level LanglandsTunnell.deltaLiftSystem_toRawCentral AutomorphicForm.productionPinsCompact_ν AutomorphicForm.productionPinsCompact_U AutomorphicForm.productionPinsCompact_D AutomorphicForm.productionPinsCompact_nS"
p2m_attr_erase "simp" "AutomorphicForm.productionPinsCompact_gen AutomorphicForm.productionPinsCompact_Z AutomorphicForm.productionPinsCompact_mS AutomorphicForm.productionPinsCompact_μ AutomorphicForm.productionPins_nS AutomorphicForm.productionPins_mS AutomorphicForm.productionPins_ν AutomorphicForm.productionPins_Z AutomorphicForm.productionPins_U AutomorphicForm.productionPins_μ AutomorphicForm.productionPins_gen AutomorphicForm.productionPins_D AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_zero AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_zero AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_one AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_one AutomorphicForm.gl2Weyl_val"

set_option autoImplicit false

open NumberField AutomorphicForm AutomorphicForm.WindowedSiegel LanglandsTunnell LanglandsTunnell.Converse MeasureTheory Set

namespace K7Rot

noncomputable def rotM (θ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![Real.cos θ, -Real.sin θ; Real.sin θ, Real.cos θ]

theorem det_rotM (θ : ℝ) : (rotM θ).det = 1 := by
  rw [rotM, Matrix.det_fin_two_of]
  have := Real.sin_sq_add_cos_sq θ
  nlinarith

noncomputable def rotGL (θ : ℝ) : GL (Fin 2) ℝ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (rotM θ) (by rw [det_rotM]; exact one_ne_zero)

@[scoped simp] theorem coe_rotGL (θ : ℝ) : ((rotGL θ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = rotM θ := rfl

theorem rotGL_mem (θ : ℝ) : rotGL θ ∈ rowIsometrySubgroup₀ ℝ := by
  rw [mem_rowIsometrySubgroup₀_iff]
  refine ⟨by rw [coe_rotGL, det_rotM], ?_, ?_⟩
  · rw [coe_rotGL, det_rotM, norm_one]
  · intro x y
    simp only [coe_rotGL, rotM, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one, Matrix.empty_val', Real.norm_eq_abs, sq_abs]
    have := Real.sin_sq_add_cos_sq θ
    nlinarith [this]

noncomputable def rotK (θ : ℝ) : rowIsometrySubgroup₀ ℝ := ⟨rotGL θ, rotGL_mem θ⟩

theorem coe_rotK (θ : ℝ) :
    ((rotK θ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = !![Real.cos θ, -Real.sin θ; Real.sin θ, Real.cos θ] := rfl

theorem archWeightOneℝ_rotK (θ : ℝ) :
    (archWeightOneℝ (rotK θ) : ℂ) = Complex.exp (-(θ : ℂ) * Complex.I) := by
  show firstRowℂ (rotGL θ) = _
  apply Complex.ext
  · simp [firstRowℂ, rotM, Complex.exp_re]
  · simp [firstRowℂ, rotM, Complex.exp_im]

theorem archWeightCharℝ_rotK (k : ℤ) (θ : ℝ) :
    (archWeightCharℝ k (rotK θ) : ℂ) = Complex.exp (-(k : ℂ) * (θ : ℂ) * Complex.I) := by
  have h1 : (archWeightCharℝ k (rotK θ) : ℂ) = ((archWeightOneℝ (rotK θ)) ^ k : ℂˣ) := rfl
  rw [h1, Units.val_zpow_eq_zpow_val, archWeightOneℝ_rotK, ← Complex.exp_int_mul]
  congr 1; ring

theorem cos_add_I_sin (θ : ℝ) :
    ((Real.cos θ : ℝ) : ℂ) + Complex.I * ((Real.sin θ : ℝ) : ℂ) = Complex.exp ((θ : ℂ) * Complex.I) := by
  rw [Complex.exp_mul_I, Complex.ofReal_cos, Complex.ofReal_sin]; ring

theorem col_factor (θ y₂ ε' : ℝ) (hε' : ε' = 1 ∨ ε' = -1) :
    ((y₂ * Real.sin θ : ℝ) : ℂ) + (ε' : ℂ) * Complex.I * ((y₂ * Real.cos θ : ℝ) : ℂ) =
      ((ε' : ℂ) * Complex.I * (y₂ : ℂ)) * Complex.exp (-((ε' : ℂ) * (θ : ℂ)) * Complex.I) := by
  have hI : Complex.I * Complex.I = -1 := Complex.I_mul_I
  rcases hε' with h | h
  · subst h
    push_cast
    rw [show -((1 : ℂ) * (θ : ℂ)) * Complex.I = (-(θ : ℂ)) * Complex.I by ring, Complex.exp_mul_I,
      Complex.cos_neg, Complex.sin_neg, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
    linear_combination ((y₂ : ℂ) * (Real.sin θ : ℂ)) * hI
  · subst h
    push_cast
    rw [show -((-1 : ℂ) * (θ : ℂ)) * Complex.I = (θ : ℂ) * Complex.I by ring, Complex.exp_mul_I,
      ← Complex.ofReal_cos, ← Complex.ofReal_sin]
    linear_combination ((y₂ : ℂ) * (Real.sin θ : ℂ)) * hI

theorem phase_eq_one (m n : ℕ) (k₀ : ℤ) (ε' θ : ℝ)
    (hcol : (ε' = -1 ∧ (n : ℤ) = k₀ - m) ∨ (ε' = 1 ∧ (n : ℤ) = m - k₀)) :
    Complex.exp ((θ : ℂ) * Complex.I) ^ m * Complex.exp (-((ε' : ℂ) * (θ : ℂ)) * Complex.I) ^ n *
      Complex.exp (-(k₀ : ℂ) * (θ : ℂ) * Complex.I) = 1 := by
  rw [← Complex.exp_nat_mul, ← Complex.exp_nat_mul, ← Complex.exp_add, ← Complex.exp_add]
  rcases hcol with ⟨hε, hn⟩ | ⟨hε, hn⟩
  · have hn' : ((n : ℤ) : ℂ) = (k₀ : ℂ) - (m : ℂ) := by rw [hn]; push_cast; ring
    have : (n : ℂ) = (k₀ : ℂ) - (m : ℂ) := by exact_mod_cast hn'
    rw [this, hε]; push_cast
    rw [show (m : ℂ) * ((θ : ℂ) * Complex.I) + ((k₀ : ℂ) - (m : ℂ)) * (-((-1 : ℂ) * (θ : ℂ)) * Complex.I) +
      -(k₀ : ℂ) * (θ : ℂ) * Complex.I = 0 by ring, Complex.exp_zero]
  · have hn' : ((n : ℤ) : ℂ) = (m : ℂ) - (k₀ : ℂ) := by rw [hn]; push_cast; ring
    have : (n : ℂ) = (m : ℂ) - (k₀ : ℂ) := by exact_mod_cast hn'
    rw [this, hε]; push_cast
    rw [show (m : ℂ) * ((θ : ℂ) * Complex.I) + ((m : ℂ) - (k₀ : ℂ)) * (-((1 : ℂ) * (θ : ℂ)) * Complex.I) +
      -(k₀ : ℂ) * (θ : ℂ) * Complex.I = 0 by ring, Complex.exp_zero]

end K7Rot
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_forall_iwasawaIntegral_eq_const_mul_oneSided_torusPair_add_mirror_of_discreteProfile_conjBlockHarmonic_colHarmonic.K7Rot"

namespace K7Theta
open K7Rot

theorem ae_ne_zero : ∀ᵐ t : ℝ ∂volume, t ≠ 0 := by
  rw [ae_iff]; simp

theorem pointwise {P₂ : RealArchParam} (D : ArchDatumR P₂) (k₀ : ℤ)
    (hDW : ∀ (r : rowIsometrySubgroup₀ ℝ) (x : GL (Fin 2) ℝ),
        D.W ((x * (r : GL (Fin 2) ℝ) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
          (archWeightCharℝ k₀ r : ℂ) * D.W (x : Matrix (Fin 2) (Fin 2) ℝ))
    (W : ℝ → ℂ) (u₀ cP : ℂ) (a₀ : ZMod 2) (m n : ℕ) (ε' : ℝ)
    (hcol : (ε' = -1 ∧ (n : ℤ) = k₀ - m) ∨ (ε' = 1 ∧ (n : ℤ) = m - k₀))
    (s : ℂ) (x y₁ y₂ θ : ℝ) (hy₁ : y₁ ≠ 0) (hy₂ : 0 < y₂) :
    ArchR.quasiChar u₀ a₀ (y₁ * y₂)⁻¹ * (((|(y₁ * y₂)⁻¹| ^ 2)⁻¹ : ℝ) : ℂ) *
        ((∫ t : ℝ, W t * D.W (ArchR.diagOne ((-1 : ℝ) * t) *
              !![y₁ * Real.cos θ + x * y₂ * Real.sin θ, -(y₁ * Real.sin θ) + x * y₂ * Real.cos θ;
                 y₂ * Real.sin θ, y₂ * Real.cos θ]) *
            (((|t| : ℝ) : ℂ) ^ (s - 1 / 2)) * (((t ^ 2)⁻¹ : ℝ) : ℂ)) *
          (((((Real.cos θ : ℝ) : ℂ) + Complex.I * ((Real.sin θ : ℝ) : ℂ)) *
                ((((1 / y₁ - 1 / y₂ : ℝ) : ℂ)) + Complex.I * (((x / y₁ : ℝ) : ℂ)))) ^ m *
            (Real.exp (-(Real.pi * ((1 + x ^ 2) / y₁ ^ 2 + 1 / y₂ ^ 2))) : ℂ) *
            ((|y₁ * y₂| : ℝ) : ℂ) *
            (-Complex.I * (-1 : ℂ)) ^ n *
            (((y₂ * Real.sin θ : ℝ) : ℂ) + (ε' : ℂ) * Complex.I * ((y₂ * Real.cos θ : ℝ) : ℂ)) ^ n *
            ((1 / 2 : ℂ) *
              ((Real.pi * (-1 : ℝ) ^ 2 * ((y₂ * Real.sin θ) ^ 2 + (y₂ * Real.cos θ) ^ 2) : ℝ) : ℂ)
                  ^ (-((cP + P₂.centralExponent + 2 * s + n + 1) / 2)) *
              Complex.Gamma ((cP + P₂.centralExponent + 2 * s + n + 1) / 2)))) *
        ((y₂ ^ 2 * (|y₁ * y₂| ^ 4)⁻¹ : ℝ) : ℂ)
      = ArchR.quasiChar u₀ a₀ (y₁ * y₂)⁻¹ * (((|(y₁ * y₂)⁻¹| ^ 2)⁻¹ : ℝ) : ℂ) *
          ((ArchR.centralChar P₂ y₂ * ((|y₂| : ℝ) : ℂ)) *
            (∫ t : ℝ, W t * ArchR.psi ((-1 : ℝ) * t * x) * D.W (ArchR.diagOne ((-1 : ℝ) * t * y₁ / y₂)) *
               (((|t| : ℝ) : ℂ) ^ (s - 1 / 2)) * (((t ^ 2)⁻¹ : ℝ) : ℂ)) *
            (((((1 / y₁ - 1 / y₂ : ℝ) : ℂ)) + Complex.I * (((x / y₁ : ℝ) : ℂ))) ^ m *
              (Real.exp (-(Real.pi * ((1 + x ^ 2) / y₁ ^ 2 + 1 / y₂ ^ 2))) : ℂ) *
              ((|y₁ * y₂| : ℝ) : ℂ) *
              (-Complex.I * ((-1 : ℝ) : ℂ)) ^ n * ((ε' : ℂ) * Complex.I * (y₂ : ℂ)) ^ n *
              ((1 / 2 : ℂ) * ((Real.pi * (-1 : ℝ) ^ 2 * y₂ ^ 2 : ℝ) : ℂ) ^ (-((cP + P₂.centralExponent + 2 * s + n + 1) / 2)) *
                Complex.Gamma ((cP + P₂.centralExponent + 2 * s + n + 1) / 2)))) *
          ((y₂ ^ 2 * (|y₁ * y₂| ^ 4)⁻¹ : ℝ) : ℂ) := by
  have hε : ε' = 1 ∨ ε' = -1 := by
    rcases hcol with ⟨h, _⟩ | ⟨h, _⟩
    · exact Or.inr h
    · exact Or.inl h

  have hT : (∫ t : ℝ, W t * D.W (ArchR.diagOne ((-1 : ℝ) * t) *
              !![y₁ * Real.cos θ + x * y₂ * Real.sin θ, -(y₁ * Real.sin θ) + x * y₂ * Real.cos θ;
                 y₂ * Real.sin θ, y₂ * Real.cos θ]) *
            (((|t| : ℝ) : ℂ) ^ (s - 1 / 2)) * (((t ^ 2)⁻¹ : ℝ) : ℂ)) =
      (ArchR.centralChar P₂ y₂ * ((|y₂| : ℝ) : ℂ)) * (archWeightCharℝ k₀ (rotK θ) : ℂ) *
        (∫ t : ℝ, W t * ArchR.psi ((-1 : ℝ) * t * x) * D.W (ArchR.diagOne ((-1 : ℝ) * t * y₁ / y₂)) *
           (((|t| : ℝ) : ℂ) ^ (s - 1 / 2)) * (((t ^ 2)⁻¹ : ℝ) : ℂ)) := by
    rw [← integral_const_mul]
    refine integral_congr_ae ?_
    filter_upwards [ae_ne_zero] with t ht
    have hc : (-1 : ℝ) * t ≠ 0 := mul_ne_zero (by norm_num) ht
    rw [LanglandsTunnell.Converse.ArchDatumR.W_diagOne_mul_iwasawa_eq_psi_mul_centralChar_mul_archWeightChar_mul_W_diagOne
      D k₀ hDW hc x hy₁ hy₂ θ (rotK θ) (coe_rotK θ)]
    ring
  rw [hT, archWeightCharℝ_rotK, cos_add_I_sin, col_factor θ y₂ ε' hε,
    show (y₂ * Real.sin θ) ^ 2 + (y₂ * Real.cos θ) ^ 2 = y₂ ^ 2 by nlinarith [Real.sin_sq_add_cos_sq θ],
    mul_pow (Complex.exp ((θ : ℂ) * Complex.I)), mul_pow ((ε' : ℂ) * Complex.I * (y₂ : ℂ))]
  have hph := phase_eq_one m n k₀ ε' θ hcol
  have hcast : (-Complex.I * (-1 : ℂ)) ^ n = (-Complex.I * ((-1 : ℝ) : ℂ)) ^ n := by push_cast; rfl
  rw [hcast]
  linear_combination (ArchR.quasiChar u₀ a₀ (y₁ * y₂)⁻¹ * (((|(y₁ * y₂)⁻¹| ^ 2)⁻¹ : ℝ) : ℂ) *
          ((ArchR.centralChar P₂ y₂ * ((|y₂| : ℝ) : ℂ)) *
            (∫ t : ℝ, W t * ArchR.psi ((-1 : ℝ) * t * x) * D.W (ArchR.diagOne ((-1 : ℝ) * t * y₁ / y₂)) *
               (((|t| : ℝ) : ℂ) ^ (s - 1 / 2)) * (((t ^ 2)⁻¹ : ℝ) : ℂ)) *
            (((((1 / y₁ - 1 / y₂ : ℝ) : ℂ)) + Complex.I * (((x / y₁ : ℝ) : ℂ))) ^ m *
              (Real.exp (-(Real.pi * ((1 + x ^ 2) / y₁ ^ 2 + 1 / y₂ ^ 2))) : ℂ) *
              ((|y₁ * y₂| : ℝ) : ℂ) *
              (-Complex.I * ((-1 : ℝ) : ℂ)) ^ n * ((ε' : ℂ) * Complex.I * (y₂ : ℂ)) ^ n *
              ((1 / 2 : ℂ) * ((Real.pi * (-1 : ℝ) ^ 2 * y₂ ^ 2 : ℝ) : ℂ) ^ (-((cP + P₂.centralExponent + 2 * s + n + 1) / 2)) *
                Complex.Gamma ((cP + P₂.centralExponent + 2 * s + n + 1) / 2)))) *
          ((y₂ ^ 2 * (|y₁ * y₂| ^ 4)⁻¹ : ℝ) : ℂ)) * hph

end K7Theta
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_forall_iwasawaIntegral_eq_const_mul_oneSided_torusPair_add_mirror_of_discreteProfile_conjBlockHarmonic_colHarmonic.K7Rot"

namespace K7F

noncomputable def SGN (a₀ : ZMod 2) (y : ℝ) : ℂ := if a₀ = 0 then (1 : ℂ) else ((SignType.sign y : ℝ) : ℂ)

noncomputable def Gfun {P₂ : RealArchParam} (D : ArchDatumR P₂) (W : ℝ → ℂ) (u cP : ℂ) (a₀ : ZMod 2)
    (m n : ℕ) (ε' : ℝ) (s : ℂ) (q : ℝ × ℝ × ℝ) : ℂ :=
  ArchR.quasiChar u a₀ (q.2.1 * q.2.2)⁻¹ * (((|(q.2.1 * q.2.2)⁻¹| ^ 2)⁻¹ : ℝ) : ℂ) *
    ((ArchR.centralChar P₂ q.2.2 * ((|q.2.2| : ℝ) : ℂ)) *
      (∫ t : ℝ, W t * ArchR.psi ((-1 : ℝ) * t * q.1) * D.W (ArchR.diagOne ((-1 : ℝ) * t * q.2.1 / q.2.2)) *
         (((|t| : ℝ) : ℂ) ^ (s - 1 / 2)) * (((t ^ 2)⁻¹ : ℝ) : ℂ)) *
      (((((1 / q.2.1 - 1 / q.2.2 : ℝ) : ℂ)) + Complex.I * (((q.1 / q.2.1 : ℝ) : ℂ))) ^ m *
        (Real.exp (-(Real.pi * ((1 + q.1 ^ 2) / q.2.1 ^ 2 + 1 / q.2.2 ^ 2))) : ℂ) *
        ((|q.2.1 * q.2.2| : ℝ) : ℂ) *
        (-Complex.I * ((-1 : ℝ) : ℂ)) ^ n * ((ε' : ℂ) * Complex.I * (q.2.2 : ℂ)) ^ n *
        ((1 / 2 : ℂ) * ((Real.pi * (-1 : ℝ) ^ 2 * q.2.2 ^ 2 : ℝ) : ℂ) ^ (-((cP + P₂.centralExponent + 2 * s + n + 1) / 2)) *
          Complex.Gamma ((cP + P₂.centralExponent + 2 * s + n + 1) / 2)))) *
    ((q.2.2 ^ 2 * (|q.2.1 * q.2.2| ^ 4)⁻¹ : ℝ) : ℂ)

noncomputable def Zb (m : ℕ) (t y₁ y₂ : ℝ) : ℂ :=
  ∫ z : ℝ, (((y₁⁻¹ - y₂⁻¹ + t * y₁ : ℝ) : ℂ) + Complex.I * (z : ℂ)) ^ m * (Real.exp (-(Real.pi * z ^ 2)) : ℂ)

noncomputable def Pfun {P₂ : RealArchParam} (D : ArchDatumR P₂) (m : ℕ) (α β γ : ℂ) (t y₁ y₂ : ℝ) : ℂ :=
  ((t : ℝ) : ℂ) ^ α * (Real.exp (-(2 * Real.pi * t)) : ℂ) *
    ((|y₁| : ℝ) : ℂ) ^ β * ((y₂ : ℝ) : ℂ) ^ γ *
    (Real.exp (-(Real.pi * ((y₁ ^ 2)⁻¹ + t ^ 2 * y₁ ^ 2 + (y₂ ^ 2)⁻¹))) : ℂ) *
    D.W (ArchR.diagOne ((-1 : ℝ) * t * y₁ / y₂)) * Zb m t y₁ y₂

end K7F
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_forall_iwasawaIntegral_eq_const_mul_oneSided_torusPair_add_mirror_of_discreteProfile_conjBlockHarmonic_colHarmonic.K7Rot"

namespace K7Collect
open K7F

theorem cpow_ofReal_mul {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (r : ℂ) :
    (((a * b : ℝ) : ℂ)) ^ r = ((a : ℝ) : ℂ) ^ r * ((b : ℝ) : ℂ) ^ r := by
  push_cast
  exact Complex.mul_cpow_ofReal_nonneg ha hb r

theorem cpow_ofReal_inv {a : ℝ} (ha : 0 < a) (r : ℂ) :
    (((a⁻¹ : ℝ) : ℂ)) ^ r = ((a : ℝ) : ℂ) ^ (-r) := by
  rw [Complex.cpow_neg, Complex.ofReal_inv, Complex.inv_cpow _ _ (by
    rw [Complex.arg_ofReal_of_nonneg ha.le]; exact Real.pi_ne_zero.symm)]

theorem cpow_ofReal_sq {a : ℝ} (ha : 0 < a) (r : ℂ) :
    (((a ^ 2 : ℝ) : ℂ)) ^ r = ((a : ℝ) : ℂ) ^ (2 * r) := by
  rw [sq, cpow_ofReal_mul ha.le ha.le, ← Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr ha.ne'), two_mul]

theorem quasiChar_inv_mul (u : ℂ) (a₀ : ZMod 2) {y₁ y₂ : ℝ} (hy₁ : y₁ ≠ 0) (hy₂ : 0 < y₂) :
    ArchR.quasiChar u a₀ (y₁ * y₂)⁻¹ =
      ((|y₁| : ℝ) : ℂ) ^ (-u) * ((y₂ : ℝ) : ℂ) ^ (-u) *
        (if a₀ = 0 then (1 : ℂ) else ((SignType.sign y₁ : ℝ) : ℂ)) := by
  unfold ArchR.quasiChar
  have h1 : |(y₁ * y₂)⁻¹| = |y₁|⁻¹ * y₂⁻¹ := by
    rw [abs_inv, abs_mul, abs_of_pos hy₂, mul_inv]
  have hs : SignType.sign (y₁ * y₂)⁻¹ = SignType.sign y₁ := by
    rcases lt_or_gt_of_ne hy₁ with h | h
    · rw [sign_neg h, sign_neg (inv_lt_zero.mpr (mul_neg_of_neg_of_pos h hy₂))]
    · rw [sign_pos h, sign_pos (inv_pos.mpr (mul_pos h hy₂))]
  rw [h1, hs, cpow_ofReal_mul (inv_nonneg.mpr (abs_nonneg _)) (inv_nonneg.mpr hy₂.le),
    cpow_ofReal_inv (abs_pos.mpr hy₁), cpow_ofReal_inv hy₂]

theorem centralChar_pos (P₂ : RealArchParam) {y₂ : ℝ} (hy₂ : 0 < y₂) :
    ArchR.centralChar P₂ y₂ = ((y₂ : ℝ) : ℂ) ^ P₂.centralExponent := by
  unfold ArchR.centralChar ArchR.quasiChar
  rw [abs_of_pos hy₂, sign_pos hy₂]
  split_ifs <;> simp

theorem collect {P₂ : RealArchParam} (D : ArchDatumR P₂) (W : ℝ → ℂ) (u₀ cP uP : ℂ) (a₀ : ZMod 2)
    (nP m n : ℕ) (hm : m = nP + 1) (ε' : ℝ) (s : ℂ)
    (hWpos : ∀ t : ℝ, 0 < t → W t = (2 : ℂ) * (t : ℂ) ^ (uP + (nP : ℂ) / 2 + 1) * (Real.exp (-(2 * Real.pi * t)) : ℂ))
    (t y₁ y₂ : ℝ) (ht : 0 < t) (hy₁ : y₁ ≠ 0) (hy₂ : 0 < y₂) :
    ArchR.quasiChar (u₀ + 2) a₀ (y₁ * y₂)⁻¹ * (((|(y₁ * y₂)⁻¹| ^ 2)⁻¹ : ℝ) : ℂ) *
        (ArchR.centralChar P₂ y₂ * ((|y₂| : ℝ) : ℂ)) * ((|y₁ * y₂| : ℝ) : ℂ) *
        (-Complex.I * ((-1 : ℝ) : ℂ)) ^ n * ((ε' : ℂ) * Complex.I * (y₂ : ℂ)) ^ n *
        ((1 / 2 : ℂ) * ((Real.pi * (-1 : ℝ) ^ 2 * y₂ ^ 2 : ℝ) : ℂ) ^ (-((cP + P₂.centralExponent + 2 * s + n + 1) / 2)) *
          Complex.Gamma ((cP + P₂.centralExponent + 2 * s + n + 1) / 2)) *
        ((y₂ ^ 2 * (|y₁ * y₂| ^ 4)⁻¹ : ℝ) : ℂ) *
        ((Real.exp (-(Real.pi * (1 / y₁ ^ 2 + 1 / y₂ ^ 2))) : ℂ) * ((|y₁| : ℝ) : ℂ)) *
        (W t * D.W (ArchR.diagOne ((-1 : ℝ) * t * y₁ / y₂)) * (((|t| : ℝ) : ℂ) ^ (s - 1 / 2)) * (((t ^ 2)⁻¹ : ℝ) : ℂ) *
          ((Real.exp (-(Real.pi * (((-1 : ℝ) * t) * y₁) ^ 2)) : ℂ) *
            ∫ z : ℝ, (((1 / y₁ - 1 / y₂ - ((-1 : ℝ) * t) * y₁ : ℝ) : ℂ) + Complex.I * (z : ℂ)) ^ m *
              (Real.exp (-(Real.pi * z ^ 2)) : ℂ)))
      = Complex.Gammaℝ (cP + P₂.centralExponent + 2 * s + n + 1) * (-(ε' : ℂ)) ^ n * SGN a₀ y₁ *
          Pfun D m (s + uP + (m : ℂ) / 2 - 2) (-(u₀ + 2)) (-(cP + 2 * s + u₀ + 1)) t y₁ y₂ := by

  have hy₂0 : y₂ ≠ 0 := hy₂.ne'
  have ha0 : |y₁| ≠ 0 := abs_ne_zero.mpr hy₁
  have hQ2 : ((|(y₁ * y₂)⁻¹| ^ 2)⁻¹ : ℝ) = |y₁| ^ 2 * y₂ ^ 2 := by
    rw [abs_inv, inv_pow, inv_inv, abs_mul, abs_of_pos hy₂, mul_pow]
  have hJ : (y₂ ^ 2 * (|y₁ * y₂| ^ 4)⁻¹ : ℝ) = (|y₁| ^ 4)⁻¹ * (y₂ ^ 2)⁻¹ := by
    rw [abs_mul, abs_of_pos hy₂]; field_simp
  have h14 : (|y₁ * y₂| : ℝ) = |y₁| * y₂ := by rw [abs_mul, abs_of_pos hy₂]
  have hbr : (1 / y₁ - 1 / y₂ - ((-1 : ℝ) * t) * y₁ : ℝ) = y₁⁻¹ - y₂⁻¹ + t * y₁ := by
    simp only [one_div]; ring
  have hE : Real.exp (-(Real.pi * (1 / y₁ ^ 2 + 1 / y₂ ^ 2))) * Real.exp (-(Real.pi * (((-1 : ℝ) * t) * y₁) ^ 2)) =
      Real.exp (-(Real.pi * ((y₁ ^ 2)⁻¹ + t ^ 2 * y₁ ^ 2 + (y₂ ^ 2)⁻¹))) := by
    rw [← Real.exp_add]; congr 1; simp only [one_div]; ring

  set zz : ℂ := cP + P₂.centralExponent + 2 * s + n + 1 with hzz
  have hbase : ((Real.pi * (-1 : ℝ) ^ 2 * y₂ ^ 2 : ℝ) : ℂ) ^ (-(zz / 2)) =
      ((Real.pi : ℝ) : ℂ) ^ (-(zz / 2)) * ((y₂ : ℝ) : ℂ) ^ (-zz) := by
    rw [show (Real.pi * (-1 : ℝ) ^ 2 * y₂ ^ 2 : ℝ) = Real.pi * y₂ ^ 2 by ring,
      cpow_ofReal_mul Real.pi_pos.le (sq_nonneg _), cpow_ofReal_sq hy₂]
    congr 1; ring
  have hGR : Complex.Gammaℝ zz = ((Real.pi : ℝ) : ℂ) ^ (-(zz / 2)) * Complex.Gamma (zz / 2) := by
    rw [Complex.Gammaℝ_def, neg_div]
  have hi : (-Complex.I * ((-1 : ℝ) : ℂ)) ^ n * ((ε' : ℂ) * Complex.I * (y₂ : ℂ)) ^ n =
      (-(ε' : ℂ)) ^ n * ((y₂ : ℝ) : ℂ) ^ n := by
    rw [← mul_pow, ← mul_pow]; congr 1
    have : Complex.I * Complex.I = -1 := Complex.I_mul_I
    push_cast
    linear_combination ((ε' : ℂ) * (y₂ : ℂ)) * this

  have hY0 : ((y₂ : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hy₂0
  have hT0 : ((t : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht.ne'
  have hA0 : ((|y₁| : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ha0
  have hY : ((y₂ : ℝ) : ℂ) ^ (-(u₀ + 2)) * ((y₂ : ℝ) : ℂ) ^ P₂.centralExponent * ((y₂ : ℝ) : ℂ) ^ (-zz) *
      ((y₂ : ℝ) : ℂ) ^ (n + 2) = ((y₂ : ℝ) : ℂ) ^ (-(cP + 2 * s + u₀ + 1)) := by
    have hexp : -(u₀ + 2) + P₂.centralExponent + -zz + ((n + 2 : ℕ) : ℂ) = -(cP + 2 * s + u₀ + 1) := by
      rw [hzz]; push_cast; ring
    rw [← Complex.cpow_natCast, ← Complex.cpow_add _ _ hY0, ← Complex.cpow_add _ _ hY0, ← Complex.cpow_add _ _ hY0, hexp]
  have hmC : (m : ℂ) = (nP : ℂ) + 1 := by rw [hm]; push_cast; ring
  have hT : ((t : ℝ) : ℂ) ^ (uP + (nP : ℂ) / 2 + 1) * ((t : ℝ) : ℂ) ^ (s - 1 / 2) * (((t : ℝ) : ℂ) ^ 2)⁻¹ =
      ((t : ℝ) : ℂ) ^ (s + uP + (m : ℂ) / 2 - 2) := by
    rw [← Complex.cpow_two, ← Complex.cpow_neg, ← Complex.cpow_add _ _ hT0, ← Complex.cpow_add _ _ hT0]
    congr 1; rw [hmC]; ring
  have hA : ((|y₁| : ℝ) : ℂ) ^ 2 * ((|y₁| : ℝ) : ℂ) * ((|y₁| : ℝ) : ℂ) * (((|y₁| : ℝ) : ℂ) ^ 4)⁻¹ = 1 := by
    field_simp
  have hYn : ((y₂ : ℝ) : ℂ) ^ 2 * ((y₂ : ℝ) : ℂ) * ((y₂ : ℝ) : ℂ) * ((y₂ : ℝ) : ℂ) ^ n * (((y₂ : ℝ) : ℂ) ^ 2)⁻¹ =
      ((y₂ : ℝ) : ℂ) ^ (n + 2) := by
    field_simp; ring

  simp only [Pfun, SGN, Zb]
  rw [hWpos t ht, quasiChar_inv_mul (u₀ + 2) a₀ hy₁ hy₂, centralChar_pos P₂ hy₂, abs_of_pos hy₂, abs_of_pos ht,
    hQ2, hJ, h14, hbase, hbr]
  simp only [Complex.ofReal_mul, Complex.ofReal_pow, Complex.ofReal_inv]
  rw [← hY, ← hT, hGR]

  have hE' : ((Real.exp (-(Real.pi * (1 / y₁ ^ 2 + 1 / y₂ ^ 2))) : ℝ) : ℂ) *
      ((Real.exp (-(Real.pi * (((-1 : ℝ) * t) * y₁) ^ 2)) : ℝ) : ℂ) =
      ((Real.exp (-(Real.pi * ((y₁ ^ 2)⁻¹ + t ^ 2 * y₁ ^ 2 + (y₂ ^ 2)⁻¹))) : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul, hE]
  rw [← hE', ← hYn]
  linear_combination (((if a₀ = 0 then (1 : ℂ) else ((SignType.sign y₁ : ℝ) : ℂ)) *
      Complex.Gamma (zz / 2) * ((Real.pi : ℝ) : ℂ) ^ (-(zz / 2)) *
      D.W (ArchR.diagOne ((-1 : ℝ) * t * y₁ / y₂)) *
      (∫ z : ℝ, (((y₁⁻¹ - y₂⁻¹ + t * y₁ : ℝ) : ℂ) + Complex.I * (z : ℂ)) ^ m * (Real.exp (-(Real.pi * z ^ 2)) : ℂ)) *
      (((Real.exp (-(Real.pi * (1 / y₁ ^ 2 + 1 / y₂ ^ 2))) : ℝ) : ℂ) *
        ((Real.exp (-(Real.pi * (((-1 : ℝ) * t) * y₁) ^ 2)) : ℝ) : ℂ)) *
      ((Real.exp (-(2 * Real.pi * t)) : ℝ) : ℂ) *
      ((|y₁| : ℝ) : ℂ) ^ (-(u₀ + 2)) *
      (((y₂ : ℝ) : ℂ) ^ (-(u₀ + 2)) * ((y₂ : ℝ) : ℂ) ^ P₂.centralExponent * ((y₂ : ℝ) : ℂ) ^ (-zz) *
        (((y₂ : ℝ) : ℂ) ^ 2 * ((y₂ : ℝ) : ℂ) * ((y₂ : ℝ) : ℂ) * (((y₂ : ℝ) : ℂ) ^ 2)⁻¹)) *
      (((t : ℝ) : ℂ) ^ (uP + (nP : ℂ) / 2 + 1) * ((t : ℝ) : ℂ) ^ (s - 1 / 2) * (((t : ℝ) : ℂ) ^ 2)⁻¹)) *
      (((|y₁| : ℝ) : ℂ) ^ 2 * ((|y₁| : ℝ) : ℂ) * ((|y₁| : ℝ) : ℂ) * (((|y₁| : ℝ) : ℂ) ^ 4)⁻¹)) * hi
    + (((if a₀ = 0 then (1 : ℂ) else ((SignType.sign y₁ : ℝ) : ℂ)) *
      Complex.Gamma (zz / 2) * ((Real.pi : ℝ) : ℂ) ^ (-(zz / 2)) *
      D.W (ArchR.diagOne ((-1 : ℝ) * t * y₁ / y₂)) *
      (∫ z : ℝ, (((y₁⁻¹ - y₂⁻¹ + t * y₁ : ℝ) : ℂ) + Complex.I * (z : ℂ)) ^ m * (Real.exp (-(Real.pi * z ^ 2)) : ℂ)) *
      (((Real.exp (-(Real.pi * (1 / y₁ ^ 2 + 1 / y₂ ^ 2))) : ℝ) : ℂ) *
        ((Real.exp (-(Real.pi * (((-1 : ℝ) * t) * y₁) ^ 2)) : ℝ) : ℂ)) *
      ((Real.exp (-(2 * Real.pi * t)) : ℝ) : ℂ) *
      ((|y₁| : ℝ) : ℂ) ^ (-(u₀ + 2)) *
      (((y₂ : ℝ) : ℂ) ^ (-(u₀ + 2)) * ((y₂ : ℝ) : ℂ) ^ P₂.centralExponent * ((y₂ : ℝ) : ℂ) ^ (-zz) *
        (((y₂ : ℝ) : ℂ) ^ 2 * ((y₂ : ℝ) : ℂ) * ((y₂ : ℝ) : ℂ) * (((y₂ : ℝ) : ℂ) ^ 2)⁻¹)) *
      (((t : ℝ) : ℂ) ^ (uP + (nP : ℂ) / 2 + 1) * ((t : ℝ) : ℂ) ^ (s - 1 / 2) * (((t : ℝ) : ℂ) ^ 2)⁻¹)) *
      ((-(ε' : ℂ)) ^ n * ((y₂ : ℝ) : ℂ) ^ n)) * hA

end K7Collect
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_forall_iwasawaIntegral_eq_const_mul_oneSided_torusPair_add_mirror_of_discreteProfile_conjBlockHarmonic_colHarmonic.K7Rot"

section
open Complex
namespace K7XS

theorem add_pow_le_two_pow (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) (j : ℕ) :
    (A + B) ^ j ≤ 2 ^ j * (A ^ j + B ^ j) := by
  rcases le_total A B with h | h
  · calc (A + B) ^ j ≤ (2 * B) ^ j := by gcongr; linarith
      _ = 2 ^ j * B ^ j := mul_pow _ _ _
      _ ≤ 2 ^ j * (A ^ j + B ^ j) := by gcongr; have := pow_nonneg hA j; linarith
  · calc (A + B) ^ j ≤ (2 * A) ^ j := by gcongr; linarith
      _ = 2 ^ j * A ^ j := mul_pow _ _ _
      _ ≤ 2 ^ j * (A ^ j + B ^ j) := by gcongr; have := pow_nonneg hB j; linarith

theorem integrable_abs_pow_mul_gauss (j : ℕ) :
    Integrable (fun x : ℝ => |x| ^ j * Real.exp (-(Real.pi * x ^ 2))) := by
  have h := integrable_rpow_mul_exp_neg_mul_sq Real.pi_pos (s := (j : ℝ))
    (by have : (0:ℝ) ≤ j := Nat.cast_nonneg j; linarith)
  have h' : Integrable (fun x : ℝ => x ^ j * Real.exp (-(Real.pi * x ^ 2))) := by
    refine h.congr (Filter.Eventually.of_forall fun x => ?_)
    simp only [Real.rpow_natCast, neg_mul]
  refine (h'.norm).congr (Filter.Eventually.of_forall fun x => ?_)
  simp only [norm_mul, norm_pow, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]

theorem integrable_pow_gauss_cexp (j : ℕ) (ξ : ℝ) :
    Integrable (fun x : ℝ => ((x : ℝ) : ℂ) ^ j * (Real.exp (-(Real.pi * x ^ 2)) : ℂ) *
      Complex.exp (2 * Real.pi * Complex.I * (ξ : ℂ) * (x : ℂ))) := by
  refine (integrable_abs_pow_mul_gauss j).mono' (by fun_prop) (Filter.Eventually.of_forall fun x => ?_)
  rw [norm_mul, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, Complex.norm_of_nonneg (Real.exp_pos _).le,
    Complex.norm_exp]
  have : (2 * (Real.pi : ℂ) * Complex.I * (ξ : ℂ) * (x : ℂ)).re = 0 := by
    simp [Complex.mul_re, Complex.mul_im]
  rw [this, Real.exp_zero, mul_one]

theorem integrable_sub_I_mul_pow_gauss (j : ℕ) (σ : ℝ) :
    Integrable (fun z : ℝ => ((σ : ℂ) - Complex.I * (z : ℂ)) ^ j * (Real.exp (-(Real.pi * z ^ 2)) : ℂ)) := by
  have hmaj : Integrable (fun z : ℝ => (2 : ℝ) ^ j * (|σ| ^ j * Real.exp (-(Real.pi * z ^ 2)) +
      |z| ^ j * Real.exp (-(Real.pi * z ^ 2)))) := by
    refine Integrable.const_mul (Integrable.add ?_ (integrable_abs_pow_mul_gauss j)) _
    have := integrable_exp_neg_mul_sq Real.pi_pos
    refine (this.const_mul (|σ| ^ j)).congr (Filter.Eventually.of_forall fun z => ?_)
    simp only [neg_mul]
  refine hmaj.mono' (by fun_prop) (Filter.Eventually.of_forall fun z => ?_)
  rw [norm_mul, norm_pow, Complex.norm_of_nonneg (Real.exp_pos _).le]
  have h1 : ‖(σ : ℂ) - Complex.I * (z : ℂ)‖ ≤ |σ| + |z| := by
    calc ‖(σ : ℂ) - Complex.I * (z : ℂ)‖ ≤ ‖(σ : ℂ)‖ + ‖Complex.I * (z : ℂ)‖ := norm_sub_le _ _
      _ = |σ| + |z| := by rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Complex.norm_real,
            Real.norm_eq_abs, Real.norm_eq_abs]
  have he : 0 ≤ Real.exp (-(Real.pi * z ^ 2)) := (Real.exp_pos _).le
  calc ‖(σ : ℂ) - Complex.I * (z : ℂ)‖ ^ j * Real.exp (-(Real.pi * z ^ 2))
      ≤ (|σ| + |z|) ^ j * Real.exp (-(Real.pi * z ^ 2)) := by gcongr
    _ ≤ (2 ^ j * (|σ| ^ j + |z| ^ j)) * Real.exp (-(Real.pi * z ^ 2)) := by
        gcongr; exact add_pow_le_two_pow _ _ (abs_nonneg _) (abs_nonneg _) j
    _ = _ := by ring

theorem integral_add_I_mul_pow_mul_gauss_mul_cexp (m : ℕ) (c : ℂ) (ξ : ℝ) :
    ∫ x : ℝ, (c + Complex.I * (x : ℂ)) ^ m * (Real.exp (-(Real.pi * x ^ 2)) : ℂ) *
        Complex.exp (2 * Real.pi * Complex.I * (ξ : ℂ) * (x : ℂ)) =
      (Real.exp (-(Real.pi * ξ ^ 2)) : ℂ) *
        ∫ z : ℝ, (c - (ξ : ℂ) + Complex.I * (z : ℂ)) ^ m * (Real.exp (-(Real.pi * z ^ 2)) : ℂ) := by
  have hL : ∀ x : ℝ, (c + Complex.I * (x : ℂ)) ^ m * (Real.exp (-(Real.pi * x ^ 2)) : ℂ) *
      Complex.exp (2 * Real.pi * Complex.I * (ξ : ℂ) * (x : ℂ)) =
      ∑ k ∈ Finset.range (m + 1), (c ^ k * Complex.I ^ (m - k) * (m.choose k : ℂ)) *
        (((x : ℝ) : ℂ) ^ (m - k) * (Real.exp (-(Real.pi * x ^ 2)) : ℂ) *
          Complex.exp (2 * Real.pi * Complex.I * (ξ : ℂ) * (x : ℂ))) := by
    intro x
    rw [add_pow, Finset.sum_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [mul_pow]; ring
  have hR : ∀ z : ℝ, (c - (ξ : ℂ) + Complex.I * (z : ℂ)) ^ m * (Real.exp (-(Real.pi * z ^ 2)) : ℂ) =
      ∑ k ∈ Finset.range (m + 1), (c ^ k * (-1) ^ (m - k) * (m.choose k : ℂ)) *
        (((ξ : ℂ) - Complex.I * (z : ℂ)) ^ (m - k) * (Real.exp (-(Real.pi * z ^ 2)) : ℂ)) := by
    intro z
    rw [show c - (ξ : ℂ) + Complex.I * (z : ℂ) = c + -((ξ : ℂ) - Complex.I * (z : ℂ)) by ring, add_pow,
      Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [neg_pow]; ring
  simp_rw [hL, hR]
  rw [integral_finsetSum _ (fun k _ => (integrable_pow_gauss_cexp (m - k) ξ).const_mul _),
    integral_finsetSum _ (fun k _ => (integrable_sub_I_mul_pow_gauss (m - k) ξ).const_mul _), Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [integral_const_mul, integral_const_mul,
    LanglandsTunnell.integral_ofReal_pow_mul_exp_neg_pi_mul_sq_mul_cexp_eq_iteratedDeriv (m - k) ξ]
  conv_rhs => rw [mul_left_comm,
    LanglandsTunnell.exp_neg_pi_mul_sq_mul_integral_sub_I_mul_pow_mul_exp_eq_iteratedDeriv (m - k) ξ]
  generalize iteratedDeriv (m - k) (fun η : ℝ => (Real.exp (-(Real.pi * η ^ 2)) : ℂ)) ξ = D
  have hπ : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_pos.ne'
  have key : Complex.I ^ (m - k) * (2 * (Real.pi : ℂ) * Complex.I)⁻¹ ^ (m - k) =
      (-1 : ℂ) ^ (m - k) * (-(2 * (Real.pi : ℂ)))⁻¹ ^ (m - k) := by
    rw [← mul_pow, ← mul_pow]
    congr 1
    field_simp
  linear_combination (c ^ k * (m.choose k : ℂ) * D) * key

theorem integral_block_pow_mul_gaussian_mul_psi (m : ℕ) (y₁ y₂ ξ : ℝ) (hy₁ : y₁ ≠ 0) :
    ∫ x : ℝ, ((((1 / y₁ - 1 / y₂ : ℝ) : ℂ)) + Complex.I * (((x / y₁ : ℝ) : ℂ))) ^ m *
        (Real.exp (-(Real.pi * ((1 + x ^ 2) / y₁ ^ 2 + 1 / y₂ ^ 2))) : ℂ) * ArchR.psi (ξ * x) =
      (Real.exp (-(Real.pi * (1 / y₁ ^ 2 + 1 / y₂ ^ 2))) : ℂ) * ((|y₁| : ℝ) : ℂ) *
        (Real.exp (-(Real.pi * (ξ * y₁) ^ 2)) : ℂ) *
        ∫ z : ℝ, (((1 / y₁ - 1 / y₂ - ξ * y₁ : ℝ) : ℂ) + Complex.I * (z : ℂ)) ^ m *
          (Real.exp (-(Real.pi * z ^ 2)) : ℂ) := by
  have hy₁' : (y₁ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hy₁
  set c : ℂ := ((1 / y₁ - 1 / y₂ : ℝ) : ℂ) with hc
  set g : ℝ → ℂ := fun z => (c + Complex.I * (z : ℂ)) ^ m * (Real.exp (-(Real.pi * z ^ 2)) : ℂ) *
      Complex.exp (2 * Real.pi * Complex.I * ((ξ * y₁ : ℝ) : ℂ) * (z : ℂ)) with hg
  have hsub : ∀ x : ℝ, (c + Complex.I * (((x / y₁ : ℝ) : ℂ))) ^ m *
        (Real.exp (-(Real.pi * ((1 + x ^ 2) / y₁ ^ 2 + 1 / y₂ ^ 2))) : ℂ) * ArchR.psi (ξ * x) =
      (Real.exp (-(Real.pi * (1 / y₁ ^ 2 + 1 / y₂ ^ 2))) : ℂ) * g (y₁⁻¹ * x) := by
    intro x
    simp only [hg, ArchR.psi]
    have e1 : (((x / y₁ : ℝ)) : ℂ) = (((y₁⁻¹ * x : ℝ)) : ℂ) := by push_cast; ring
    have e2 : Real.exp (-(Real.pi * ((1 + x ^ 2) / y₁ ^ 2 + 1 / y₂ ^ 2))) =
        Real.exp (-(Real.pi * (1 / y₁ ^ 2 + 1 / y₂ ^ 2))) * Real.exp (-(Real.pi * (y₁⁻¹ * x) ^ 2)) := by
      rw [← Real.exp_add]; congr 1; field_simp; ring
    have e3 : (2 * (Real.pi : ℂ) * Complex.I * ((ξ * x : ℝ) : ℂ)) =
        2 * Real.pi * Complex.I * ((ξ * y₁ : ℝ) : ℂ) * (((y₁⁻¹ * x : ℝ)) : ℂ) := by
      push_cast; field_simp
    rw [e1, e2, e3]; push_cast; ring
  simp_rw [hsub]
  rw [integral_const_mul, Measure.integral_comp_mul_left g, inv_inv, Complex.real_smul, hg,
    integral_add_I_mul_pow_mul_gauss_mul_cexp m c (ξ * y₁)]
  have : c - ((ξ * y₁ : ℝ) : ℂ) = ((1 / y₁ - 1 / y₂ - ξ * y₁ : ℝ) : ℂ) := by rw [hc]; push_cast; ring
  rw [this]
  push_cast
  ring

theorem integral_torusT_mul_block_mul_gaussian_eq (f W : ℝ → ℂ) (m : ℕ) (s : ℂ) (y₁ y₂ : ℝ) (hy₁ : y₁ ≠ 0)
    (hI : Integrable (fun q : ℝ × ℝ =>
        ((Real.exp (-(Real.pi * (q.1 ^ 2 / y₁ ^ 2))) : ℂ) *
            ((((1 / y₁ - 1 / y₂ : ℝ) : ℂ)) + Complex.I * (((q.1 / y₁ : ℝ) : ℂ))) ^ m *
            ArchR.psi ((-1 : ℝ) * q.2 * q.1)) *
          (W q.2 * f ((-1 : ℝ) * q.2 * y₁ / y₂) * (((|q.2| : ℝ) : ℂ) ^ (s - 1 / 2)) * (((q.2 ^ 2)⁻¹ : ℝ) : ℂ)))
        ((volume : Measure ℝ).prod (volume : Measure ℝ))) :
    ∫ x : ℝ, (∫ t : ℝ, W t * ArchR.psi ((-1 : ℝ) * t * x) * f ((-1 : ℝ) * t * y₁ / y₂) *
          (((|t| : ℝ) : ℂ) ^ (s - 1 / 2)) * (((t ^ 2)⁻¹ : ℝ) : ℂ)) *
        ((((1 / y₁ - 1 / y₂ : ℝ) : ℂ)) + Complex.I * (((x / y₁ : ℝ) : ℂ))) ^ m *
        (Real.exp (-(Real.pi * ((1 + x ^ 2) / y₁ ^ 2 + 1 / y₂ ^ 2))) : ℂ)
      = (Real.exp (-(Real.pi * (1 / y₁ ^ 2 + 1 / y₂ ^ 2))) : ℂ) * ((|y₁| : ℝ) : ℂ) *
        ∫ t : ℝ, W t * f ((-1 : ℝ) * t * y₁ / y₂) * (((|t| : ℝ) : ℂ) ^ (s - 1 / 2)) * (((t ^ 2)⁻¹ : ℝ) : ℂ) *
          ((Real.exp (-(Real.pi * (((-1 : ℝ) * t) * y₁) ^ 2)) : ℂ) *
            ∫ z : ℝ, (((1 / y₁ - 1 / y₂ - ((-1 : ℝ) * t) * y₁ : ℝ) : ℂ) + Complex.I * (z : ℂ)) ^ m *
              (Real.exp (-(Real.pi * z ^ 2)) : ℂ)) := by

  have hE : ∀ x : ℝ, Real.exp (-(Real.pi * ((1 + x ^ 2) / y₁ ^ 2 + 1 / y₂ ^ 2))) =
      Real.exp (-(Real.pi * (1 / y₁ ^ 2 + 1 / y₂ ^ 2))) * Real.exp (-(Real.pi * (x ^ 2 / y₁ ^ 2))) := by
    intro x; rw [← Real.exp_add]; congr 1; field_simp; ring

  set k : ℝ → ℝ → ℂ := fun x t =>
    W t * ArchR.psi ((-1 : ℝ) * t * x) * f ((-1 : ℝ) * t * y₁ / y₂) * (((|t| : ℝ) : ℂ) ^ (s - 1 / 2)) *
      (((t ^ 2)⁻¹ : ℝ) : ℂ) *
      (((((1 / y₁ - 1 / y₂ : ℝ) : ℂ)) + Complex.I * (((x / y₁ : ℝ) : ℂ))) ^ m *
        (Real.exp (-(Real.pi * ((1 + x ^ 2) / y₁ ^ 2 + 1 / y₂ ^ 2))) : ℂ)) with hk
  have hkI : Integrable (Function.uncurry k) ((volume : Measure ℝ).prod (volume : Measure ℝ)) := by
    refine (hI.const_mul ((Real.exp (-(Real.pi * (1 / y₁ ^ 2 + 1 / y₂ ^ 2))) : ℂ))).congr
      (Filter.Eventually.of_forall fun q => ?_)
    simp only [Function.uncurry_def, hk, hE q.1]
    push_cast
    ring
  have h1 : ∀ x : ℝ, (∫ t : ℝ, W t * ArchR.psi ((-1 : ℝ) * t * x) * f ((-1 : ℝ) * t * y₁ / y₂) *
          (((|t| : ℝ) : ℂ) ^ (s - 1 / 2)) * (((t ^ 2)⁻¹ : ℝ) : ℂ)) *
        ((((1 / y₁ - 1 / y₂ : ℝ) : ℂ)) + Complex.I * (((x / y₁ : ℝ) : ℂ))) ^ m *
        (Real.exp (-(Real.pi * ((1 + x ^ 2) / y₁ ^ 2 + 1 / y₂ ^ 2))) : ℂ) = ∫ t : ℝ, k x t := by
    intro x
    rw [mul_assoc, ← integral_mul_const]
  simp_rw [h1]
  rw [integral_integral_swap hkI]
  have h2 : ∀ t : ℝ, (∫ x : ℝ, k x t) =
      (W t * f ((-1 : ℝ) * t * y₁ / y₂) * (((|t| : ℝ) : ℂ) ^ (s - 1 / 2)) * (((t ^ 2)⁻¹ : ℝ) : ℂ)) *
        ∫ x : ℝ, ((((1 / y₁ - 1 / y₂ : ℝ) : ℂ)) + Complex.I * (((x / y₁ : ℝ) : ℂ))) ^ m *
          (Real.exp (-(Real.pi * ((1 + x ^ 2) / y₁ ^ 2 + 1 / y₂ ^ 2))) : ℂ) * ArchR.psi (((-1 : ℝ) * t) * x) := by
    intro t
    rw [← integral_const_mul]
    congr 1; ext x
    simp only [hk, mul_assoc]
    ring
  simp_rw [h2, integral_block_pow_mul_gaussian_mul_psi m y₁ y₂ _ hy₁]
  rw [← integral_const_mul]
  congr 1; ext t
  ring

end K7XS
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_forall_iwasawaIntegral_eq_const_mul_oneSided_torusPair_add_mirror_of_discreteProfile_conjBlockHarmonic_colHarmonic.K7Rot"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_forall_iwasawaIntegral_eq_const_mul_oneSided_torusPair_add_mirror_of_discreteProfile_conjBlockHarmonic_colHarmonic.K7Rot"

namespace K7MT

variable {X Y Z T E : Type*} [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z] [MeasurableSpace T]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

def cyc : Y × Z × X ≃ᵐ X × Y × Z :=
  (MeasurableEquiv.prodAssoc.symm : Y × Z × X ≃ᵐ (Y × Z) × X).trans MeasurableEquiv.prodComm

theorem cyc_apply (p : Y × Z × X) : (cyc p : X × Y × Z) = (p.2.2, p.1, p.2.1) := rfl

theorem measurePreserving_cyc (μ : Measure X) (ν : Measure Y) (ρ : Measure Z)
    [SFinite μ] [SFinite ν] [SFinite ρ] :
    MeasurePreserving (cyc : Y × Z × X ≃ᵐ X × Y × Z) (ν.prod (ρ.prod μ)) (μ.prod (ν.prod ρ)) := by
  have h1 : MeasurePreserving (MeasurableEquiv.prodAssoc.symm : Y × Z × X ≃ᵐ (Y × Z) × X)
      (ν.prod (ρ.prod μ)) ((ν.prod ρ).prod μ) :=
    (MeasureTheory.measurePreserving_prodAssoc ν ρ μ).symm _
  have h2 : MeasurePreserving (MeasurableEquiv.prodComm : (Y × Z) × X ≃ᵐ X × (Y × Z))
      ((ν.prod ρ).prod μ) (μ.prod (ν.prod ρ)) :=
    Measure.measurePreserving_swap
  exact h2.comp h1

theorem integral3_eq_integral_prod (μ : Measure X) (ν : Measure Y) (ρ : Measure Z)
    [SFinite μ] [SFinite ν] [SFinite ρ]
    (f : X × Y × Z → E) (hf : Integrable f (μ.prod (ν.prod ρ))) :
    ∫ x, ∫ y, ∫ z, f (x, y, z) ∂ρ ∂ν ∂μ = ∫ p, f p ∂(μ.prod (ν.prod ρ)) := by
  rw [integral_prod f hf]
  refine integral_congr_ae ?_
  filter_upwards [hf.prod_right_ae] with x hx
  exact (integral_prod _ hx).symm

theorem integral3_cycle (μ : Measure X) (ν : Measure Y) (ρ : Measure Z)
    [SFinite μ] [SFinite ν] [SFinite ρ]
    (f : X × Y × Z → E) (hf : Integrable f (μ.prod (ν.prod ρ))) :
    ∫ x, ∫ y, ∫ z, f (x, y, z) ∂ρ ∂ν ∂μ = ∫ y, ∫ z, ∫ x, f (x, y, z) ∂μ ∂ρ ∂ν := by
  rw [integral3_eq_integral_prod μ ν ρ f hf]
  have hc := measurePreserving_cyc μ ν ρ
  have hf' : Integrable (fun p : Y × Z × X => f (cyc p)) (ν.prod (ρ.prod μ)) :=
    (hc.integrable_comp_emb (cyc).measurableEmbedding).mpr hf
  rw [← hc.integral_comp' f, ← integral3_eq_integral_prod ν ρ μ _ hf']
  rfl

def assoc4 : X × Y × Z × T ≃ᵐ (X × Y × Z) × T :=
  ((MeasurableEquiv.refl X).prodCongr (MeasurableEquiv.prodAssoc.symm : Y × Z × T ≃ᵐ (Y × Z) × T)).trans
    (MeasurableEquiv.prodAssoc.symm : X × (Y × Z) × T ≃ᵐ (X × Y × Z) × T)

theorem assoc4_symm_apply (p : (X × Y × Z) × T) : ((assoc4).symm p : X × Y × Z × T) = (p.1.1, p.1.2.1, p.1.2.2, p.2) := rfl

theorem measurePreserving_assoc4 (μ : Measure X) (ν : Measure Y) (ρ : Measure Z) (τ : Measure T)
    [SFinite μ] [SFinite ν] [SFinite ρ] [SFinite τ] :
    MeasurePreserving (assoc4 : X × Y × Z × T ≃ᵐ (X × Y × Z) × T)
      (μ.prod (ν.prod (ρ.prod τ))) ((μ.prod (ν.prod ρ)).prod τ) := by
  have h1 : MeasurePreserving ((MeasurableEquiv.refl X).prodCongr
      (MeasurableEquiv.prodAssoc.symm : Y × Z × T ≃ᵐ (Y × Z) × T))
      (μ.prod (ν.prod (ρ.prod τ))) (μ.prod ((ν.prod ρ).prod τ)) :=
    (MeasurePreserving.id μ).prod ((MeasureTheory.measurePreserving_prodAssoc ν ρ τ).symm _)
  have h2 : MeasurePreserving (MeasurableEquiv.prodAssoc.symm : X × (Y × Z) × T ≃ᵐ (X × Y × Z) × T)
      (μ.prod ((ν.prod ρ).prod τ)) ((μ.prod (ν.prod ρ)).prod τ) :=
    (MeasureTheory.measurePreserving_prodAssoc μ (ν.prod ρ) τ).symm _
  exact h2.comp h1

theorem integrable_integral_inner4 (μ : Measure X) (ν : Measure Y) (ρ : Measure Z) (τ : Measure T)
    [SFinite μ] [SFinite ν] [SFinite ρ] [SFinite τ]
    (F : X × Y × Z × T → E) (hF : Integrable F (μ.prod (ν.prod (ρ.prod τ)))) :
    Integrable (fun p : X × Y × Z => ∫ t, F (p.1, p.2.1, p.2.2, t) ∂τ) (μ.prod (ν.prod ρ)) := by
  have hc := measurePreserving_assoc4 μ ν ρ τ
  have hF' : Integrable (fun q : (X × Y × Z) × T => F ((assoc4).symm q)) ((μ.prod (ν.prod ρ)).prod τ) :=
    ((hc.symm _).integrable_comp_emb (assoc4).symm.measurableEmbedding).mpr hF
  exact hF'.integral_prod_left

theorem integral3_cycle_inner4 (μ : Measure X) (ν : Measure Y) (ρ : Measure Z) (τ : Measure T)
    [SFinite μ] [SFinite ν] [SFinite ρ] [SFinite τ]
    (F : X × Y × Z × T → E) (hF : Integrable F (μ.prod (ν.prod (ρ.prod τ)))) :
    ∫ x, ∫ y, ∫ z, ∫ t, F (x, y, z, t) ∂τ ∂ρ ∂ν ∂μ = ∫ y, ∫ z, ∫ x, ∫ t, F (x, y, z, t) ∂τ ∂μ ∂ρ ∂ν :=
  integral3_cycle μ ν ρ (fun p : X × Y × Z => ∫ t, F (p.1, p.2.1, p.2.2, t) ∂τ)
    (integrable_integral_inner4 μ ν ρ τ F hF)

end K7MT
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_forall_iwasawaIntegral_eq_const_mul_oneSided_torusPair_add_mirror_of_discreteProfile_conjBlockHarmonic_colHarmonic.K7Rot"

noncomputable section

namespace K9S6
open K7F LanglandsTunnell.Converse.ArchR

section Profile
variable {P₂ : RealArchParam} (D : ArchDatumR P₂)

def Fp (τ : ℝ) : ℂ := D.W (ArchR.diagOne τ)

theorem continuous_diagOneCoords : Continuous fun τ : ℝ => Matrix.of.symm (ArchR.diagOne τ) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  fin_cases i <;> fin_cases j <;>
    simp [ArchR.diagOne, continuous_const, continuous_id']

theorem continuousOn_Fp : ContinuousOn (Fp D) {τ : ℝ | τ ≠ 0} := by
  have hW := D.smooth.continuousOn
  have hmap : MapsTo (fun τ : ℝ => Matrix.of.symm (ArchR.diagOne τ)) {τ : ℝ | τ ≠ 0} ArchR.glSet := by
    intro τ hτ
    show (Matrix.of (Matrix.of.symm (ArchR.diagOne τ))).det ≠ 0
    simpa [ArchR.diagOne, Matrix.det_fin_two] using hτ
  have h := hW.comp (continuous_diagOneCoords).continuousOn hmap
  refine h.congr (fun τ _ => ?_)
  simp [Fp, ArchR.asPi]

theorem measurable_Fp : Measurable (Fp D) :=
  measurable_of_continuousOn_compl_singleton 0 (by rw [Set.compl_singleton_eq]; exact continuousOn_Fp D)

theorem measurable_Fp_neg : Measurable (fun τ : ℝ => Fp D (-τ)) := (measurable_Fp D).comp measurable_neg

theorem exists_bound_Fp : ∃ CF σF : ℝ, 0 ≤ CF ∧ 0 ≤ σF ∧ ∀ τ : ℝ, τ ≠ 0 → ‖Fp D τ‖ ≤ CF * (1 + |τ| ^ (-σF)) := by
  obtain ⟨C₁, hC₁⟩ := D.decay_top 0 0
  obtain ⟨C₂, σ₂, hC₂⟩ := D.decay_zero 0
  have hK1 : ArchR.IsK (1 : Matrix (Fin 2) (Fin 2) ℝ) := Submonoid.one_mem _
  have key : ∀ y : ℝ, ‖iteratedFDerivWithin ℝ 0 (ArchR.asPi D.W) ArchR.glSet (ArchR.diagOneMulCoords y 1)‖ = ‖Fp D y‖ := by
    intro y; rw [norm_iteratedFDerivWithin_zero]; simp [ArchR.asPi, ArchR.diagOneMulCoords, Fp]
  have h1 : ∀ y : ℝ, 1 ≤ |y| → ‖Fp D y‖ ≤ C₁ := by
    intro y hy; have := hC₁ y 1 hK1 hy; rw [key] at this; simpa using this
  have h2 : ∀ y : ℝ, y ≠ 0 → |y| ≤ 1 → ‖Fp D y‖ ≤ C₂ * |y| ^ (-σ₂) := by
    intro y hy hy1; have := hC₂ y 1 hK1 hy hy1; rwa [key] at this
  have hC₁0 : 0 ≤ C₁ := le_trans (norm_nonneg _) (h1 1 (by simp))
  have hC₂0 : 0 ≤ C₂ := by
    have := h2 1 one_ne_zero (by simp)
    simp only [abs_one, Real.one_rpow, mul_one] at this
    exact le_trans (norm_nonneg _) this
  refine ⟨max C₁ C₂, max σ₂ 0, hC₁0.trans (le_max_left _ _), le_max_right _ _, fun τ hτ => ?_⟩
  have hM : 0 ≤ max C₁ C₂ := hC₁0.trans (le_max_left _ _)
  have hτp : 0 < |τ| := abs_pos.2 hτ
  have hr : 0 ≤ |τ| ^ (-max σ₂ 0) := Real.rpow_nonneg hτp.le _
  by_cases h : 1 ≤ |τ|
  · calc ‖Fp D τ‖ ≤ C₁ := h1 τ h
      _ ≤ max C₁ C₂ := le_max_left _ _
      _ ≤ max C₁ C₂ * (1 + |τ| ^ (-max σ₂ 0)) := le_mul_of_one_le_right hM (by linarith)
  · push Not at h
    calc ‖Fp D τ‖ ≤ C₂ * |τ| ^ (-σ₂) := h2 τ hτ h.le
      _ ≤ max C₁ C₂ * |τ| ^ (-max σ₂ 0) := by
          refine mul_le_mul (le_max_right _ _) ?_ (Real.rpow_nonneg hτp.le _) hM
          exact Real.rpow_le_rpow_of_exponent_ge hτp h.le (neg_le_neg (le_max_left _ _))
      _ ≤ max C₁ C₂ * (1 + |τ| ^ (-max σ₂ 0)) := by nlinarith

theorem bound_Fp_neg {CF σF : ℝ} (h : ∀ τ : ℝ, τ ≠ 0 → ‖Fp D τ‖ ≤ CF * (1 + |τ| ^ (-σF))) :
    ∀ τ : ℝ, τ ≠ 0 → ‖Fp D (-τ)‖ ≤ CF * (1 + |τ| ^ (-σF)) := by
  intro τ hτ; have := h (-τ) (neg_ne_zero.2 hτ); rwa [abs_neg] at this

end Profile
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_forall_iwasawaIntegral_eq_const_mul_oneSided_torusPair_add_mirror_of_discreteProfile_conjBlockHarmonic_colHarmonic.K7Rot"

def Bm (m : ℕ) (p q r z : ℝ) : ℂ := (((p - q + r : ℝ) : ℂ) + Complex.I * (z : ℂ)) ^ m
def Bm' (m : ℕ) (p q r z : ℝ) : ℂ := (((-p - q - r : ℝ) : ℂ) + Complex.I * (z : ℂ)) ^ m

theorem measurable_Bm (m : ℕ) : Measurable fun x : ℝ × ℝ × ℝ × ℝ => Bm m x.1 x.2.1 x.2.2.1 x.2.2.2 := by
  unfold Bm
  refine Measurable.pow_const ((Complex.measurable_ofReal.comp ?_).add
    (measurable_const.mul (Complex.measurable_ofReal.comp (measurable_snd.comp (measurable_snd.comp measurable_snd))))) m
  exact (measurable_fst.sub (measurable_fst.comp measurable_snd)).add (measurable_fst.comp (measurable_snd.comp measurable_snd))

theorem measurable_Bm' (m : ℕ) : Measurable fun x : ℝ × ℝ × ℝ × ℝ => Bm' m x.1 x.2.1 x.2.2.1 x.2.2.2 := by
  unfold Bm'
  refine Measurable.pow_const ((Complex.measurable_ofReal.comp ?_).add
    (measurable_const.mul (Complex.measurable_ofReal.comp (measurable_snd.comp (measurable_snd.comp measurable_snd))))) m
  exact (measurable_fst.neg.sub (measurable_fst.comp measurable_snd)).sub (measurable_fst.comp (measurable_snd.comp measurable_snd))

theorem sum_le_prod_one_add (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) :
    a + b + c + d ≤ (1 + a) * (1 + b) * (1 + c) * (1 + d) := by
  have h1 : 1 + a + b ≤ (1 + a) * (1 + b) := by nlinarith
  have h2 : (1 + a + b) * (1 + c) ≤ (1 + a) * (1 + b) * (1 + c) := mul_le_mul_of_nonneg_right h1 (by linarith)
  have h3 : 1 + a + b + c ≤ (1 + a + b) * (1 + c) := by nlinarith
  have h4 : (1 + a + b + c) * (1 + d) ≤ (1 + a) * (1 + b) * (1 + c) * (1 + d) :=
    mul_le_mul_of_nonneg_right (h3.trans h2) (by linarith)
  have h5 : 1 + a + b + c + d ≤ (1 + a + b + c) * (1 + d) := by nlinarith
  linarith

theorem norm_lin_add_I_pow_le (m : ℕ) (L p q r z : ℝ) (hL : |L| ≤ |p| + |q| + |r|) :
    ‖((L : ℝ) : ℂ) + Complex.I * (z : ℂ)‖ ^ m ≤
      1 * (1 + |p|) ^ m * (1 + |q|) ^ m * (1 + |r|) ^ m * (1 + |z|) ^ m := by
  have h1 : ‖((L : ℝ) : ℂ) + Complex.I * (z : ℂ)‖ ≤ (1 + |p|) * (1 + |q|) * (1 + |r|) * (1 + |z|) := by
    calc ‖((L : ℝ) : ℂ) + Complex.I * (z : ℂ)‖ ≤ ‖((L : ℝ) : ℂ)‖ + ‖Complex.I * (z : ℂ)‖ := norm_add_le _ _
      _ = |L| + |z| := by rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs]
      _ ≤ |p| + |q| + |r| + |z| := by linarith
      _ ≤ _ := sum_le_prod_one_add _ _ _ _ (abs_nonneg _) (abs_nonneg _) (abs_nonneg _) (abs_nonneg _)
  calc ‖((L : ℝ) : ℂ) + Complex.I * (z : ℂ)‖ ^ m ≤ ((1 + |p|) * (1 + |q|) * (1 + |r|) * (1 + |z|)) ^ m :=
        pow_le_pow_left₀ (norm_nonneg _) h1 m
    _ = _ := by rw [mul_pow, mul_pow, mul_pow, one_mul]

theorem bound_Bm (m : ℕ) (p q r z : ℝ) :
    ‖Bm m p q r z‖ ≤ 1 * (1 + |p|) ^ m * (1 + |q|) ^ m * (1 + |r|) ^ m * (1 + |z|) ^ m := by
  unfold Bm; rw [norm_pow]
  refine norm_lin_add_I_pow_le m _ p q r z ?_
  calc |p - q + r| ≤ |p - q| + |r| := abs_add_le _ _
    _ ≤ |p| + |q| + |r| := by linarith [abs_sub p q]

theorem bound_Bm' (m : ℕ) (p q r z : ℝ) :
    ‖Bm' m p q r z‖ ≤ 1 * (1 + |p|) ^ m * (1 + |q|) ^ m * (1 + |r|) ^ m * (1 + |z|) ^ m := by
  unfold Bm'; rw [norm_pow]
  refine norm_lin_add_I_pow_le m _ p q r z ?_
  calc |-p - q - r| = |-(p + q + r)| := by ring_nf
    _ = |p + q + r| := abs_neg _
    _ ≤ |p + q| + |r| := abs_add_le _ _
    _ ≤ |p| + |q| + |r| := by linarith [abs_add_le p q]

local notation "μ3" => Measure.prod (Measure.restrict (volume : Measure ℝ) (Ioi (0:ℝ)))
  (Measure.prod (Measure.restrict (volume : Measure ℝ) (Iio (0:ℝ))) (Measure.restrict (volume : Measure ℝ) (Ioi (0:ℝ))))

theorem ae_mu3 : ∀ᵐ p : ℝ × ℝ × ℝ ∂μ3, 0 < p.1 ∧ p.2.1 < 0 ∧ 0 < p.2.2 := by
  have h1 : ∀ᵐ t : ℝ ∂(Measure.restrict volume (Ioi (0:ℝ))), 0 < t := ae_restrict_mem measurableSet_Ioi
  have h2 : ∀ᵐ y : ℝ ∂(Measure.restrict volume (Iio (0:ℝ))), y < 0 := ae_restrict_mem measurableSet_Iio
  have hB : ∀ᵐ q : ℝ × ℝ ∂(Measure.prod (Measure.restrict volume (Iio (0:ℝ))) (Measure.restrict volume (Ioi (0:ℝ)))),
      q.1 < 0 ∧ 0 < q.2 :=
    ((Measure.quasiMeasurePreserving_fst).ae h2).and ((Measure.quasiMeasurePreserving_snd).ae h1)
  exact ((Measure.quasiMeasurePreserving_fst).ae h1).and ((Measure.quasiMeasurePreserving_snd).ae hB)

theorem SGN_of_neg (a₀ : ZMod 2) {y : ℝ} (hy : y < 0) : SGN a₀ y = (-1 : ℂ) ^ a₀.val := by
  unfold SGN
  by_cases h : a₀ = 0
  · simp [h]
  · have h1 : a₀ = 1 := by
      fin_cases a₀
      · exact absurd rfl h
      · rfl
    subst h1
    simp [sign_neg hy, ZMod.val_one]

theorem SGN_of_pos (a₀ : ZMod 2) {y : ℝ} (hy : 0 < y) : SGN a₀ y = 1 := by
  unfold SGN
  by_cases h : a₀ = 0
  · simp [h]
  · simp [h, sign_pos hy]

theorem integrableOn_Ioi_of_comp_neg_Iio {E : Type*} [NormedAddCommGroup E] (F : ℝ → E)
    (hF : IntegrableOn (fun t => F (-t)) (Iio 0)) : IntegrableOn F (Ioi 0) := by
  rw [← (Measure.measurePreserving_neg (volume : Measure ℝ)).integrableOn_comp_preimage
    (Homeomorph.neg ℝ).measurableEmbedding]
  simpa only [Function.comp_def, neg_preimage, neg_Ioi, neg_zero] using hF

end K9S6
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_forall_iwasawaIntegral_eq_const_mul_oneSided_torusPair_add_mirror_of_discreteProfile_conjBlockHarmonic_colHarmonic.K7Rot"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_forall_iwasawaIntegral_eq_const_mul_oneSided_torusPair_add_mirror_of_discreteProfile_conjBlockHarmonic_colHarmonic.K7Rot"

namespace K7S6
open K7F K9S6 LanglandsTunnell.Converse.ArchR

theorem assemble {P₂ : RealArchParam} (D : ArchDatumR P₂) (W : ℝ → ℂ) (u₀ cP uP : ℂ) (a₀ : ZMod 2)
    (nP m n : ℕ) (hm : m = nP + 1) (ε' : ℝ)
    (hWpos : ∀ t : ℝ, 0 < t → W t = (2 : ℂ) * (t : ℂ) ^ (uP + (nP : ℂ) / 2 + 1) * (Real.exp (-(2 * Real.pi * t)) : ℂ))
    (hWneg : ∀ t : ℝ, t < 0 → W t = 0) :
    ∃ σ₂ : ℝ, ∀ s : ℂ, σ₂ < s.re →
      (∀ y₁ : ℝ, y₁ ≠ 0 → ∀ y₂ : ℝ, 0 < y₂ →
        ∫ x : ℝ, Gfun D W (u₀ + 2) cP a₀ m n ε' s (x, y₁, y₂) =
          Complex.Gammaℝ (cP + P₂.centralExponent + 2 * s + n + 1) * (-(ε' : ℂ)) ^ n * SGN a₀ y₁ *
            ∫ t in Ioi (0 : ℝ), Pfun D m (s + uP + (m : ℂ) / 2 - 2) (-(u₀ + 2)) (-(cP + 2 * s + u₀ + 1)) t y₁ y₂) →
      ((2 * Real.pi : ℝ) : ℂ) * ∫ y₁ : ℝ, ∫ y₂ in Ioi (0 : ℝ), ∫ x : ℝ, Gfun D W (u₀ + 2) cP a₀ m n ε' s (x, y₁, y₂)
        = (Real.pi : ℂ) * Complex.Gammaℝ (cP + P₂.centralExponent + 2 * s + (n : ℂ) + 1) *
          ((-(ε' : ℂ)) ^ n) * (2 : ℂ) *
        ((-1 : ℂ) ^ (a₀.val) *
          (∫ t in Ioi (0 : ℝ), ∫ y₁ in Iio (0 : ℝ), ∫ y₂ in Ioi (0 : ℝ),
            ((t : ℝ) : ℂ) ^ (s + uP + (m : ℂ) / 2 - 2) * (Real.exp (-(2 * Real.pi * t)) : ℂ) *
              ((|y₁| : ℝ) : ℂ) ^ (-(u₀ + 2)) * ((y₂ : ℝ) : ℂ) ^ (-(cP + 2 * s + u₀ + 1)) *
              (Real.exp (-(Real.pi * ((y₁ ^ 2)⁻¹ + t ^ 2 * y₁ ^ 2 + (y₂ ^ 2)⁻¹))) : ℂ) *
              D.W (ArchR.diagOne (t * |y₁| / y₂)) *
              (∫ z : ℝ, (((y₁⁻¹ - y₂⁻¹ + t * y₁ : ℝ) : ℂ) + Complex.I * (z : ℂ)) ^ m *
                (Real.exp (-(Real.pi * z ^ 2)) : ℂ))) +
         (∫ t in Ioi (0 : ℝ), ∫ y₁ in Iio (0 : ℝ), ∫ y₂ in Ioi (0 : ℝ),
            ((t : ℝ) : ℂ) ^ (s + uP + (m : ℂ) / 2 - 2) * (Real.exp (-(2 * Real.pi * t)) : ℂ) *
              ((|y₁| : ℝ) : ℂ) ^ (-(u₀ + 2)) * ((y₂ : ℝ) : ℂ) ^ (-(cP + 2 * s + u₀ + 1)) *
              (Real.exp (-(Real.pi * ((y₁ ^ 2)⁻¹ + t ^ 2 * y₁ ^ 2 + (y₂ ^ 2)⁻¹))) : ℂ) *
              D.W (ArchR.diagOne (-(t * |y₁| / y₂))) *
              (∫ z : ℝ, (((-y₁⁻¹ - y₂⁻¹ - t * y₁ : ℝ) : ℂ) + Complex.I * (z : ℂ)) ^ m *
                (Real.exp (-(Real.pi * z ^ 2)) : ℂ)))) := by

  obtain ⟨CF, σF, hCF, hσF, hbF⟩ := K9S6.exists_bound_Fp D
  obtain ⟨σ₀, hσ₀⟩ :=
    LanglandsTunnell.exists_forall_integrable_oneSided_torusPair_integrand_of_torusBound_of_polyBound
      (-(u₀ + 2)) (K9S6.Fp D) (K9S6.measurable_Fp D) CF σF hσF hbF (K9S6.Bm m) (K9S6.measurable_Bm m) 1 m
      (K9S6.bound_Bm m)
  obtain ⟨σ₀', hσ₀'⟩ :=
    LanglandsTunnell.exists_forall_integrable_oneSided_torusPair_integrand_of_torusBound_of_polyBound
      (-(u₀ + 2)) (fun τ => K9S6.Fp D (-τ)) (K9S6.measurable_Fp_neg D) CF σF hσF (K9S6.bound_Fp_neg D hbF)
      (K9S6.Bm' m) (K9S6.measurable_Bm' m) 1 m (K9S6.bound_Bm' m)
  refine ⟨|σ₀| + |σ₀'| + |uP.re| + |cP.re| + |u₀.re| + 3, fun s hs hrow => ?_⟩
  have ha0 := le_abs_self σ₀; have ha0' := le_abs_self σ₀'
  have hb0 := neg_abs_le σ₀; have hb0' := neg_abs_le σ₀'
  have h1 := neg_abs_le uP.re; have h2 := le_abs_self cP.re; have h3 := le_abs_self u₀.re
  have h2' := neg_abs_le cP.re; have h3' := neg_abs_le u₀.re
  have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  have hn1 := abs_nonneg σ₀; have hn2 := abs_nonneg σ₀'; have hn3 := abs_nonneg uP.re
  have hn4 := abs_nonneg cP.re; have hn5 := abs_nonneg u₀.re

  set α : ℂ := s + uP + (m : ℂ) / 2 - 2 with hα
  set β : ℂ := -(u₀ + 2) with hβ
  set γ : ℂ := -(cP + 2 * s + u₀ + 1) with hγ
  have hαre : α.re = s.re + uP.re + (m : ℝ) / 2 - 2 := by
    rw [hα]; simp
  have hγre : γ.re = -(cP.re + 2 * s.re + u₀.re + 1) := by
    rw [hγ]; simp
  have hα1 : σ₀ < α.re := by rw [hαre]; linarith
  have hα2 : σ₀' < α.re := by rw [hαre]; linarith
  have hγ1 : γ.re < -σ₀ := by rw [hγre]; linarith
  have hγ2 : γ.re < -σ₀' := by rw [hγre]; linarith
  have I4 := hσ₀ α γ hα1 hγ1
  have I4' := hσ₀' α γ hα2 hγ2
  set P : ℝ → ℝ → ℝ → ℂ := fun t y₁ y₂ => Pfun D m α β γ t y₁ y₂ with hP

  have I3 : Integrable (fun p : ℝ × ℝ × ℝ => P p.1 p.2.1 p.2.2)
      (Measure.prod (Measure.restrict volume (Ioi (0:ℝ)))
        (Measure.prod (Measure.restrict volume (Iio (0:ℝ))) (Measure.restrict volume (Ioi (0:ℝ))))) := by
    have h := K7MT.integrable_integral_inner4 (Measure.restrict volume (Ioi (0:ℝ))) (Measure.restrict volume (Iio (0:ℝ)))
      (Measure.restrict volume (Ioi (0:ℝ))) (volume : Measure ℝ) _ I4
    refine h.congr ?_
    filter_upwards [K9S6.ae_mu3] with p hp
    obtain ⟨t, y₁, y₂⟩ := p
    obtain ⟨ht, hy₁, hy₂⟩ := hp
    simp only at ht hy₁ hy₂
    have e1 : (-1 : ℝ) * t * y₁ / y₂ = t * |y₁| / y₂ := by rw [abs_of_neg hy₁]; ring
    simp only [hP, Pfun, Zb, K9S6.Fp, K9S6.Bm, e1]
    rw [integral_const_mul]
  have I3' : Integrable (fun p : ℝ × ℝ × ℝ => P p.1 (-p.2.1) p.2.2)
      (Measure.prod (Measure.restrict volume (Ioi (0:ℝ)))
        (Measure.prod (Measure.restrict volume (Iio (0:ℝ))) (Measure.restrict volume (Ioi (0:ℝ))))) := by
    have h := K7MT.integrable_integral_inner4 (Measure.restrict volume (Ioi (0:ℝ))) (Measure.restrict volume (Iio (0:ℝ)))
      (Measure.restrict volume (Ioi (0:ℝ))) (volume : Measure ℝ) _ I4'
    refine h.congr ?_
    filter_upwards [K9S6.ae_mu3] with p hp
    obtain ⟨t, y₁, y₂⟩ := p
    obtain ⟨ht, hy₁, hy₂⟩ := hp
    simp only at ht hy₁ hy₂
    have e1 : (-1 : ℝ) * t * -y₁ / y₂ = -(t * |y₁| / y₂) := by rw [abs_of_neg hy₁]; ring
    have e2 : ((-y₁)⁻¹ - y₂⁻¹ + t * -y₁ : ℝ) = -y₁⁻¹ - y₂⁻¹ - t * y₁ := by rw [inv_neg]; ring
    simp only [hP, Pfun, Zb, K9S6.Fp, K9S6.Bm', e1, e2, abs_neg, neg_sq]
    rw [integral_const_mul]

  set H : ℝ → ℂ := fun y₁ => ∫ y₂ in Ioi (0:ℝ), ∫ t in Ioi (0:ℝ), P t y₁ y₂ with hH
  have Hneg : IntegrableOn H (Iio 0) := by
    have hc := K7MT.measurePreserving_cyc (Measure.restrict volume (Ioi (0:ℝ))) (Measure.restrict volume (Iio (0:ℝ)))
      (Measure.restrict volume (Ioi (0:ℝ)))
    have I3c : Integrable (fun q : ℝ × ℝ × ℝ => P q.2.2 q.1 q.2.1)
        (Measure.prod (Measure.restrict volume (Iio (0:ℝ)))
          (Measure.prod (Measure.restrict volume (Ioi (0:ℝ))) (Measure.restrict volume (Ioi (0:ℝ))))) :=
      (hc.integrable_comp_emb (K7MT.cyc).measurableEmbedding).mpr I3
    have Hl := I3c.integral_prod_left
    refine Hl.congr ?_
    filter_upwards [I3c.prod_right_ae] with y₁ hy
    simp only [hH]
    exact integral_prod _ hy
  have Hpos' : IntegrableOn (fun y₁ => H (-y₁)) (Iio 0) := by
    have hc := K7MT.measurePreserving_cyc (Measure.restrict volume (Ioi (0:ℝ))) (Measure.restrict volume (Iio (0:ℝ)))
      (Measure.restrict volume (Ioi (0:ℝ)))
    have I3c : Integrable (fun q : ℝ × ℝ × ℝ => P q.2.2 (-q.1) q.2.1)
        (Measure.prod (Measure.restrict volume (Iio (0:ℝ)))
          (Measure.prod (Measure.restrict volume (Ioi (0:ℝ))) (Measure.restrict volume (Ioi (0:ℝ))))) :=
      (hc.integrable_comp_emb (K7MT.cyc).measurableEmbedding).mpr I3'
    have Hl := I3c.integral_prod_left
    refine Hl.congr ?_
    filter_upwards [I3c.prod_right_ae] with y₁ hy
    simp only [hH]
    exact integral_prod _ hy
  have Hpos : IntegrableOn H (Ioi 0) := K9S6.integrableOn_Ioi_of_comp_neg_Iio H Hpos'

  set Cst : ℂ := Complex.Gammaℝ (cP + P₂.centralExponent + 2 * s + n + 1) * (-(ε' : ℂ)) ^ n with hCst
  have hA : (∫ y₁ : ℝ, ∫ y₂ in Ioi (0 : ℝ), ∫ x : ℝ, Gfun D W (u₀ + 2) cP a₀ m n ε' s (x, y₁, y₂)) =
      ∫ y₁ : ℝ, Cst * (SGN a₀ y₁ * H y₁) := by
    refine integral_congr_ae ?_
    have hae : ∀ᵐ y₁ : ℝ ∂(volume : Measure ℝ), y₁ ≠ 0 := by
      have : ({0}ᶜ : Set ℝ) ∈ ae (volume : Measure ℝ) := compl_mem_ae_iff.2 (measure_singleton 0)
      filter_upwards [this] with x hx
      simpa using hx
    filter_upwards [hae] with y₁ hy₁
    rw [setIntegral_congr_fun measurableSet_Ioi (fun y₂ (hy₂ : (0:ℝ) < y₂) => hrow y₁ hy₁ y₂ hy₂), integral_const_mul,
      hH, mul_assoc]

  have hF_Iio : IntegrableOn (fun y₁ => SGN a₀ y₁ * H y₁) (Iio 0) := by
    refine IntegrableOn.congr_fun (Hneg.const_mul ((-1 : ℂ) ^ a₀.val)) (fun y₁ (hy₁ : y₁ < 0) => ?_) measurableSet_Iio
    rw [K9S6.SGN_of_neg a₀ hy₁]
  have hF_Iic : IntegrableOn (fun y₁ => SGN a₀ y₁ * H y₁) (Iic 0) := by
    first
      | exact hF_Iio.congr_set_ae Iio_ae_eq_Iic
      | exact hF_Iio.congr_set_ae Iio_ae_eq_Iic.symm
  have hF_Ioi : IntegrableOn (fun y₁ => SGN a₀ y₁ * H y₁) (Ioi 0) := by
    refine IntegrableOn.congr_fun Hpos (fun y₁ (hy₁ : (0:ℝ) < y₁) => ?_) measurableSet_Ioi
    rw [K9S6.SGN_of_pos a₀ hy₁, one_mul]
  have hB : (∫ y₁ : ℝ, Cst * (SGN a₀ y₁ * H y₁)) =
      Cst * ((-1 : ℂ) ^ a₀.val * (∫ y₁ in Iio (0:ℝ), H y₁) + ∫ y₁ in Iio (0:ℝ), H (-y₁)) := by
    rw [integral_const_mul, ← intervalIntegral.integral_Iic_add_Ioi hF_Iic hF_Ioi,
      setIntegral_congr_set Iio_ae_eq_Iic.symm]
    congr 1
    congr 1
    · rw [← integral_const_mul]
      exact setIntegral_congr_fun measurableSet_Iio (fun y₁ (hy₁ : y₁ < 0) => by rw [K9S6.SGN_of_neg a₀ hy₁])
    · rw [setIntegral_congr_fun measurableSet_Ioi (fun y₁ (hy₁ : (0:ℝ) < y₁) => by rw [K9S6.SGN_of_pos a₀ hy₁, one_mul]),
        setIntegral_congr_set (Iio_ae_eq_Iic : Iio (0:ℝ) =ᵐ[volume] Iic 0), integral_comp_neg_Iic, neg_zero]

  have hIneg : (∫ y₁ in Iio (0:ℝ), H y₁) =
      ∫ t in Ioi (0 : ℝ), ∫ y₁ in Iio (0 : ℝ), ∫ y₂ in Ioi (0 : ℝ),
            ((t : ℝ) : ℂ) ^ (s + uP + (m : ℂ) / 2 - 2) * (Real.exp (-(2 * Real.pi * t)) : ℂ) *
              ((|y₁| : ℝ) : ℂ) ^ (-(u₀ + 2)) * ((y₂ : ℝ) : ℂ) ^ (-(cP + 2 * s + u₀ + 1)) *
              (Real.exp (-(Real.pi * ((y₁ ^ 2)⁻¹ + t ^ 2 * y₁ ^ 2 + (y₂ ^ 2)⁻¹))) : ℂ) *
              D.W (ArchR.diagOne (t * |y₁| / y₂)) *
              (∫ z : ℝ, (((y₁⁻¹ - y₂⁻¹ + t * y₁ : ℝ) : ℂ) + Complex.I * (z : ℂ)) ^ m *
                (Real.exp (-(Real.pi * z ^ 2)) : ℂ)) := by
    have hcyc := K7MT.integral3_cycle (Measure.restrict volume (Ioi (0:ℝ))) (Measure.restrict volume (Iio (0:ℝ)))
      (Measure.restrict volume (Ioi (0:ℝ))) (fun p : ℝ × ℝ × ℝ => P p.1 p.2.1 p.2.2) I3
    simp only [hH]
    rw [← hcyc]
    refine setIntegral_congr_fun measurableSet_Ioi (fun t _ => ?_)
    refine setIntegral_congr_fun measurableSet_Iio (fun y₁ (hy₁ : y₁ < 0) => ?_)
    refine setIntegral_congr_fun measurableSet_Ioi (fun y₂ _ => ?_)
    have e1 : (-1 : ℝ) * t * y₁ / y₂ = t * |y₁| / y₂ := by rw [abs_of_neg hy₁]; ring
    simp only [hP, Pfun, Zb, e1]
    rw [hα, hβ, hγ]
  have hIpos : (∫ y₁ in Iio (0:ℝ), H (-y₁)) =
      ∫ t in Ioi (0 : ℝ), ∫ y₁ in Iio (0 : ℝ), ∫ y₂ in Ioi (0 : ℝ),
            ((t : ℝ) : ℂ) ^ (s + uP + (m : ℂ) / 2 - 2) * (Real.exp (-(2 * Real.pi * t)) : ℂ) *
              ((|y₁| : ℝ) : ℂ) ^ (-(u₀ + 2)) * ((y₂ : ℝ) : ℂ) ^ (-(cP + 2 * s + u₀ + 1)) *
              (Real.exp (-(Real.pi * ((y₁ ^ 2)⁻¹ + t ^ 2 * y₁ ^ 2 + (y₂ ^ 2)⁻¹))) : ℂ) *
              D.W (ArchR.diagOne (-(t * |y₁| / y₂))) *
              (∫ z : ℝ, (((-y₁⁻¹ - y₂⁻¹ - t * y₁ : ℝ) : ℂ) + Complex.I * (z : ℂ)) ^ m *
                (Real.exp (-(Real.pi * z ^ 2)) : ℂ)) := by
    have hcyc := K7MT.integral3_cycle (Measure.restrict volume (Ioi (0:ℝ))) (Measure.restrict volume (Iio (0:ℝ)))
      (Measure.restrict volume (Ioi (0:ℝ))) (fun p : ℝ × ℝ × ℝ => P p.1 (-p.2.1) p.2.2) I3'
    simp only [hH]
    rw [← hcyc]
    refine setIntegral_congr_fun measurableSet_Ioi (fun t _ => ?_)
    refine setIntegral_congr_fun measurableSet_Iio (fun y₁ (hy₁ : y₁ < 0) => ?_)
    refine setIntegral_congr_fun measurableSet_Ioi (fun y₂ _ => ?_)
    have e1 : (-1 : ℝ) * t * -y₁ / y₂ = -(t * |y₁| / y₂) := by rw [abs_of_neg hy₁]; ring
    have e2 : ((-y₁)⁻¹ - y₂⁻¹ + t * -y₁ : ℝ) = -y₁⁻¹ - y₂⁻¹ - t * y₁ := by rw [inv_neg]; ring
    simp only [hP, Pfun, Zb, e1, e2, abs_neg, neg_sq]
    rw [hα, hβ, hγ]
  rw [hA, hB, hIneg, hIpos, hCst]
  push_cast
  ring

end K7S6
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_forall_iwasawaIntegral_eq_const_mul_oneSided_torusPair_add_mirror_of_discreteProfile_conjBlockHarmonic_colHarmonic.K7Rot"

namespace K8S5
open K7F

noncomputable def Cst {P₂ : RealArchParam} (u₀ cP : ℂ) (a₀ : ZMod 2) (n : ℕ) (ε' : ℝ) (s : ℂ) (y₁ y₂ : ℝ) : ℂ :=
  ArchR.quasiChar (u₀ + 2) a₀ (y₁ * y₂)⁻¹ * (((|(y₁ * y₂)⁻¹| ^ 2)⁻¹ : ℝ) : ℂ) *
        (ArchR.centralChar P₂ y₂ * ((|y₂| : ℝ) : ℂ)) * ((|y₁ * y₂| : ℝ) : ℂ) *
        (-Complex.I * ((-1 : ℝ) : ℂ)) ^ n * ((ε' : ℂ) * Complex.I * (y₂ : ℂ)) ^ n *
        ((1 / 2 : ℂ) * ((Real.pi * (-1 : ℝ) ^ 2 * y₂ ^ 2 : ℝ) : ℂ) ^ (-((cP + P₂.centralExponent + 2 * s + n + 1) / 2)) *
          Complex.Gamma ((cP + P₂.centralExponent + 2 * s + n + 1) / 2)) *
        ((y₂ ^ 2 * (|y₁ * y₂| ^ 4)⁻¹ : ℝ) : ℂ)

theorem Gfun_eq_Cst_mul {P₂ : RealArchParam} (D : ArchDatumR P₂) (W : ℝ → ℂ) (u₀ cP : ℂ) (a₀ : ZMod 2)
    (m n : ℕ) (ε' : ℝ) (s : ℂ) (x y₁ y₂ : ℝ) :
    Gfun D W (u₀ + 2) cP a₀ m n ε' s (x, y₁, y₂) =
      Cst (P₂ := P₂) u₀ cP a₀ n ε' s y₁ y₂ *
        ((∫ t : ℝ, W t * ArchR.psi ((-1 : ℝ) * t * x) * D.W (ArchR.diagOne ((-1 : ℝ) * t * y₁ / y₂)) *
            (((|t| : ℝ) : ℂ) ^ (s - 1 / 2)) * (((t ^ 2)⁻¹ : ℝ) : ℂ)) *
          ((((1 / y₁ - 1 / y₂ : ℝ) : ℂ)) + Complex.I * (((x / y₁ : ℝ) : ℂ))) ^ m *
          (Real.exp (-(Real.pi * ((1 + x ^ 2) / y₁ ^ 2 + 1 / y₂ ^ 2))) : ℂ)) := by
  simp only [Gfun, Cst]
  ring

private theorem _root_.K8S5.integral_Gfun_eq {P₂ : RealArchParam} (D : ArchDatumR P₂) (W : ℝ → ℂ) (u₀ cP uP : ℂ) (a₀ : ZMod 2)
    (nP m n : ℕ) (hm : m = nP + 1) (ε' : ℝ) (s : ℂ)
    (hWpos : ∀ t : ℝ, 0 < t → W t = (2 : ℂ) * (t : ℂ) ^ (uP + (nP : ℂ) / 2 + 1) * (Real.exp (-(2 * Real.pi * t)) : ℂ))
    (hWneg : ∀ t : ℝ, t < 0 → W t = 0)
    (y₁ y₂ : ℝ) (hy₁ : y₁ ≠ 0) (hy₂ : 0 < y₂)
    (hXT : Integrable (fun q : ℝ × ℝ =>
        ((Real.exp (-(Real.pi * (q.1 ^ 2 / y₁ ^ 2))) : ℂ) *
            ((((1 / y₁ - 1 / y₂ : ℝ) : ℂ)) + (((y₁⁻¹ : ℝ) : ℂ)) * Complex.I * (q.1 : ℂ)) ^ m *
            ArchR.psi ((-1 : ℝ) * q.2 * q.1)) *
          (W q.2 * D.W (ArchR.diagOne ((-1 : ℝ) * q.2 * y₁ / y₂)) * (((|q.2| : ℝ) : ℂ) ^ (s - 1 / 2)) *
            (((q.2 ^ 2)⁻¹ : ℝ) : ℂ)))
        ((volume : Measure ℝ).prod (volume : Measure ℝ))) :
    ∫ x : ℝ, Gfun D W (u₀ + 2) cP a₀ m n ε' s (x, y₁, y₂) =
      Complex.Gammaℝ (cP + P₂.centralExponent + 2 * s + n + 1) * (-(ε' : ℂ)) ^ n * SGN a₀ y₁ *
        ∫ t in Ioi (0 : ℝ), Pfun D m (s + uP + (m : ℂ) / 2 - 2) (-(u₀ + 2)) (-(cP + 2 * s + u₀ + 1)) t y₁ y₂ := by

  simp_rw [Gfun_eq_Cst_mul D W u₀ cP a₀ m n ε' s]
  rw [integral_const_mul]

  have hI : Integrable (fun q : ℝ × ℝ =>
        ((Real.exp (-(Real.pi * (q.1 ^ 2 / y₁ ^ 2))) : ℂ) *
            ((((1 / y₁ - 1 / y₂ : ℝ) : ℂ)) + Complex.I * (((q.1 / y₁ : ℝ) : ℂ))) ^ m *
            ArchR.psi ((-1 : ℝ) * q.2 * q.1)) *
          (W q.2 * (fun v : ℝ => D.W (ArchR.diagOne v)) ((-1 : ℝ) * q.2 * y₁ / y₂) *
            (((|q.2| : ℝ) : ℂ) ^ (s - 1 / 2)) * (((q.2 ^ 2)⁻¹ : ℝ) : ℂ)))
        ((volume : Measure ℝ).prod (volume : Measure ℝ)) := by
    refine hXT.congr (Filter.Eventually.of_forall (fun q => ?_))
    have : (((y₁⁻¹ : ℝ) : ℂ)) * Complex.I * (q.1 : ℂ) = Complex.I * (((q.1 / y₁ : ℝ) : ℂ)) := by
      push_cast; ring
    simp only [this]
  have hXS := K7XS.integral_torusT_mul_block_mul_gaussian_eq (fun v : ℝ => D.W (ArchR.diagOne v)) W m s y₁ y₂ hy₁ hI
  beta_reduce at hXS
  rw [hXS]

  rw [← integral_const_mul, ← integral_const_mul]
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Ioi (0 : ℝ)) (fun t ht => ?_)]
  swap
  · simp only [Set.mem_Ioi, not_lt] at ht
    rcases ht.lt_or_eq with h | h
    · simp [hWneg t h]
    · subst h; simp
  rw [← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
  have hc := K7Collect.collect D W u₀ cP uP a₀ nP m n hm ε' s hWpos t y₁ y₂ ht hy₁ hy₂
  rw [← hc]
  simp only [Cst]
  ring

p2m_export "K8S5" "integral_Gfun_eq"
end K8S5
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_forall_iwasawaIntegral_eq_const_mul_oneSided_torusPair_add_mirror_of_discreteProfile_conjBlockHarmonic_colHarmonic.K7Rot"

namespace K7S5
open K7F in
private theorem _root_.K7S5.integral_Gfun_eq {P₂ : RealArchParam} (D : ArchDatumR P₂) (W : ℝ → ℂ) (u₀ cP uP : ℂ) (a₀ : ZMod 2)
    (nP m n : ℕ) (hm : m = nP + 1) (ε' : ℝ) (s : ℂ)
    (hWpos : ∀ t : ℝ, 0 < t → W t = (2 : ℂ) * (t : ℂ) ^ (uP + (nP : ℂ) / 2 + 1) * (Real.exp (-(2 * Real.pi * t)) : ℂ))
    (hWneg : ∀ t : ℝ, t < 0 → W t = 0)
    (y₁ y₂ : ℝ) (hy₁ : y₁ ≠ 0) (hy₂ : 0 < y₂)
    (hXT : Integrable (fun q : ℝ × ℝ =>
        ((Real.exp (-(Real.pi * (q.1 ^ 2 / y₁ ^ 2))) : ℂ) *
            ((((1 / y₁ - 1 / y₂ : ℝ) : ℂ)) + (((y₁⁻¹ : ℝ) : ℂ)) * Complex.I * (q.1 : ℂ)) ^ m *
            ArchR.psi ((-1 : ℝ) * q.2 * q.1)) *
          (W q.2 * D.W (ArchR.diagOne ((-1 : ℝ) * q.2 * y₁ / y₂)) * (((|q.2| : ℝ) : ℂ) ^ (s - 1 / 2)) *
            (((q.2 ^ 2)⁻¹ : ℝ) : ℂ)))
        ((volume : Measure ℝ).prod (volume : Measure ℝ))) :
    ∫ x : ℝ, Gfun D W (u₀ + 2) cP a₀ m n ε' s (x, y₁, y₂) =
      Complex.Gammaℝ (cP + P₂.centralExponent + 2 * s + n + 1) * (-(ε' : ℂ)) ^ n * SGN a₀ y₁ *
        ∫ t in Ioi (0 : ℝ), Pfun D m (s + uP + (m : ℂ) / 2 - 2) (-(u₀ + 2)) (-(cP + 2 * s + u₀ + 1)) t y₁ y₂ :=
  K8S5.integral_Gfun_eq D W u₀ cP uP a₀ nP m n hm ε' s hWpos hWneg y₁ y₂ hy₁ hy₂ hXT

end K7S5
p2m_export "" "K7S5.integral_Gfun_eq"
open K7F in
theorem solution
    {P₂ : RealArchParam} (D : ArchDatumR P₂) (k₀ : ℤ)
    (hDW : ∀ (r : rowIsometrySubgroup₀ ℝ) (x : GL (Fin 2) ℝ),
        D.W ((x * (r : GL (Fin 2) ℝ) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
          (archWeightCharℝ k₀ r : ℂ) * D.W (x : Matrix (Fin 2) (Fin 2) ℝ))
    (a : ℚ) (ha1 : a = -1)
    (u₀ cP uP : ℂ) (a₀ : ZMod 2) (nP m : ℕ) (hm : m = nP + 1) (n : ℕ) (ε' : ℝ)
    (hcol : (ε' = -1 ∧ (n : ℤ) = k₀ - m) ∨ (ε' = 1 ∧ (n : ℤ) = m - k₀))
    (W : ℝ → ℂ)
    (hWpos : ∀ t : ℝ, 0 < t → W t = (2 : ℂ) * (t : ℂ) ^ (uP + (nP : ℂ) / 2 + 1) * (Real.exp (-(2 * Real.pi * t)) : ℂ))
    (hWneg : ∀ t : ℝ, t < 0 → W t = 0)
    :
    ∃ σ₁ : ℝ, ∀ s : ℂ, σ₁ < s.re →
    (∫ p : ℝ × ℝ × ℝ × ℝ in Set.univ ×ˢ (Set.univ ×ˢ (Set.Ioi (0 : ℝ) ×ˢ Set.Ioc (0 : ℝ) (2 * Real.pi))),
        (let x : ℝ := p.1
         let y₁ : ℝ := p.2.1
         let y₂ : ℝ := p.2.2.1
         let θ : ℝ := p.2.2.2
         let g : Matrix (Fin 2) (Fin 2) ℝ :=
           !![y₁ * Real.cos θ + x * y₂ * Real.sin θ, -(y₁ * Real.sin θ) + x * y₂ * Real.cos θ;
              y₂ * Real.sin θ, y₂ * Real.cos θ]
         ArchR.quasiChar (u₀ + 2) a₀ (y₁ * y₂)⁻¹ *
             (((|(y₁ * y₂)⁻¹| ^ 2)⁻¹ : ℝ) : ℂ) *
           ((∫ t : ℝ, W t * D.W (ArchR.diagOne ((a : ℝ) * t) * g) *
               (((|t| : ℝ) : ℂ) ^ (s - 1 / 2)) * (((t ^ 2)⁻¹ : ℝ) : ℂ)) *
            (((((Real.cos θ : ℝ) : ℂ) + Complex.I * ((Real.sin θ : ℝ) : ℂ)) *
                  ((((1 / y₁ - 1 / y₂ : ℝ) : ℂ)) + Complex.I * (((x / y₁ : ℝ) : ℂ)))) ^ m *
              (Real.exp (-(Real.pi * ((1 + x ^ 2) / y₁ ^ 2 + 1 / y₂ ^ 2))) : ℂ) *
              ((|y₁ * y₂| : ℝ) : ℂ) *
              (-Complex.I * (a : ℂ)) ^ n *
              (((y₂ * Real.sin θ : ℝ) : ℂ) + (ε' : ℂ) * Complex.I * ((y₂ * Real.cos θ : ℝ) : ℂ)) ^ n *
              ((1 / 2 : ℂ) *
                ((Real.pi * (a : ℝ) ^ 2 * ((y₂ * Real.sin θ) ^ 2 + (y₂ * Real.cos θ) ^ 2) : ℝ) : ℂ)
                    ^ (-((cP + P₂.centralExponent + 2 * s + n + 1) / 2)) *
                Complex.Gamma ((cP + P₂.centralExponent + 2 * s + n + 1) / 2)))) *
           ((y₂ ^ 2 * (|y₁ * y₂| ^ 4)⁻¹ : ℝ) : ℂ)))
      = (Real.pi : ℂ) * Complex.Gammaℝ (cP + P₂.centralExponent + 2 * s + (n : ℂ) + 1) *
          ((-(ε' : ℂ)) ^ n) * (2 : ℂ) *
        ((-1 : ℂ) ^ (a₀.val) *
          (∫ t in Ioi (0 : ℝ), ∫ y₁ in Iio (0 : ℝ), ∫ y₂ in Ioi (0 : ℝ),
            ((t : ℝ) : ℂ) ^ (s + uP + (m : ℂ) / 2 - 2) * (Real.exp (-(2 * Real.pi * t)) : ℂ) *
              ((|y₁| : ℝ) : ℂ) ^ (-(u₀ + 2)) * ((y₂ : ℝ) : ℂ) ^ (-(cP + 2 * s + u₀ + 1)) *
              (Real.exp (-(Real.pi * ((y₁ ^ 2)⁻¹ + t ^ 2 * y₁ ^ 2 + (y₂ ^ 2)⁻¹))) : ℂ) *
              D.W (ArchR.diagOne (t * |y₁| / y₂)) *
              (∫ z : ℝ, (((y₁⁻¹ - y₂⁻¹ + t * y₁ : ℝ) : ℂ) + Complex.I * (z : ℂ)) ^ m *
                (Real.exp (-(Real.pi * z ^ 2)) : ℂ))) +
         (∫ t in Ioi (0 : ℝ), ∫ y₁ in Iio (0 : ℝ), ∫ y₂ in Ioi (0 : ℝ),
            ((t : ℝ) : ℂ) ^ (s + uP + (m : ℂ) / 2 - 2) * (Real.exp (-(2 * Real.pi * t)) : ℂ) *
              ((|y₁| : ℝ) : ℂ) ^ (-(u₀ + 2)) * ((y₂ : ℝ) : ℂ) ^ (-(cP + 2 * s + u₀ + 1)) *
              (Real.exp (-(Real.pi * ((y₁ ^ 2)⁻¹ + t ^ 2 * y₁ ^ 2 + (y₂ ^ 2)⁻¹))) : ℂ) *
              D.W (ArchR.diagOne (-(t * |y₁| / y₂))) *
              (∫ z : ℝ, (((-y₁⁻¹ - y₂⁻¹ - t * y₁ : ℝ) : ℂ) + Complex.I * (z : ℂ)) ^ m *
                (Real.exp (-(Real.pi * z ^ 2)) : ℂ)))) := by
  subst ha1
  obtain ⟨σ₁, hρ1⟩ :=
    LanglandsTunnell.Converse.exists_forall_integrable_thetaFree_iwasawaIntegrand_conjBlockPow_colHarmonic_of_oneSided_profile
      W (uP + (nP : ℂ) / 2 + 1) hWpos hWneg D (-1) (by norm_num) (u₀ + 2) cP a₀ m n ε'
  obtain ⟨σ₂, hS6⟩ := K7S6.assemble D W u₀ cP uP a₀ nP m n hm ε' hWpos hWneg
  obtain ⟨σ₃, hρ2⟩ :=
    LanglandsTunnell.Converse.exists_forall_integrable_xPowGaussian_psi_mul_torusPair_of_oneSided_profile
      W (uP + (nP : ℂ) / 2 + 1) hWpos hWneg D (-1) (by norm_num) m
  refine ⟨max σ₁ (max σ₂ σ₃), fun s hs => ?_⟩
  have hs1 : σ₁ < s.re := lt_of_le_of_lt (le_max_left _ _) hs
  have hs2 : σ₂ < s.re := lt_of_le_of_lt ((le_max_left _ _).trans (le_max_right _ _)) hs
  have hs3 : σ₃ < s.re := lt_of_le_of_lt ((le_max_right _ _).trans (le_max_right _ _)) hs

  have hrow : ∀ y₁ : ℝ, y₁ ≠ 0 → ∀ y₂ : ℝ, 0 < y₂ →
      ∫ x : ℝ, Gfun D W (u₀ + 2) cP a₀ m n ε' s (x, y₁, y₂) =
        Complex.Gammaℝ (cP + P₂.centralExponent + 2 * s + n + 1) * (-(ε' : ℂ)) ^ n * SGN a₀ y₁ *
          ∫ t in Ioi (0 : ℝ), Pfun D m (s + uP + (m : ℂ) / 2 - 2) (-(u₀ + 2)) (-(cP + 2 * s + u₀ + 1)) t y₁ y₂ :=
    fun y₁ hy₁ y₂ hy₂ => K7S5.integral_Gfun_eq D W u₀ cP uP a₀ nP m n hm ε' s hWpos hWneg y₁ y₂ hy₁ hy₂
      (hρ2 s hs3 y₁ hy₁ y₂ hy₂ _ _)

  have hG : Integrable (fun q : ℝ × ℝ × ℝ => Gfun D W (u₀ + 2) cP a₀ m n ε' s (q.1, q.2.1, q.2.2))
      ((volume : Measure ℝ).prod ((volume : Measure ℝ).prod ((volume : Measure ℝ).restrict (Ioi 0)))) := by
    have h := hρ1 s hs1
    simpa only [K7F.Gfun] using h
  have hA := MeasureTheory.setIntegral_iwasawaRegion_eq_two_pi_mul_of_theta_free
    (fun p : ℝ × ℝ × ℝ × ℝ =>
        (let x : ℝ := p.1
         let y₁ : ℝ := p.2.1
         let y₂ : ℝ := p.2.2.1
         let θ : ℝ := p.2.2.2
         let g : Matrix (Fin 2) (Fin 2) ℝ :=
           !![y₁ * Real.cos θ + x * y₂ * Real.sin θ, -(y₁ * Real.sin θ) + x * y₂ * Real.cos θ;
              y₂ * Real.sin θ, y₂ * Real.cos θ]
         ArchR.quasiChar (u₀ + 2) a₀ (y₁ * y₂)⁻¹ *
             (((|(y₁ * y₂)⁻¹| ^ 2)⁻¹ : ℝ) : ℂ) *
           ((∫ t : ℝ, W t * D.W (ArchR.diagOne (((-1 : ℚ) : ℝ) * t) * g) *
               (((|t| : ℝ) : ℂ) ^ (s - 1 / 2)) * (((t ^ 2)⁻¹ : ℝ) : ℂ)) *
            (((((Real.cos θ : ℝ) : ℂ) + Complex.I * ((Real.sin θ : ℝ) : ℂ)) *
                  ((((1 / y₁ - 1 / y₂ : ℝ) : ℂ)) + Complex.I * (((x / y₁ : ℝ) : ℂ)))) ^ m *
              (Real.exp (-(Real.pi * ((1 + x ^ 2) / y₁ ^ 2 + 1 / y₂ ^ 2))) : ℂ) *
              ((|y₁ * y₂| : ℝ) : ℂ) *
              (-Complex.I * ((-1 : ℚ) : ℂ)) ^ n *
              (((y₂ * Real.sin θ : ℝ) : ℂ) + (ε' : ℂ) * Complex.I * ((y₂ * Real.cos θ : ℝ) : ℂ)) ^ n *
              ((1 / 2 : ℂ) *
                ((Real.pi * ((-1 : ℚ) : ℝ) ^ 2 * ((y₂ * Real.sin θ) ^ 2 + (y₂ * Real.cos θ) ^ 2) : ℝ) : ℂ)
                    ^ (-((cP + P₂.centralExponent + 2 * s + n + 1) / 2)) *
                Complex.Gamma ((cP + P₂.centralExponent + 2 * s + n + 1) / 2)))) *
           ((y₂ ^ 2 * (|y₁ * y₂| ^ 4)⁻¹ : ℝ) : ℂ)))
    (fun x y₁ y₂ => Gfun D W (u₀ + 2) cP a₀ m n ε' s (x, y₁, y₂))
    (by
      intro x y₁ y₂ θ hy₁ hy₂
      simp only [Rat.cast_neg, Rat.cast_one, K7F.Gfun]
      exact K7Theta.pointwise D k₀ hDW W (u₀ + 2) cP a₀ m n ε' hcol s x y₁ y₂ θ hy₁ hy₂)
    hG
  rw [hA]
  exact hS6 s hs2 hrow

#print axioms solution

end S_LanglandsTunnell_RankinSelberg_exists_forall_iwasawaIntegral_eq_const_mul_oneSided_torusPair_add_mirror_of_discreteProfile_conjBlockHarmonic_colHarmonic
end P2MW
export P2MW.S_LanglandsTunnell_RankinSelberg_exists_forall_iwasawaIntegral_eq_const_mul_oneSided_torusPair_add_mirror_of_discreteProfile_conjBlockHarmonic_colHarmonic (solution)
