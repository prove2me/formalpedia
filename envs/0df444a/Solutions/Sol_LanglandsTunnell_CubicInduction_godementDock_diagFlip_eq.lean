-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.godementDock_diagFlip_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/8fcd4387-46ca-55bb-a897-5fc4fb51898d

import Definitions.Def_LanglandsTunnell_CubicInduction_GodementSection
import Definitions.Def_LanglandsTunnell_CubicInduction_LocalZeta31
import Definitions.Def_LanglandsTunnell_CubicInduction_PrincipalSeries2
import Definitions.Def_LanglandsTunnell_RSCarrier
import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_AdelicDock_LocalEmbedding
import Theorems.Thm_Matrix_GeneralLinearGroup_isMulRightInvariant_and_isInvInvariant_of_isHaarMeasure_fin_two
import Theorems.Thm_LanglandsTunnell_TateLocal_modulus_adicCompletion_eq_nnnorm
import Theorems.Thm_AutomorphicForm_secondCountableTopology_and_locallyCompactSpace_gl_two_and_isClosed_range_unipotentGL2Hom
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_CubicInduction_godementDock_diagFlip_eq

set_option autoImplicit false

p2m_open "IsDedekindDomain NumberField MeasureTheory AutomorphicForm LanglandsTunnell.TateLocal LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_godementDock_diagFlip_eq.LanglandsTunnell.CubicInduction NumberField.StandardAddChar"

open NumberField.AdelicLevel (diagOne)

noncomputable section

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "TateLocal.localBorel TateLocal.borelSpace_localBorel TateLocal.modulus_adicCompletion_eq_nnnorm"
namespace CubicInduction
namespace DockFlipF3
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

open scoped Matrix

attribute [local instance] LanglandsTunnell.TateLocal.localBorel LanglandsTunnell.TateLocal.borelSpace_localBorel
  AutomorphicForm.localGLBorel AutomorphicForm.borelSpace_localGLBorel

variable (p : HeightOneSpectrum (𝓞 ℚ))

local notation "F" => p.adicCompletion ℚ
local notation "Mat" => Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)
local notation "G2" => GL (Fin 2) (p.adicCompletion ℚ)

theorem gl_eq_of_entries {g h : G2}
    (h00 : (g : Mat) 0 0 = (h : Mat) 0 0) (h01 : (g : Mat) 0 1 = (h : Mat) 0 1)
    (h10 : (g : Mat) 1 0 = (h : Mat) 1 0) (h11 : (g : Mat) 1 1 = (h : Mat) 1 1) : g = h := by
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j
  · exact h00
  · exact h01
  · exact h10
  · exact h11

theorem mul_coe_apply (g h : G2) (i j : Fin 2) :
    ((g * h : G2) : Mat) i j = (g : Mat) i 0 * (h : Mat) 0 j + (g : Mat) i 1 * (h : Mat) 1 j := by
  rw [Matrix.GeneralLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]

theorem d_mul_d (d : G2) (hd : ((d : G2) : Mat) = !![1, 0; 0, -1]) : d * d = 1 := by
  apply gl_eq_of_entries <;> simp [mul_coe_apply, hd]

theorem d_inv (d : G2) (hd : ((d : G2) : Mat) = !![1, 0; 0, -1]) : d⁻¹ = d :=
  inv_eq_of_mul_eq_one_right (d_mul_d p d hd)

theorem d_mul_row_one (d : G2) (hd : ((d : G2) : Mat) = !![1, 0; 0, -1]) (x : G2) (j : Fin 2) :
    ((d * x : G2) : Mat) 1 j = -((x : Mat) 1 j) := by
  rw [mul_coe_apply, hd]; simp

def M (g : G2) : ℂ := ((modulus ((Matrix.GeneralLinearGroup.det g : (F)ˣ) : F) : ℝ) : ℂ)

theorem M_eq_norm (g : G2) : M p g = ((‖((Matrix.GeneralLinearGroup.det g : (F)ˣ) : F)‖ : ℝ) : ℂ) := by
  rw [M, LanglandsTunnell.TateLocal.modulus_adicCompletion_eq_nnnorm]; rfl

theorem M_mul (g h : G2) : M p (g * h) = M p g * M p h := by
  simp only [M_eq_norm, map_mul, Units.val_mul, norm_mul, Complex.ofReal_mul]

theorem M_d (d : G2) (hd : ((d : G2) : Mat) = !![1, 0; 0, -1]) : M p d = 1 := by
  rw [M_eq_norm, Matrix.GeneralLinearGroup.val_det_apply, hd, Matrix.det_fin_two_of]; simp

theorem chi_d_sq (χ : (F)ˣ →* ℂˣ) (d : G2) (hd : ((d : G2) : Mat) = !![1, 0; 0, -1]) :
    ((χ (Matrix.GeneralLinearGroup.det d) : ℂˣ) : ℂ) * ((χ (Matrix.GeneralLinearGroup.det d) : ℂˣ) : ℂ) = 1 := by
  rw [← Units.val_mul, ← map_mul, ← map_mul, d_mul_d p d hd, map_one, map_one, Units.val_one]

theorem main
    (η : AddChar (p.adicCompletion ℚ) ℂ) (χ : (p.adicCompletion ℚ)ˣ →* ℂˣ)
    (φ₁ : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ) → ℂ) (φ₂ : (p.adicCompletion ℚ) × (p.adicCompletion ℚ) → ℂ) (K : GL (Fin 2) (p.adicCompletion ℚ) → ℂ)
    (d : GL (Fin 2) (p.adicCompletion ℚ)) (hd : ((d : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) = !![1, 0; 0, -1]) :
    ∀ (μ₂ : Measure (GL (Fin 2) (p.adicCompletion ℚ))) [μ₂.IsHaarMeasure] (g : GL (Fin 2) (p.adicCompletion ℚ)),
      ((χ (Matrix.GeneralLinearGroup.det (d * g)) : ℂˣ) : ℂ) * ((modulus ((Matrix.GeneralLinearGroup.det (d * g) : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ)) : ℝ) : ℂ) *
          ∫ h : GL (Fin 2) (p.adicCompletion ℚ),
            φ₁ ((h * (d * g) : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) *
              (∫ u : (p.adicCompletion ℚ) × (p.adicCompletion ℚ),
                  φ₂ u * η⁻¹ (u.1 * ((h⁻¹ : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 0 + u.2 * ((h⁻¹ : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 1) ∂((selfDualHaarAt ℚ p).prod (selfDualHaarAt ℚ p))) *
              K h⁻¹ * ((χ (Matrix.GeneralLinearGroup.det h) : ℂˣ) : ℂ) *
              ((modulus ((Matrix.GeneralLinearGroup.det h : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ)) : ℝ) : ℂ) ^ (1 / 2 : ℂ) ∂μ₂ =
        ((χ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) * ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ)) : ℝ) : ℂ) *
          ∫ h : GL (Fin 2) (p.adicCompletion ℚ),
            φ₁ ((h * g : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) *
              (∫ u : (p.adicCompletion ℚ) × (p.adicCompletion ℚ),
                  φ₂ u * η (u.1 * ((h⁻¹ : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 0 + u.2 * ((h⁻¹ : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 1) ∂((selfDualHaarAt ℚ p).prod (selfDualHaarAt ℚ p))) *
              K (d * h⁻¹) * ((χ (Matrix.GeneralLinearGroup.det h) : ℂˣ) : ℂ) *
              ((modulus ((Matrix.GeneralLinearGroup.det h : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ)) : ℝ) : ℂ) ^ (1 / 2 : ℂ) ∂μ₂ := by
  intro μ₂ _ g
  obtain ⟨hsc, hlc, -, -⟩ :=
    AutomorphicForm.secondCountableTopology_and_locallyCompactSpace_gl_two_and_isClosed_range_unipotentGL2Hom ℚ p
  haveI := hsc
  haveI := hlc
  obtain ⟨hμR, -⟩ := Matrix.GeneralLinearGroup.isMulRightInvariant_and_isInvInvariant_of_isHaarMeasure_fin_two μ₂
  haveI := hμR

  set R : G2 → ℂ := fun h => φ₁ ((h * g : G2) : Mat) *
      (∫ u : F × F, φ₂ u * η (u.1 * ((h⁻¹ : G2) : Mat) 1 0 + u.2 * ((h⁻¹ : G2) : Mat) 1 1) ∂((selfDualHaarAt ℚ p).prod (selfDualHaarAt ℚ p))) *
      K (d * h⁻¹) * ((χ (Matrix.GeneralLinearGroup.det h) : ℂˣ) : ℂ) *
      ((modulus ((Matrix.GeneralLinearGroup.det h : (F)ˣ) : F) : ℝ) : ℂ) ^ (1 / 2 : ℂ) with hR

  conv_lhs => rw [← integral_mul_right_eq_self _ d]
  have hpt : ∀ h : G2,
      φ₁ ((h * d * (d * g) : G2) : Mat) *
        (∫ u : F × F, φ₂ u * η⁻¹ (u.1 * (((h * d)⁻¹ : G2) : Mat) 1 0 + u.2 * (((h * d)⁻¹ : G2) : Mat) 1 1) ∂((selfDualHaarAt ℚ p).prod (selfDualHaarAt ℚ p))) *
        K ((h * d)⁻¹) * ((χ (Matrix.GeneralLinearGroup.det (h * d)) : ℂˣ) : ℂ) *
        ((modulus ((Matrix.GeneralLinearGroup.det (h * d) : (F)ˣ) : F) : ℝ) : ℂ) ^ (1 / 2 : ℂ) =
      ((χ (Matrix.GeneralLinearGroup.det d) : ℂˣ) : ℂ) * R h := by
    intro h
    have e1 : h * d * (d * g) = h * g := by rw [mul_assoc, ← mul_assoc d, d_mul_d p d hd, one_mul]
    have e2 : (h * d)⁻¹ = d * h⁻¹ := by rw [mul_inv_rev, d_inv p d hd]
    have e3 : (∫ u : F × F, φ₂ u * η⁻¹ (u.1 * (((h * d)⁻¹ : G2) : Mat) 1 0 + u.2 * (((h * d)⁻¹ : G2) : Mat) 1 1) ∂((selfDualHaarAt ℚ p).prod (selfDualHaarAt ℚ p))) =
        ∫ u : F × F, φ₂ u * η (u.1 * ((h⁻¹ : G2) : Mat) 1 0 + u.2 * ((h⁻¹ : G2) : Mat) 1 1) ∂((selfDualHaarAt ℚ p).prod (selfDualHaarAt ℚ p)) := by
      congr 1
      funext u
      rw [e2, d_mul_row_one p d hd, d_mul_row_one p d hd, AddChar.inv_apply]
      congr 1
      ring
    have e4 : ((modulus ((Matrix.GeneralLinearGroup.det (h * d) : (F)ˣ) : F) : ℝ) : ℂ) =
        ((modulus ((Matrix.GeneralLinearGroup.det h : (F)ˣ) : F) : ℝ) : ℂ) := by
      show M p (h * d) = M p h
      rw [M_mul, M_d p d hd, mul_one]
    rw [e1, e3, e2, e4, map_mul, map_mul, Units.val_mul (χ _) (χ _), hR]
    ring
  simp_rw [hpt]
  rw [integral_const_mul, show ((modulus ((Matrix.GeneralLinearGroup.det (d * g) : (F)ˣ) : F) : ℝ) : ℂ) =
      ((modulus ((Matrix.GeneralLinearGroup.det g : (F)ˣ) : F) : ℝ) : ℂ) from by
        show M p (d * g) = M p g; rw [M_mul, M_d p d hd, one_mul],
    map_mul, map_mul, Units.val_mul (χ _) (χ _)]
  have hχd := chi_d_sq p χ d hd
  linear_combination (((χ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) *
    ((modulus ((Matrix.GeneralLinearGroup.det g : (F)ˣ) : F) : ℝ) : ℂ) * ∫ h : G2, R h ∂μ₂) * hχd

end LanglandsTunnell.CubicInduction.DockFlipF3

end

theorem solution
    (p : HeightOneSpectrum (𝓞 ℚ)) (η : AddChar (p.adicCompletion ℚ) ℂ) (χ : (p.adicCompletion ℚ)ˣ →* ℂˣ)
    (φ₁ : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ) → ℂ) (φ₂ : (p.adicCompletion ℚ) × (p.adicCompletion ℚ) → ℂ) (K : GL (Fin 2) (p.adicCompletion ℚ) → ℂ)
    (d : GL (Fin 2) (p.adicCompletion ℚ)) (hd : ((d : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) = !![1, 0; 0, -1]) :
    letI := localGLBorel ℚ p
    haveI := borelSpace_localGLBorel ℚ p
    letI : MeasurableSpace (p.adicCompletion ℚ) := localBorel ℚ p
    ∀ (μ₂ : Measure (GL (Fin 2) (p.adicCompletion ℚ))) [μ₂.IsHaarMeasure] (g : GL (Fin 2) (p.adicCompletion ℚ)),
      ((χ (Matrix.GeneralLinearGroup.det (d * g)) : ℂˣ) : ℂ) * ((modulus ((Matrix.GeneralLinearGroup.det (d * g) : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ)) : ℝ) : ℂ) *
          ∫ h : GL (Fin 2) (p.adicCompletion ℚ),
            φ₁ ((h * (d * g) : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) *
              (∫ u : (p.adicCompletion ℚ) × (p.adicCompletion ℚ),
                  φ₂ u * η⁻¹ (u.1 * ((h⁻¹ : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 0 + u.2 * ((h⁻¹ : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 1) ∂((selfDualHaarAt ℚ p).prod (selfDualHaarAt ℚ p))) *
              K h⁻¹ * ((χ (Matrix.GeneralLinearGroup.det h) : ℂˣ) : ℂ) *
              ((modulus ((Matrix.GeneralLinearGroup.det h : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ)) : ℝ) : ℂ) ^ (1 / 2 : ℂ) ∂μ₂ =
        ((χ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) * ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ)) : ℝ) : ℂ) *
          ∫ h : GL (Fin 2) (p.adicCompletion ℚ),
            φ₁ ((h * g : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) *
              (∫ u : (p.adicCompletion ℚ) × (p.adicCompletion ℚ),
                  φ₂ u * η (u.1 * ((h⁻¹ : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 0 + u.2 * ((h⁻¹ : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 1) ∂((selfDualHaarAt ℚ p).prod (selfDualHaarAt ℚ p))) *
              K (d * h⁻¹) * ((χ (Matrix.GeneralLinearGroup.det h) : ℂˣ) : ℂ) *
              ((modulus ((Matrix.GeneralLinearGroup.det h : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ)) : ℝ) : ℂ) ^ (1 / 2 : ℂ) ∂μ₂ :=
  LanglandsTunnell.CubicInduction.DockFlipF3.main p η χ φ₁ φ₂ K d hd

end S_LanglandsTunnell_CubicInduction_godementDock_diagFlip_eq
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_godementDock_diagFlip_eq (solution)
