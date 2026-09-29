-- Prove2me | solution 1 for ModularCurve.periodAlongOf_eq_neg_conj_periodAlongOf_J_smul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/1d7b2e05-46eb-52ec-aefc-e34eef7aa485

import Mathlib
import Definitions.Def_ModularCurve_PeriodOf
import Definitions.Def_ModularCurve_PeriodHomPair
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_periodAlongOf_eq_neg_conj_periodAlongOf_J_smul

set_option autoImplicit false

open UpperHalfPlane Matrix Matrix.SpecialLinearGroup
open scoped MatrixGroups ModularForm ComplexConjugate

noncomputable section

namespace ModularCurve
p2m_export "ModularCurve" "periodAlongOf periodAlongOf_apply periodOf segmentPoint segmentPath coe_segmentPath period Period.jConjMat Period.jConjSL"
namespace PeriodConj
p2m_open "ModularCurve"

theorem J_smul_segmentPath (τ₀ τ₁ : ℍ) (t : ℝ) :
    UpperHalfPlane.J • ModularCurve.segmentPath τ₀ τ₁ t =
      ModularCurve.segmentPath (UpperHalfPlane.J • τ₀) (UpperHalfPlane.J • τ₁) t := by
  apply UpperHalfPlane.ext
  rw [UpperHalfPlane.coe_J_smul, ModularCurve.coe_segmentPath, ModularCurve.coe_segmentPath,
    ModularCurve.segmentPoint, ModularCurve.segmentPoint, UpperHalfPlane.coe_J_smul,
    UpperHalfPlane.coe_J_smul]
  simp only [Complex.ext_iff, Complex.add_re, Complex.add_im, Complex.neg_re, Complex.neg_im,
    Complex.real_smul, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.conj_re, Complex.conj_im, zero_mul, sub_zero, add_zero]
  constructor <;> ring

theorem periodAlongOf_eq (Γ : Subgroup SL(2, ℤ)) (f g : CuspForm Γ 2)
    (hg : ∀ τ : ℍ, g τ = conj (f (UpperHalfPlane.J • τ))) (τ₀ τ₁ : ℍ) :
    ModularCurve.periodAlongOf Γ τ₀ τ₁ g =
      -conj (ModularCurve.periodAlongOf Γ (UpperHalfPlane.J • τ₀) (UpperHalfPlane.J • τ₁) f) := by
  rw [ModularCurve.periodAlongOf_apply, ModularCurve.periodAlongOf_apply]
  have hint : ∀ t : ℝ, g (ModularCurve.segmentPath τ₀ τ₁ t) * ((τ₁ : ℂ) - τ₀) =
      -conj (f (ModularCurve.segmentPath (UpperHalfPlane.J • τ₀) (UpperHalfPlane.J • τ₁) t) *
        (((UpperHalfPlane.J • τ₁ : ℍ) : ℂ) - ((UpperHalfPlane.J • τ₀ : ℍ) : ℂ))) := by
    intro t
    rw [hg, J_smul_segmentPath, map_mul, UpperHalfPlane.coe_J_smul, UpperHalfPlane.coe_J_smul,
      map_sub, map_neg, map_neg, Complex.conj_conj, Complex.conj_conj]
    ring
  simp_rw [hint]
  rw [intervalIntegral.integral_neg]
  simp only [intervalIntegral, integral_conj, map_sub]

theorem J_smul_I : UpperHalfPlane.J • UpperHalfPlane.I = UpperHalfPlane.I := by
  apply UpperHalfPlane.ext
  rw [UpperHalfPlane.coe_J_smul, UpperHalfPlane.coe_I, Complex.conj_I, neg_neg]

theorem J_inv_mul_mapGL_mul_J (γ : SL(2, ℤ)) :
    UpperHalfPlane.J⁻¹ * (mapGL ℝ γ : GL (Fin 2) ℝ) * UpperHalfPlane.J =
      (mapGL ℝ (ModularCurve.Period.jConjSL γ) : GL (Fin 2) ℝ) := by
  have hJ : UpperHalfPlane.J⁻¹ = UpperHalfPlane.J := by
    rw [inv_eq_iff_mul_eq_one, ← sq, UpperHalfPlane.J_sq]
  rw [hJ]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [UpperHalfPlane.J, Matrix.mul_apply, Fin.sum_univ_two, ModularCurve.Period.jConjMat,
      Matrix.GeneralLinearGroup.mkOfDetNeZero, Matrix.vecMul, dotProduct]

theorem J_smul_sl_smul (γ : SL(2, ℤ)) (τ : ℍ) :
    UpperHalfPlane.J • (γ • τ) = ModularCurve.Period.jConjSL γ • (UpperHalfPlane.J • τ) := by
  have hJ : UpperHalfPlane.J⁻¹ = UpperHalfPlane.J := by
    rw [inv_eq_iff_mul_eq_one, ← sq, UpperHalfPlane.J_sq]
  have h := J_inv_mul_mapGL_mul_J γ
  rw [hJ] at h
  have h2 : UpperHalfPlane.J * (mapGL ℝ γ : GL (Fin 2) ℝ) =
      (mapGL ℝ (ModularCurve.Period.jConjSL γ) : GL (Fin 2) ℝ) * UpperHalfPlane.J := by
    rw [← h, mul_assoc, mul_assoc, ← sq, UpperHalfPlane.J_sq, mul_one]
  rw [MulAction.compHom_smul_def, MulAction.compHom_smul_def, ← mul_smul, ← mul_smul]
  exact congrArg (· • τ) h2

theorem periodOf_eq (Γ : Subgroup SL(2, ℤ)) (f g : CuspForm Γ 2)
    (hg : ∀ τ : ℍ, g τ = conj (f (UpperHalfPlane.J • τ))) (γ : Γ)
    (hγ : ModularCurve.Period.jConjSL (γ : SL(2, ℤ)) ∈ Γ) :
    ModularCurve.periodOf Γ γ g =
      -conj (ModularCurve.periodOf Γ ⟨ModularCurve.Period.jConjSL (γ : SL(2, ℤ)), hγ⟩ f) := by
  rw [ModularCurve.periodOf, ModularCurve.periodOf, periodAlongOf_eq Γ f g hg, J_smul_I, J_smul_sl_smul,
    J_smul_I]

theorem periodAlongOf_I_eq (Γ : Subgroup SL(2, ℤ)) (f g : CuspForm Γ 2)
    (hg : ∀ τ : ℍ, g τ = conj (f (UpperHalfPlane.J • τ))) (τ : ℍ) :
    ModularCurve.periodAlongOf Γ UpperHalfPlane.I τ g =
      -conj (ModularCurve.periodAlongOf Γ UpperHalfPlane.I (UpperHalfPlane.J • τ) f) := by
  rw [periodAlongOf_eq Γ f g hg, J_smul_I]

end ModularCurve.PeriodConj

end

theorem solution
    (Γ : Subgroup SL(2, ℤ)) (f g : CuspForm Γ 2)
    (hg : ∀ τ : UpperHalfPlane, g τ = (starRingEnd ℂ) (f (UpperHalfPlane.J • τ)))
    (τ₀ τ₁ : UpperHalfPlane) :
    ModularCurve.periodAlongOf Γ τ₀ τ₁ g =
      -(starRingEnd ℂ) (ModularCurve.periodAlongOf Γ (UpperHalfPlane.J • τ₀) (UpperHalfPlane.J • τ₁) f) :=
  ModularCurve.PeriodConj.periodAlongOf_eq Γ f g hg τ₀ τ₁

end S_ModularCurve_periodAlongOf_eq_neg_conj_periodAlongOf_J_smul
end P2MW
export P2MW.S_ModularCurve_periodAlongOf_eq_neg_conj_periodAlongOf_J_smul (solution)
