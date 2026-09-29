-- Prove2me | solution 1 for ModularCurve.hasSum_qParam_heckeMatrix_smul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/12ffb1d3-8081-5d76-b098-f42f76f0fd3a

import Mathlib.Analysis.Complex.UpperHalfPlane.Exp
import Mathlib.RingTheory.LaurentSeries
import Definitions.Def_ModularForm_HeckeOperator
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_hasSum_qParam_heckeMatrix_smul

set_option autoImplicit false

noncomputable section

open UpperHalfPlane Complex Filter Topology Function
open scoped MatrixGroups

local notation "𝕢" => Function.Periodic.qParam

namespace ModularCurve

namespace Realized

theorem hasSum_qParam_heckeMatrix_smul' (ℓ : ℕ) [NeZero ℓ] (b : ℕ) (A : LaurentSeries ℂ) (F : ℍ → ℂ)
    (hA : ∀ τ : ℍ, HasSum (fun m : ℤ => A.coeff m * 𝕢 1 (τ : ℂ) ^ m) (F τ)) (τ : ℍ) :
    HasSum (fun m : ℤ => (Complex.exp (2 * Real.pi * Complex.I * b * m / ℓ) * A.coeff m) * 𝕢 ℓ (τ : ℂ) ^ m)
      (F (ModularForm.heckeMatrix ℓ b • τ)) := by
  have hℓ : ℓ ≠ 0 := NeZero.ne ℓ
  have hℓ' : (ℓ : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hℓ
  have e : 𝕢 1 ((ModularForm.heckeMatrix ℓ b • τ : ℍ) : ℂ)
      = Complex.exp (2 * Real.pi * Complex.I * b / ℓ) * 𝕢 ℓ (τ : ℂ) := by
    rw [ModularForm.coe_heckeMatrix_smul hℓ, Periodic.qParam, Periodic.qParam, ← Complex.exp_add]
    congr 1
    push_cast
    field_simp
    ring
  have e2 : ∀ m : ℤ, Complex.exp (2 * Real.pi * Complex.I * b / ℓ) ^ m
      = Complex.exp (2 * Real.pi * Complex.I * b * m / ℓ) := by
    intro m
    rw [← Complex.exp_int_mul]
    congr 1
    ring
  have hfg : (fun m : ℤ => (Complex.exp (2 * Real.pi * Complex.I * b * m / ℓ) * A.coeff m) * 𝕢 ℓ (τ : ℂ) ^ m)
      = fun m : ℤ => A.coeff m * 𝕢 1 ((ModularForm.heckeMatrix ℓ b • τ : ℍ) : ℂ) ^ m := by
    funext m
    rw [e, mul_zpow, e2]
    ring
  rw [hfg]
  exact hA _

end Realized

end ModularCurve

end

theorem solution (ℓ : ℕ) [NeZero ℓ] (b : ℕ) (A : LaurentSeries ℂ) (F : UpperHalfPlane → ℂ) (hA : ∀ τ : UpperHalfPlane, HasSum (fun m : ℤ => A.coeff m * Function.Periodic.qParam 1 (τ : ℂ) ^ m) (F τ)) (τ : UpperHalfPlane) : HasSum (fun m : ℤ => (Complex.exp (2 * Real.pi * Complex.I * b * m / ℓ) * A.coeff m) * Function.Periodic.qParam ℓ (τ : ℂ) ^ m) (F (ModularForm.heckeMatrix ℓ b • τ)) :=
  ModularCurve.Realized.hasSum_qParam_heckeMatrix_smul' ℓ b A F hA τ

end S_ModularCurve_hasSum_qParam_heckeMatrix_smul
end P2MW
export P2MW.S_ModularCurve_hasSum_qParam_heckeMatrix_smul (solution)
