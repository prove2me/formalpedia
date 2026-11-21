-- Prove2me | solution 1 for NewtonianLipschitz.candidateMaximum_le_of_universal_fderiv_opNorm_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T04:12:45.917747+00:00
-- url     : https://prove2.me/submissions/55b4fce5-2903-4f22-91c9-2c446dc8e512

module
public import Definitions.Def_NewtonianLipschitz_CartesianBoxSharp
public import Definitions.Def_NewtonianLipschitz_DerivativeCoefficientMinimality
public import Theorems.Thm_NewtonianLipschitz_NewtonianPointSource_unitAxis_fderiv_opNorm_eq_candidateMaximum
public import Theorems.Thm_NewtonianLipschitz_NewtonianPointSource_unitAxis_gravitationalParameter_eq_one
public import Theorems.Thm_NewtonianLipschitz_criticalDiagonal_cartesian_norm_eq_one


set_option autoImplicit true
@[expose] public section
public section
open NewtonianLipschitz
namespace NewtonianLipschitz
theorem _root_.solution
    (K : ℝ)
    (hK : ∀ (c : NewtonianPointSource) (x : Vec3),
      x ≠ 0 →
        ‖fderiv ℝ c.accelerationField x‖ ≤
          (1 / ‖x‖ ^ 3) * (c.gravitationalParameter * K)) :
    candidateMaximum ≤ K := by
  let x : Vec3 :=
    normalizedVector candidateCriticalPoint candidateCriticalPoint
  have hnorm : ‖x‖ = (1 : ℝ) :=
    criticalDiagonal_cartesian_norm_eq_one
  have hx : x ≠ 0 := by
    intro hzero
    rw [hzero, norm_zero] at hnorm
    norm_num at hnorm
  have hbound := hK NewtonianPointSource.unitAxis x hx
  have hmu :
      NewtonianPointSource.unitAxis.gravitationalParameter =
        (1 : ℝ) :=
    NewtonianPointSource.unitAxis_gravitationalParameter_eq_one
  rw [hnorm, one_pow, div_one, one_mul, hmu, one_mul] at hbound
  have heq :
      ‖fderiv ℝ NewtonianPointSource.unitAxis.accelerationField x‖ =
        candidateMaximum :=
    NewtonianPointSource.unitAxis_fderiv_opNorm_eq_candidateMaximum
  rw [heq] at hbound
  exact hbound
end NewtonianLipschitz
