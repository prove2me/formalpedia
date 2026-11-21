-- Prove2me | solution 1 for NewtonianLipschitz.NewtonianPointSource.unitAxis_fderiv_opNorm_eq_candidateMaximum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T04:10:56.51004+00:00
-- url     : https://prove2.me/submissions/d82e104b-309d-4214-9c4d-8048c40308fa

module
public import Definitions.Def_NewtonianLipschitz_JacobianSharpWitness
public import Definitions.Def_NewtonianLipschitz_JacobianOperatorWitness
public import Theorems.Thm_NewtonianLipschitz_NewtonianPointSource_unitAxis_fderiv_opNorm_ge_candidateMaximum
public import Theorems.Thm_NewtonianLipschitz_NewtonianPointSource_accelerationField_fderiv_opNorm_le_candidateMaximum
public import Theorems.Thm_NewtonianLipschitz_NewtonianPointSource_unitAxis_gravitationalParameter_eq_one
public import Theorems.Thm_NewtonianLipschitz_criticalDiagonal_cartesian_norm_eq_one


set_option autoImplicit true
@[expose] public section
public section
open Matrix
open NewtonianLipschitz
namespace NewtonianLipschitz
namespace NewtonianPointSource
theorem _root_.solution :
    ‖fderiv ℝ NewtonianPointSource.unitAxis.accelerationField
      (normalizedVector candidateCriticalPoint candidateCriticalPoint)‖ =
        candidateMaximum := by
  let x := normalizedVector candidateCriticalPoint candidateCriticalPoint
  let c := NewtonianPointSource.unitAxis
  have hnorm : ‖x‖ = (1 : ℝ) :=
    criticalDiagonal_cartesian_norm_eq_one
  have hx : x ≠ 0 := by
    intro hzero
    rw [hzero, norm_zero] at hnorm
    norm_num at hnorm
  apply le_antisymm
  · have hup :=
      c.accelerationField_fderiv_opNorm_le_candidateMaximum x hx
    have hmu : c.gravitationalParameter = 1 := by
      change NewtonianPointSource.unitAxis.gravitationalParameter = 1
      exact NewtonianPointSource.unitAxis_gravitationalParameter_eq_one
    rw [hnorm, one_pow, div_one, one_mul, hmu, one_mul] at hup
    exact hup
  · exact NewtonianPointSource.unitAxis_fderiv_opNorm_ge_candidateMaximum
end NewtonianPointSource
end NewtonianLipschitz
