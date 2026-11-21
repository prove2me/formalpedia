-- Prove2me | solution 1 for NewtonianLipschitz.NewtonianPointSource.unitAxis_exists_safe_secant_quotient_limit
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T04:19:44.07118+00:00
-- url     : https://prove2.me/submissions/90f65c30-bd86-4731-b4f5-b681580800f7

module
public import Definitions.Def_NewtonianLipschitz_AdmissibleCriticalDirection
public import Definitions.Def_NewtonianLipschitz_AdmissibleSecantPairs
public import Theorems.Thm_NewtonianLipschitz_NewtonianPointSource_unitAxis_exists_safe_distinct_secant_pairs
public import Theorems.Thm_NewtonianLipschitz_NewtonianPointSource_accelerationField_contDiffAt
public import Theorems.Thm_NewtonianLipschitz_criticalDiagonal_cartesian_norm_eq_one


set_option autoImplicit true
@[expose] public section
public section
open NewtonianLipschitz
namespace NewtonianLipschitz
namespace NewtonianPointSource
theorem _root_.solution :
    ∃ h : Vec3, ‖h‖ = 1 ∧
      (∀ s : ℝ, 0 < s →
        (1 : ℝ) ≤
          ‖normalizedVector candidateCriticalPoint candidateCriticalPoint +
            s • h‖ ∧
        ‖(normalizedVector candidateCriticalPoint candidateCriticalPoint +
            s • h) -
          normalizedVector candidateCriticalPoint candidateCriticalPoint‖ =
            s ∧
        normalizedVector candidateCriticalPoint candidateCriticalPoint +
          s • h ≠
            normalizedVector candidateCriticalPoint candidateCriticalPoint) ∧
      Filter.Tendsto
        (fun s : ℝ =>
          ‖s⁻¹ •
            (NewtonianPointSource.unitAxis.accelerationField
                (normalizedVector candidateCriticalPoint candidateCriticalPoint +
                  s • h) -
              NewtonianPointSource.unitAxis.accelerationField
                (normalizedVector candidateCriticalPoint candidateCriticalPoint))‖)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds candidateMaximum) := by
  let c : NewtonianPointSource := NewtonianPointSource.unitAxis
  let x : Vec3 :=
    normalizedVector candidateCriticalPoint candidateCriticalPoint
  obtain ⟨h, hunit, haction, hsafe⟩ :=
    NewtonianPointSource.unitAxis_exists_safe_distinct_secant_pairs
  refine ⟨h, hunit, hsafe, ?_⟩
  have hnorm : ‖x‖ = (1 : ℝ) :=
    criticalDiagonal_cartesian_norm_eq_one
  have hx : x ≠ 0 := by
    intro hzero
    rw [hzero, norm_zero] at hnorm
    norm_num at hnorm
  have hf : HasFDerivAt c.accelerationField
      (fderiv ℝ c.accelerationField x) x :=
    (c.accelerationField_contDiffAt x hx).differentiableAt_one.hasFDerivAt
  have hline :=
    (hf.hasLineDerivAt h).tendsto_slope_zero_right
  have hnorm_limit := hline.norm
  change Filter.Tendsto
    (fun s : ℝ =>
      ‖s⁻¹ •
        (NewtonianPointSource.unitAxis.accelerationField
          (normalizedVector candidateCriticalPoint candidateCriticalPoint +
            s • h) -
        NewtonianPointSource.unitAxis.accelerationField
          (normalizedVector candidateCriticalPoint candidateCriticalPoint))‖)
    (nhdsWithin 0 (Set.Ioi 0))
    (nhds ‖(fderiv ℝ NewtonianPointSource.unitAxis.accelerationField
      (normalizedVector candidateCriticalPoint candidateCriticalPoint)) h‖)
    at hnorm_limit
  rw [haction] at hnorm_limit
  exact hnorm_limit
end NewtonianPointSource
end NewtonianLipschitz
