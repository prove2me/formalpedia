-- Prove2me | solution 1 for NewtonianLipschitz.NewtonianPointSource.unitAxis_exists_safe_sharp_outward_ray
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T04:16:14.429907+00:00
-- url     : https://prove2.me/submissions/88b9a2d4-0d7b-460e-bf9e-6e3db7398a23

module
public import Definitions.Def_NewtonianLipschitz_DerivativeAttainingDirection
public import Definitions.Def_NewtonianLipschitz_AdmissibleCriticalDirection
public import Theorems.Thm_NewtonianLipschitz_NewtonianPointSource_unitAxis_exists_outward_attaining_direction
public import Theorems.Thm_NewtonianLipschitz_criticalDiagonal_outward_ray_cartesian_clearance

set_option autoImplicit true
@[expose] public section
public section
open NewtonianLipschitz
namespace NewtonianLipschitz
namespace NewtonianPointSource
theorem _root_.solution :
    ∃ h : Vec3, ‖h‖ ≤ 1 ∧
      ‖(fderiv ℝ NewtonianPointSource.unitAxis.accelerationField
        (normalizedVector candidateCriticalPoint candidateCriticalPoint)) h‖ =
          candidateMaximum ∧
      ∀ s : ℝ, 0 ≤ s →
        (1 : ℝ) ≤
          ‖normalizedVector candidateCriticalPoint candidateCriticalPoint +
            s • h‖ := by
  obtain ⟨h, hnorm, hfirst, haction⟩ :=
    NewtonianPointSource.unitAxis_exists_outward_attaining_direction
  refine ⟨h, hnorm, haction, ?_⟩
  intro s hs
  exact criticalDiagonal_outward_ray_cartesian_clearance
    h hfirst s hs
end NewtonianPointSource
end NewtonianLipschitz
