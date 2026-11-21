-- Prove2me | solution 1 for NewtonianLipschitz.candidateMaximum_no_smaller_universal_safe_secant_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T04:22:59.82294+00:00
-- url     : https://prove2.me/submissions/6bbad797-4395-4795-82ec-830a59f52332

module
public import Definitions.Def_NewtonianLipschitz_AdmissibleCriticalDirection
public import Definitions.Def_NewtonianLipschitz_AdmissibleSecantPairs
public import Theorems.Thm_NewtonianLipschitz_candidateMaximum_le_of_universal_safe_secant_bound

set_option autoImplicit true
@[expose] public section
public section
open NewtonianLipschitz
namespace NewtonianLipschitz
theorem _root_.solution
    (K : ℝ) (hK : K < candidateMaximum) :
    ¬ ∀ x y : Vec3,
      (1 : ℝ) ≤ ‖x‖ → (1 : ℝ) ≤ ‖y‖ →
        ‖NewtonianPointSource.unitAxis.accelerationField x -
          NewtonianPointSource.unitAxis.accelerationField y‖ ≤
            K * ‖x - y‖ := by
  intro hall
  have hmin :=
    candidateMaximum_le_of_universal_safe_secant_bound K hall
  linarith
end NewtonianLipschitz
