-- Prove2me | solution 1 for NewtonianLipschitz.candidateMaximum_no_smaller_universal_fderiv_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T04:14:14.97176+00:00
-- url     : https://prove2.me/submissions/cc3af992-c0dd-4f2d-be6c-3af7e7e76d67

module
public import Definitions.Def_NewtonianLipschitz_CartesianBoxSharp
public import Definitions.Def_NewtonianLipschitz_DerivativeCoefficientMinimality
public import Theorems.Thm_NewtonianLipschitz_candidateMaximum_le_of_universal_fderiv_opNorm_bound

set_option autoImplicit true
@[expose] public section
public section
open NewtonianLipschitz
namespace NewtonianLipschitz
theorem _root_.solution
    (K : ℝ) (hK : K < candidateMaximum) :
    ¬ ∀ (c : NewtonianPointSource) (x : Vec3),
        x ≠ 0 →
          ‖fderiv ℝ c.accelerationField x‖ ≤
            (1 / ‖x‖ ^ 3) * (c.gravitationalParameter * K) := by
  intro hbound
  have hminimal :=
    candidateMaximum_le_of_universal_fderiv_opNorm_bound K hbound
  linarith
end NewtonianLipschitz
