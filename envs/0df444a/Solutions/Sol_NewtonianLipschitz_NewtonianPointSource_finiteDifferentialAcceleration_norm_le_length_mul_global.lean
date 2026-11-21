-- Prove2me | solution 1 for NewtonianLipschitz.NewtonianPointSource.finiteDifferentialAcceleration_norm_le_length_mul_global
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T04:19:47.877684+00:00
-- url     : https://prove2.me/submissions/b2ae30ee-06da-44bc-a905-2b88cbdcb9d4

module
public import Definitions.Def_NewtonianLipschitz_SafePlaneFiniteDifference
public import Definitions.Def_NewtonianLipschitz_UnconditionalFiniteSource
public import Theorems.Thm_NewtonianLipschitz_NewtonianPointSource_finiteDifferentialAcceleration_norm_le_length_mul_of_oneSourceGlobal
public import Theorems.Thm_NewtonianLipschitz_oneSourceGlobalCandidateBound_proved


set_option autoImplicit true
@[expose] public section
public section
open NewtonianLipschitz
namespace NewtonianLipschitz
namespace NewtonianPointSource
theorem _root_.solution
    (sources : List (ℝ → NewtonianPointSource))
    (t : ℝ) (q : Vec3) (d M : ℝ) (hd : 0 < d)
    (hsafe : ∀ source ∈ sources,
      d ≤ ‖(source t).displacement‖ ∧
      d ≤ ‖(source t).displacement + q‖)
    (hcap : ∀ source ∈ sources,
      (source t).gravitationalParameter ≤ M) :
    ‖NewtonianPointSource.finiteDifferentialAcceleration sources t q‖ ≤
      ((1 / d ^ 3) *
        (((sources.length : ℝ) * M) * candidateMaximum)) * ‖q‖ :=
  NewtonianPointSource.finiteDifferentialAcceleration_norm_le_length_mul_of_oneSourceGlobal
    oneSourceGlobalCandidateBound_proved sources t q d M hd hsafe hcap
end NewtonianPointSource
end NewtonianLipschitz
