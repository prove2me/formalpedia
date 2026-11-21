-- Prove2me | solution 1 for NewtonianLipschitz.NewtonianPointSource.finiteDifferentialAcceleration_norm_le_sum_global
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T04:19:47.326871+00:00
-- url     : https://prove2.me/submissions/ec27f733-6d3f-4668-a074-8f11a8a40f6d

module
public import Definitions.Def_NewtonianLipschitz_SafePlaneFiniteDifference
public import Definitions.Def_NewtonianLipschitz_UnconditionalFiniteSource
public import Theorems.Thm_NewtonianLipschitz_NewtonianPointSource_finiteDifferentialAcceleration_norm_le_of_oneSourceGlobal
public import Theorems.Thm_NewtonianLipschitz_oneSourceGlobalCandidateBound_proved


set_option autoImplicit true
@[expose] public section
public section
open NewtonianLipschitz
namespace NewtonianLipschitz
namespace NewtonianPointSource
theorem _root_.solution
    (sources : List (ℝ → NewtonianPointSource))
    (t : ℝ) (q : Vec3) (d : ℝ) (hd : 0 < d)
    (hsafe : ∀ source ∈ sources,
      d ≤ ‖(source t).displacement‖ ∧
      d ≤ ‖(source t).displacement + q‖) :
    ‖NewtonianPointSource.finiteDifferentialAcceleration sources t q‖ ≤
      ((1 / d ^ 3) *
        ((sources.map (fun source =>
          (source t).gravitationalParameter)).sum * candidateMaximum)) *
        ‖q‖ :=
  NewtonianPointSource.finiteDifferentialAcceleration_norm_le_of_oneSourceGlobal
    oneSourceGlobalCandidateBound_proved sources t q d hd hsafe
end NewtonianPointSource
end NewtonianLipschitz
