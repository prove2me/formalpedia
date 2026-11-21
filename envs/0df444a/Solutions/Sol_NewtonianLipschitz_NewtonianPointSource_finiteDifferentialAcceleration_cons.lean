-- Prove2me | solution 1 for NewtonianLipschitz.NewtonianPointSource.finiteDifferentialAcceleration_cons
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T03:23:56.030005+00:00
-- url     : https://prove2.me/submissions/014bac92-1cb3-43a4-b36e-2501ddd25101

module
public import Definitions.Def_NewtonianLipschitz_Field
public import Definitions.Def_NewtonianLipschitz_FiniteSources
public import Theorems.Thm_NewtonianLipschitz_NewtonianPointSource_finiteDifferentialAcceleration_nil
public import Theorems.Thm_NewtonianLipschitz_ofLp_toPhysicalVec3
public import Theorems.Thm_NewtonianLipschitz_toPhysicalVec3_apply
public import Theorems.Thm_NewtonianLipschitz_toPhysicalVec3_zero
attribute [local simp] NewtonianLipschitz.ofLp_toPhysicalVec3
attribute [local simp] NewtonianLipschitz.toPhysicalVec3_apply
attribute [local simp] NewtonianLipschitz.toPhysicalVec3_zero


attribute [local simp] NewtonianLipschitz.NewtonianPointSource.finiteDifferentialAcceleration_nil

set_option autoImplicit true
@[expose] public section
public section
open NewtonianLipschitz
namespace NewtonianLipschitz
namespace NewtonianPointSource
theorem _root_.solution
    (source : ℝ → NewtonianPointSource)
    (sources : List (ℝ → NewtonianPointSource)) (t : ℝ) (q : Vec3) :
    NewtonianPointSource.finiteDifferentialAcceleration (source :: sources) t q =
      (source t).exactDifferentialAcceleration q +
        NewtonianPointSource.finiteDifferentialAcceleration sources t q := by
  simp [NewtonianPointSource.finiteDifferentialAcceleration]
end NewtonianPointSource
end NewtonianLipschitz
