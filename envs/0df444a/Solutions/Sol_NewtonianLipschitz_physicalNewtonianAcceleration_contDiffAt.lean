-- Prove2me | solution 1 for NewtonianLipschitz.physicalNewtonianAcceleration_contDiffAt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T03:37:30.914456+00:00
-- url     : https://prove2.me/submissions/26d114fe-ae7b-48e9-a827-851c7ba0aca7

module
public import Definitions.Def_NewtonianLipschitz_Field
public import Definitions.Def_NewtonianLipschitz_Smoothness

set_option autoImplicit true
@[expose] public section
public section
open scoped NNReal Topology InnerProductSpace
open NewtonianLipschitz
namespace NewtonianLipschitz
theorem _root_.solution
    (μ : ℝ) (q : PhysicalVec3) (hq : q ≠ 0) :
    ContDiffAt ℝ 1 (physicalNewtonianAcceleration μ) q := by
  have hnorm : ContDiffAt ℝ 1 (fun x : PhysicalVec3 => ‖x‖) q :=
    contDiffAt_norm ℝ hq
  have hpow : ContDiffAt ℝ 1
      (fun x : PhysicalVec3 => ‖x‖ ^ 3) q := hnorm.pow 3
  have hnonzero : ‖q‖ ^ 3 ≠ 0 := by
    exact pow_ne_zero _ (norm_ne_zero_iff.mpr hq)
  have hscalar : ContDiffAt ℝ 1
      (fun x : PhysicalVec3 => (-(μ)) / (‖x‖ ^ 3)) q :=
    contDiffAt_const.div hpow hnonzero
  have hid : ContDiffAt ℝ 1 (fun x : PhysicalVec3 => x) q :=
    contDiffAt_id
  change ContDiffAt ℝ 1
    (fun x : PhysicalVec3 => (-(μ) / ‖x‖ ^ 3) • x) q
  exact hscalar.fun_smul hid
end NewtonianLipschitz
