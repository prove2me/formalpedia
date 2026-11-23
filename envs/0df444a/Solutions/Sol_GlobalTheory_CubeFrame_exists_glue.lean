-- Prove2me | solution 1 for GlobalTheory.CubeFrame.exists_glue
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:01:39.564176+00:00
-- url     : https://prove2.me/submissions/ec2db24e-25e0-484e-b06b-3b51f173d462

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsGlobalFrameOfLocal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Matrix Filter Topology
open scoped BigOperators Real
open GlobalTheory GlobalTheory.CubeFrame
namespace GlobalTheory.CubeFrame
theorem _root_.solution {X J : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X] {U : Set X}
    {A : J → Set X} {F : J → X → ℂ} (hA : ∀ j, IsOpen (A j)) (hcov : ∀ x, ∃ j, x ∈ A j)
    (hF : ∀ j, DifferentiableOn ℂ (F j) (U ∩ A j))
    (hagree : ∀ j k x, x ∈ U → x ∈ A j → x ∈ A k → F j x = F k x) :
    ∃ G : X → ℂ, DifferentiableOn ℂ G U ∧ ∀ j x, x ∈ U → x ∈ A j → G x = F j x := by
  choose σ hσ using hcov
  have key : ∀ j x, x ∈ U → x ∈ A j → F (σ x) x = F j x :=
    fun j x hx hj => hagree _ _ x hx (hσ x) hj
  refine ⟨fun x => F (σ x) x, fun x hx => ?_, key⟩
  have h1 : DifferentiableWithinAt ℂ (fun y => F (σ y) y) (U ∩ A (σ x)) x :=
    ((hF (σ x)).congr fun y hy => key _ y hy.1 hy.2) x ⟨hx, hσ x⟩
  exact (differentiableWithinAt_inter ((hA _).mem_nhds (hσ x))).mp h1
end GlobalTheory.CubeFrame
