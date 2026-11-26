-- Prove2me | solution 1 for GroundTheory.Automorphic.expChartUnits_symm_apply
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-26T03:25:11.231243+00:00
-- url     : https://prove2.me/submissions/4290f14e-146c-4462-ad4d-a73bb6feefa9

import Definitions.Def_GroundTheory_AutomorphicForms_RealGroupsLie
import Mathlib


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open scoped Manifold ContDiff Topology
open NormedSpace Set
set_option linter.unusedSectionVars false
variable (𝕂 : Type*) [RCLike 𝕂] {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra 𝕂 𝔸] [CompleteSpace 𝔸]
local notation "𝔢" => expPartialHomeomorph 𝕂 𝔸
theorem _root_.solution (g : 𝔸ˣ) (X : 𝔸) :
    (((expChartUnits 𝕂 g).symm X : 𝔸ˣ) : 𝔸) = g * exp X := by
  first
    | (intros; simp [expChartUnits])
    | (intros; unfold expChartUnits; simp)
    | (intros; simp [expChartUnits]; done)
    | (intros; ext; simp [expChartUnits])
    | (intros; simp only [expChartUnits]; rfl)
    | (intros; constructor <;> intro h <;> simp_all [expChartUnits])
    | (intros; refine ⟨?_, ?_⟩ <;> simp [expChartUnits])
    | (intros; unfold expChartUnits; split_ifs <;> simp_all)
    | (intros; unfold expChartUnits; positivity)
    | (intros; unfold expChartUnits; ring)
    | (intros; unfold expChartUnits; exact?)
    | (intros; aesop (add norm simp [expChartUnits]))
    | (intros; simp [expChartUnits] <;> aesop)
    | (intros; exact expChartUnits.symm ..)
    | (intros; exact expChartUnits.comm ..)
  trace "HIT_46_1"

