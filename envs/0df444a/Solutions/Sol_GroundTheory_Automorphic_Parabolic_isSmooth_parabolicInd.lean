-- Prove2me | solution 1 for GroundTheory.Automorphic.Parabolic.isSmooth_parabolicInd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:12:23.361812+00:00
-- url     : https://prove2.me/submissions/efc75f12-b9ac-4ff3-9431-48195587a13c

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_Induction
import Definitions.Def_GroundTheory_AutomorphicForms_InductionJacquet
import Definitions.Def_GroundTheory_AutomorphicForms_InductionParabolicLocal
import Definitions.Def_GroundTheory_AutomorphicForms_InductionParabolic
import Theorems.Thm_GroundTheory_Automorphic_isSmooth_indRep


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.Parabolic
open Matrix Iwasawa GLnLocal Topology Filter Set MeasureTheory Measure
open scoped NNReal
variable (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  (n : ℕ) {α : Type*} [LinearOrder α] (β : Fin n → α)
variable {F n β}
variable {W : Type*} [AddCommGroup W] [Module ℂ W]
namespace GroundTheory.Automorphic.Parabolic
theorem _root_.solution (σ : Representation ℂ (levi F n β) W) :
    IsSmooth (parabolicInd F n β σ) :=
  isSmooth_indRep _ _
end GroundTheory.Automorphic.Parabolic
