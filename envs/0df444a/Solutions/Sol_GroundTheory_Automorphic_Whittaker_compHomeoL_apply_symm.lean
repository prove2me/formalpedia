-- Prove2me | solution 1 for GroundTheory.Automorphic.Whittaker.compHomeoL_apply_symm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T04:45:22.105261+00:00
-- url     : https://prove2.me/submissions/9ccca365-4d8c-4745-bfa8-4da6a2d645d8

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HeckeAlgebra
import Definitions.Def_GroundTheory_AutomorphicForms_SmoothRepContragredient
import Definitions.Def_GroundTheory_AutomorphicForms_SmoothRepSchur
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerCriterion

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
open GroundTheory.Automorphic.Whittaker
open Set Filter Topology MeasureTheory
variable {X : Type*} [TopologicalSpace X]
namespace GroundTheory.Automorphic.Whittaker
theorem _root_.solution (e : X ≃ₜ X) (f : locallyConstantCompactSupport X ℂ ℂ) :
    compHomeoL e.symm (compHomeoL e f) = f :=
  Subtype.ext (funext fun x => by simp)
end GroundTheory.Automorphic.Whittaker
