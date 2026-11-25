-- Prove2me | solution 1 for GroundTheory.Automorphic.Whittaker.biTranslL_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T01:13:59.470636+00:00
-- url     : https://prove2.me/submissions/49575857-935c-439e-b4e9-3d97c38d1357

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
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
namespace GroundTheory.Automorphic.Whittaker
theorem _root_.solution (a b : G) (f : locallyConstantCompactSupport G ℂ ℂ) :
    biTranslL a b f = ltransL a (rtransL b f) :=
  Subtype.ext (funext fun x => by simp [mul_assoc])
end GroundTheory.Automorphic.Whittaker
