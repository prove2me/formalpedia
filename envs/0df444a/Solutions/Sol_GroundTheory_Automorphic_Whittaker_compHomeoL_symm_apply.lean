-- Prove2me | solution 1 for GroundTheory.Automorphic.Whittaker.compHomeoL_symm_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T01:13:12.990775+00:00
-- url     : https://prove2.me/submissions/9a6e5f35-4b87-4b9e-a69d-1982345694aa

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
    compHomeoL e (compHomeoL e.symm f) = f :=
  Subtype.ext (funext fun x => by simp)
end GroundTheory.Automorphic.Whittaker
