-- Prove2me | solution 1 for GroundTheory.Automorphic.Whittaker.isMulRightInvariant_of_isInvInvariant
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T01:21:45.952795+00:00
-- url     : https://prove2.me/submissions/22a94156-f14d-47f8-838a-f1638a2240e1

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HeckeAlgebra
import Definitions.Def_GroundTheory_AutomorphicForms_SmoothRepContragredient
import Definitions.Def_GroundTheory_AutomorphicForms_SmoothRepSchur
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerCriterion
import Theorems.Thm_GroundTheory_Automorphic_Whittaker_BiEquivariantSigmaInvariant_inv

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
variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul G] [MeasurableInv G]
namespace GroundTheory.Automorphic.Whittaker
theorem _root_.solution (μ : Measure G) [μ.IsMulLeftInvariant]
    [μ.IsInvInvariant] : μ.IsMulRightInvariant :=
  by
  have : μ.inv.IsMulRightInvariant := inferInstance
  rwa [Measure.inv_eq_self] at this
end GroundTheory.Automorphic.Whittaker
