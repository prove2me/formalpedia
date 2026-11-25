-- Prove2me | solution 1 for GroundTheory.Automorphic.ContragredientTranspose.map_thetaT_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:22:04.11384+00:00
-- url     : https://prove2.me/submissions/5f91ecba-2b90-4c89-8a2e-60febd5fb820

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_ContragredientTranspose_GelfandKazhdan
import Definitions.Def_GroundTheory_AutomorphicForms_ContragredientTranspose_Character
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerLocal
import Definitions.Def_GroundTheory_PowerSubgroups_CountableNeighbourhoods_MapThetaTInvariant
import Definitions.Def_GroundTheory_AutomorphicForms_ContragredientTranspose
import Theorems.Thm_P2M_GroundTheory_Variant__N1_map_thetaT_eq_self_258ed7b78331


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic GroundTheory.Automorphic.ContragredientTranspose
open MeasureTheory Measure GroundTheory.Automorphic.Whittaker
variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ}
namespace GroundTheory.Automorphic.ContragredientTranspose
theorem _root_.solution [MeasurableSpace (GL (Fin n) F)] [BorelSpace (GL (Fin n) F)]
    (μ : Measure (GL (Fin n) F)) [μ.IsHaarMeasure] :
    μ.map (thetaT : GL (Fin n) F ≃* GL (Fin n) F) = μ :=
  _root_.GroundTheory.Variant₂.N1.map_thetaT_eq_self μ
end GroundTheory.Automorphic.ContragredientTranspose
