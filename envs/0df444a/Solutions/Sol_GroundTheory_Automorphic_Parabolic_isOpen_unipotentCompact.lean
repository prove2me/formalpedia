-- Prove2me | solution 1 for GroundTheory.Automorphic.Parabolic.isOpen_unipotentCompact
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:43:14.133214+00:00
-- url     : https://prove2.me/submissions/01b3d77c-be4f-479b-90ff-a3a4711b1fd9

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_InductionParabolicGroups
import Definitions.Def_GroundTheory_AutomorphicForms_MeasuresParabolic
import Definitions.Def_GroundTheory_AutomorphicForms_InductionParabolicLocal
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_coe_unipotentCompact

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
open Matrix Iwasawa GLnLocal ValuativeRel Topology Filter Set
variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
variable (F) (n : ℕ) {α : Type*} [LinearOrder α] (β : Fin n → α)
variable {F n β}
namespace GroundTheory.Automorphic.Parabolic
theorem _root_.solution (e : ℕ) :
    IsOpen (unipotentCompact F n β e : Set (unipotentRadical F n β)) := by
  rw [coe_unipotentCompact]
  exact ((isOpen_integralGL F n).preimage (conjHomeomorph _).continuous).preimage
    continuous_subtype_val
end GroundTheory.Automorphic.Parabolic
