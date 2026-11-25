-- Prove2me | solution 1 for GroundTheory.Automorphic.Parabolic.isCompact_unipotentCompact
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:38:35.503683+00:00
-- url     : https://prove2.me/submissions/dedaed4c-3625-4847-81a2-8d45d2b25878

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_InductionParabolicGroups
import Definitions.Def_GroundTheory_AutomorphicForms_MeasuresParabolic
import Definitions.Def_GroundTheory_AutomorphicForms_InductionParabolicLocal
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_isClosed_unipotentRadical
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_coe_unipotentCompact
import Theorems.Thm_GroundTheory_Automorphic_GLnLocal_isCompact_integralGL


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
    IsCompact (unipotentCompact F n β e : Set (unipotentRadical F n β)) := by
  rw [coe_unipotentCompact]
  exact isClosed_unipotentRadical.isClosedEmbedding_subtypeVal.isCompact_preimage
    ((conjHomeomorph _).isCompact_preimage.2 (isCompact_integralGL F n))
end GroundTheory.Automorphic.Parabolic
