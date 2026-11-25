-- Prove2me | solution 1 for GroundTheory.Automorphic.Parabolic.isCompact_subgroupOf_levi
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:34:35.758638+00:00
-- url     : https://prove2.me/submissions/d8589ada-d0a8-45bf-ae6c-0c537b9f3b7d

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_InductionParabolic
import Definitions.Def_GroundTheory_AutomorphicForms_AdmissibleInduction
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_isClosed_levi

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
variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ} {α : Type*} [LinearOrder α] {β : Fin n → α}
namespace GroundTheory.Automorphic.Parabolic
theorem _root_.solution {K : Subgroup (GL (Fin n) F)}
    (hK : IsCompact (K : Set (GL (Fin n) F))) :
    IsCompact ((K.subgroupOf (levi F n β) : Subgroup (levi F n β)) : Set (levi F n β)) := by
  rw [Subgroup.coe_subgroupOf]
  exact isClosed_levi.isClosedEmbedding_subtypeVal.isCompact_preimage hK
end GroundTheory.Automorphic.Parabolic
