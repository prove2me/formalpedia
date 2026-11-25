-- Prove2me | solution 1 for GroundTheory.Automorphic.Parabolic.isCompact_subgroupOf_cellUnipotent
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T13:09:05.6349+00:00
-- url     : https://prove2.me/submissions/18f5ea26-7458-4c5c-a33b-fba17d845a11

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GeometricLemmaJacquetCell
import Definitions.Def_GroundTheory_AutomorphicForms_InductionJacquet
import Definitions.Def_GroundTheory_AutomorphicForms_GeometricLemmaCellKernel
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_isClosed_cellUnipotent
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_isCompact_unipotentCompactG


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
set_option linter.unusedSectionVars false
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.Parabolic
open Matrix Iwasawa GLnLocal ValuativeRel Topology Set DoubleCoset Filter
variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ} {β γ : Fin n → ℕ} {w : Equiv.Perm (Fin n)}
namespace GroundTheory.Automorphic.Parabolic
theorem _root_.solution (e : ℕ) :
    IsCompact (((unipotentCompactG (F := F) γ e).subgroupOf (cellUnipotent F β γ w) :
      Subgroup (cellUnipotent F β γ w)) : Set (cellUnipotent F β γ w)) := by
  rw [Subgroup.coe_subgroupOf]
  exact isClosed_cellUnipotent.isClosedEmbedding_subtypeVal.isCompact_preimage
    (isCompact_unipotentCompactG e)
end GroundTheory.Automorphic.Parabolic
