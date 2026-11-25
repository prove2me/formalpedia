-- Prove2me | solution 1 for GroundTheory.Automorphic.Parabolic.mem_unipotentCompact
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:17:59.74422+00:00
-- url     : https://prove2.me/submissions/fc8c872f-72d5-470d-b812-25e2afac9d98

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_InductionParabolicGroups
import Definitions.Def_GroundTheory_AutomorphicForms_MeasuresParabolic
import Definitions.Def_GroundTheory_AutomorphicForms_InductionParabolicLocal

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
theorem _root_.solution {e : ℕ} {u : unipotentRadical F n β} :
    u ∈ unipotentCompact F n β e ↔
      rankTorus F n β e * u * (rankTorus F n β e)⁻¹ ∈ integralGL F n := by
  rw [unipotentCompact, Subgroup.mem_subgroupOf, Subgroup.mem_comap]
  rfl
end GroundTheory.Automorphic.Parabolic
