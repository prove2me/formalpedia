-- Prove2me | solution 1 for GroundTheory.Automorphic.Parabolic.rankTorus_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:14:42.292394+00:00
-- url     : https://prove2.me/submissions/ffa84d37-bf8d-48c9-a628-7e49bc710f38

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
theorem _root_.solution (e m : ℕ) : rankTorus F n β e ^ m = rankTorus F n β (e * m) := by
  rw [rankTorus, rankTorus, torusPow, torusPow, ← map_pow]
  congr 1
  funext i
  rw [Pi.pow_apply, ← zpow_natCast, ← _root_.zpow_mul]
  congr 1
  push_cast
  ring
end GroundTheory.Automorphic.Parabolic
