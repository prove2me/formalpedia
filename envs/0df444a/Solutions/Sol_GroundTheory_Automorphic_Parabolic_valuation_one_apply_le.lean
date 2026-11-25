-- Prove2me | solution 1 for GroundTheory.Automorphic.Parabolic.valuation_one_apply_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:21:15.086899+00:00
-- url     : https://prove2.me/submissions/a7026a42-6f7a-44fc-b916-074984ac9e56

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_InductionParabolic
import Definitions.Def_GroundTheory_AutomorphicForms_AffineBruhat
import Definitions.Def_GroundTheory_AutomorphicForms_IwahoriFactorization

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
  {n : ℕ} {α : Type*} [LinearOrder α] {β : Fin n → α}
local notation "ϖ" => ((GLnLocal.uniformizer F : 𝒪[F]) : F)
omit [TopologicalSpace F] [IsNonarchimedeanLocalField F]
namespace GroundTheory.Automorphic.Parabolic
theorem _root_.solution (i j : Fin n) :
    valuation F ((1 : Matrix (Fin n) (Fin n) F) i j) ≤ 1 := by
  by_cases h : i = j
  · rw [h, one_apply_eq, map_one]
  · rw [one_apply_ne h, map_zero]
    exact zero_le
end GroundTheory.Automorphic.Parabolic
