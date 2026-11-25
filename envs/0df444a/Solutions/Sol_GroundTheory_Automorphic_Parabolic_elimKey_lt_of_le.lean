-- Prove2me | solution 1 for GroundTheory.Automorphic.Parabolic.elimKey_lt_of_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:44:11.583802+00:00
-- url     : https://prove2.me/submissions/6c7ec291-ea80-42bc-b576-6a6cff4d1eb5

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_InductionParabolic
import Definitions.Def_GroundTheory_AutomorphicForms_AffineBruhat
import Definitions.Def_GroundTheory_AutomorphicForms_IwahoriFactorization
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_elimKey_injective

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
variable {F : Type*} [Field F] {n : ℕ} {α : Type*} [LinearOrder α] (β : Fin n → α)
variable {β}
namespace GroundTheory.Automorphic.Parabolic
theorem _root_.solution {i j : Fin n} (h : elimKey β i ≤ elimKey β j) (hij : i ≠ j) :
    elimKey β i < elimKey β j :=
  lt_of_le_of_ne h fun e => hij (elimKey_injective e)
end GroundTheory.Automorphic.Parabolic
