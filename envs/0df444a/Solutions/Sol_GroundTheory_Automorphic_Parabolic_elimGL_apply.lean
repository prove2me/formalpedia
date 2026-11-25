-- Prove2me | solution 1 for GroundTheory.Automorphic.Parabolic.elimGL_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:21:24.294425+00:00
-- url     : https://prove2.me/submissions/6e7e6436-74b9-47f4-8609-6ad50ec1a730

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
variable {F : Type*} [Field F] {n : ℕ} {α : Type*} [LinearOrder α] (β : Fin n → α)
variable {β}
variable (β)
variable {β}
variable (β)
variable {β}
namespace GroundTheory.Automorphic.Parabolic
theorem _root_.solution (h : Matrix (Fin n) (Fin n) F) (a i k : Fin n) :
    (elimGL β h a : GL (Fin n) F) i k = (1 : Matrix (Fin n) (Fin n) F) i k - elimCol β h a i k :=
  rfl
end GroundTheory.Automorphic.Parabolic
