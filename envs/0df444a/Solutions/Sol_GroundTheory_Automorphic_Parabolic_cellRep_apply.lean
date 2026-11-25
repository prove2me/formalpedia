-- Prove2me | solution 1 for GroundTheory.Automorphic.Parabolic.cellRep_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:49:20.838995+00:00
-- url     : https://prove2.me/submissions/9b85317c-8e52-46da-8b25-3890e9c3b227

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GeometricLemmaCompact
import Definitions.Def_GroundTheory_AutomorphicForms_GeometricLemmaAverage
import Definitions.Def_GroundTheory_AutomorphicForms_GeometricLemmaCellGroups

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
open Matrix Iwasawa GLnLocal ValuativeRel Topology Set DoubleCoset
variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ}
variable {β : Fin n → ℕ} (w : Equiv.Perm (Fin n))
variable {W : Type*} [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ (levi F n β) W)
namespace GroundTheory.Automorphic.Parabolic
theorem _root_.solution (x : blockUpper F n (β ∘ w)) (v : W) :
    cellRep β w σ x v = inflateTwist F n β σ (permConj F β w x) v := rfl
end GroundTheory.Automorphic.Parabolic
