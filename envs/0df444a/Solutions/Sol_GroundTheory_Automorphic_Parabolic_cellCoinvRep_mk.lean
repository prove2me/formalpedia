-- Prove2me | solution 1 for GroundTheory.Automorphic.Parabolic.cellCoinvRep_mk
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:57:18.458803+00:00
-- url     : https://prove2.me/submissions/02258e11-f75c-42cc-a22d-12ce6cf1efb5

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
variable {β γ : Fin n → ℕ} {w : Equiv.Perm (Fin n)} {W : Type*} [AddCommGroup W] [Module ℂ W]
  (σ : Representation ℂ (levi F n β) W)
namespace GroundTheory.Automorphic.Parabolic
theorem _root_.solution (b : cellLeviParabolic F β γ w) (v : W) :
    cellCoinvRep σ b (Representation.Coinvariants.mk _ v) =
      Representation.Coinvariants.mk _ (cellRepM β γ w σ b v) := rfl
end GroundTheory.Automorphic.Parabolic
