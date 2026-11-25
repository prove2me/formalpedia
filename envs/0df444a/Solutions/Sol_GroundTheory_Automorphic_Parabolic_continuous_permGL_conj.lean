-- Prove2me | solution 1 for GroundTheory.Automorphic.Parabolic.continuous_permGL_conj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T11:59:58.301683+00:00
-- url     : https://prove2.me/submissions/0353b5a6-501f-4160-b11e-65c09b6fcda4

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
  {σ : Representation ℂ (levi F n β) W}
namespace GroundTheory.Automorphic.Parabolic
theorem _root_.solution (w : Equiv.Perm (Fin n)) :
    Continuous fun x : GL (Fin n) F => permGL F w * x * (permGL F w)⁻¹ :=
  (conjHomeomorph (permGL F w)).continuous
end GroundTheory.Automorphic.Parabolic
