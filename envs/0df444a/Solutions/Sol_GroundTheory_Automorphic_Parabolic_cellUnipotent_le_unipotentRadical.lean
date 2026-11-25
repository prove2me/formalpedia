-- Prove2me | solution 1 for GroundTheory.Automorphic.Parabolic.cellUnipotent_le_unipotentRadical
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:49:25.752291+00:00
-- url     : https://prove2.me/submissions/57f81336-28b1-4b52-b2e0-1988bdc3bcca

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
variable (F) (β γ : Fin n → ℕ) (w : Equiv.Perm (Fin n))
variable {F β γ w}
namespace GroundTheory.Automorphic.Parabolic
theorem _root_.solution : cellUnipotent F β γ w ≤ unipotentRadical F n γ :=
  inf_le_left
end GroundTheory.Automorphic.Parabolic
