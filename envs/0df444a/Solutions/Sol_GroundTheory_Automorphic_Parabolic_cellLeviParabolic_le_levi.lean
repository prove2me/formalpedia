-- Prove2me | solution 1 for GroundTheory.Automorphic.Parabolic.cellLeviParabolic_le_levi
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:57:45.769416+00:00
-- url     : https://prove2.me/submissions/a7aa5b39-414e-4e12-a59f-02db07b71d09

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
theorem _root_.solution : cellLeviParabolic F β γ w ≤ levi F n γ :=
  inf_le_left
end GroundTheory.Automorphic.Parabolic
