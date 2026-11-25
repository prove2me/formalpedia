-- Prove2me | solution 1 for GroundTheory.Automorphic.GodementJacquet.coe_coordEquiv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:45:56.646657+00:00
-- url     : https://prove2.me/submissions/e5ac474a-7639-4290-8538-2b9d0a046339

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GL2_GJZetaDefs
import Definitions.Def_GroundTheory_AutomorphicForms_Measures
import Definitions.Def_GroundTheory_AutomorphicForms_GL2_GJParabolicFubini

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
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.GodementJacquet
open Matrix GLnLocal Parabolic Iwasawa Measures MeasureTheory Measure Topology Set
open scoped NNReal ENNReal
set_option linter.unusedSectionVars false
variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ} {α : Type*} [LinearOrder α]
variable (β : Fin n → α)
namespace GroundTheory.Automorphic.GodementJacquet
theorem _root_.solution : ⇑(coordEquiv (F := F) β) = coordAddEquiv β := rfl
end GroundTheory.Automorphic.GodementJacquet
