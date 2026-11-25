-- Prove2me | solution 1 for GroundTheory.Automorphic.GodementSectionLocal.ord_unifPow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:35:47.946936+00:00
-- url     : https://prove2.me/submissions/dc434ee8-ee63-4b4f-ae84-354604e83bf1

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_LocalZeta
import Definitions.Def_GroundTheory_AutomorphicForms_GLnLocal
import Definitions.Def_GroundTheory_AutomorphicForms_GL2_GodementSectionLocal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix Filter Topology
open scoped NNReal ValuativeRel
open GroundTheory GroundTheory.Automorphic GroundTheory.Automorphic.GodementSectionLocal
open GroundTheory.LocalField
noncomputable section
set_option linter.unusedSectionVars false
variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
variable [MeasurableSpace F] [BorelSpace F]
omit [MeasurableSpace F] [BorelSpace F]
namespace GroundTheory.Automorphic.GodementSectionLocal
theorem _root_.solution (k : ℤ) : ord ((unifPow k : Fˣ) : F) = k := ord_unifUnit_zpow k
end GroundTheory.Automorphic.GodementSectionLocal
