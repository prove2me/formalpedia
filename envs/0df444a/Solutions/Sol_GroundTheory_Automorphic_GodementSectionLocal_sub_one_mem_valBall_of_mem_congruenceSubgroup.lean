-- Prove2me | solution 1 for GroundTheory.Automorphic.GodementSectionLocal.sub_one_mem_valBall_of_mem_congruenceSubgroup
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:46:29.895801+00:00
-- url     : https://prove2.me/submissions/32667e9c-f026-42fa-b363-9bb801be7293

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_LocalZeta
import Definitions.Def_GroundTheory_AutomorphicForms_GLnLocal
import Definitions.Def_GroundTheory_AutomorphicForms_GL2_GodementSectionLocal
import Theorems.Thm_GroundTheory_Automorphic_GodementSectionLocal_mem_valBall_of_valuation_le

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
theorem _root_.solution {m : ℕ} {u : GL (Fin 2) F}
    (hu : u ∈ GLnLocal.congruenceSubgroup F 2 m) (i j : Fin 2) :
    (u : Matrix (Fin 2) (Fin 2) F) i j - (1 : Matrix (Fin 2) (Fin 2) F) i j ∈ valBall F m :=
  mem_valBall_of_valuation_le (((GLnLocal.mem_congruenceSubgroup_iff F 2).1 hu).2 i j)
end GroundTheory.Automorphic.GodementSectionLocal
