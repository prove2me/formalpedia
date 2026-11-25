-- Prove2me | solution 1 for GroundTheory.Automorphic.GodementSectionLocal.indicator_shellAt_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:51:49.768928+00:00
-- url     : https://prove2.me/submissions/90ea2414-c31d-4609-85f9-14c03d9a588a

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_LocalZeta
import Definitions.Def_GroundTheory_AutomorphicForms_GLnLocal
import Definitions.Def_GroundTheory_AutomorphicForms_GL2_GodementSectionLocal
import Theorems.Thm_GroundTheory_Automorphic_GodementSectionLocal_isClopen_shellAt
import Theorems.Thm_GroundTheory_Automorphic_GodementSectionLocal_indicator_mem_schwartzBruhat2

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
theorem _root_.solution {Φ : (Fin 2 → F) → ℂ} (hΦ : Φ ∈ schwartzBruhat2 F) (m : ℤ) :
    (shellAt F m).indicator Φ ∈ schwartzBruhat2 F :=
  indicator_mem_schwartzBruhat2 (isClopen_shellAt m) (fun _ hx ↦ hx.1) hΦ.1
end GroundTheory.Automorphic.GodementSectionLocal
