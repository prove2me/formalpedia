-- Prove2me | solution 1 for GroundTheory.Automorphic.GodementSectionLocal.comp_smul_mem_schwartzBruhat2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:44:40.853749+00:00
-- url     : https://prove2.me/submissions/8d6d8940-3547-4e0a-9e07-69989d638408

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
theorem _root_.solution {Φ : (Fin 2 → F) → ℂ} (hΦ : Φ ∈ schwartzBruhat2 F)
    (a : Fˣ) : (fun x ↦ Φ ((a : F) • x)) ∈ schwartzBruhat2 F :=
  ⟨hΦ.1.comp_continuous (continuous_const_smul (a : F)),
    hΦ.2.comp_homeomorph (Homeomorph.smulOfNeZero (a : F) a.ne_zero)⟩
end GroundTheory.Automorphic.GodementSectionLocal
