-- Prove2me | solution 1 for GroundTheory.Automorphic.GodementSectionLocal.localSection_mem_principalSeries
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T11:45:39.249802+00:00
-- url     : https://prove2.me/submissions/c2974921-6366-4344-9d3d-2108d4ebaed3

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_LocalZeta
import Definitions.Def_GroundTheory_AutomorphicForms_GLnLocal
import Definitions.Def_GroundTheory_AutomorphicForms_GL2_GodementSectionLocal
import Theorems.Thm_GroundTheory_Automorphic_GodementSectionLocal_localSection_borelElt_mul

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
namespace GroundTheory.Automorphic.GodementSectionLocal
theorem _root_.solution (χ₁ χ₂ : Fˣ →* ℂˣ) (s : ℂ) (Φ : (Fin 2 → F) → ℂ) :
    localSection χ₁ χ₂ s Φ ∈ principalSeries χ₁ χ₂ s :=
  fun a d x g ↦ localSection_borelElt_mul χ₁ χ₂ s Φ a d x g
end GroundTheory.Automorphic.GodementSectionLocal
