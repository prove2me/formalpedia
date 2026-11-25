-- Prove2me | solution 1 for GroundTheory.Automorphic.GodementSectionLocal.continuous_mul_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:41:59.246417+00:00
-- url     : https://prove2.me/submissions/0373c76a-9da8-4c33-8f4e-9c560787f29f

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_LocalZeta
import Definitions.Def_GroundTheory_AutomorphicForms_GLnLocal
import Definitions.Def_GroundTheory_AutomorphicForms_GL2_GodementSectionLocal
import Theorems.Thm_GroundTheory_LocalField_continuous_quasiChar_inv


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
theorem _root_.solution {χ₁ χ₂ : Fˣ →* ℂˣ} (h₁ : Continuous χ₁) (h₂ : Continuous χ₂) :
    Continuous (χ₁ * χ₂⁻¹) :=
  h₁.mul (continuous_quasiChar_inv h₂)
end GroundTheory.Automorphic.GodementSectionLocal
