-- Prove2me | solution 1 for GroundTheory.Automorphic.GodementSectionLocal.modPow_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T11:00:24.286436+00:00
-- url     : https://prove2.me/submissions/d18f8720-b2aa-4b8f-8ed3-1c37be8c840e

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_LocalZeta
import Definitions.Def_GroundTheory_AutomorphicForms_GLnLocal
import Definitions.Def_GroundTheory_AutomorphicForms_GL2_GodementSectionLocal
import Theorems.Thm_GroundTheory_LocalField_modulus_ne_zero


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
namespace GroundTheory.Automorphic.GodementSectionLocal
theorem _root_.solution {x : F} (hx : x ≠ 0) (s t : ℂ) : modPow x (s + t) = modPow x s * modPow x t :=
  Complex.cpow_add _ _ (Complex.ofReal_ne_zero.2 (by exact_mod_cast modulus_ne_zero hx))
end GroundTheory.Automorphic.GodementSectionLocal
