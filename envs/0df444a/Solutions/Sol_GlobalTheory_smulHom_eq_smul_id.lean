-- Prove2me | solution 1 for GlobalTheory.smulHom_eq_smul_id
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T04:41:44.593407+00:00
-- url     : https://prove2.me/submissions/1a23273e-d5c3-4e5d-bd70-3c44671757e8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_SubsingletonOfSubsingletonFreeSheaf
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_ToAbSheafPreservesFiniteLimits

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite Limits
universe w v u
noncomputable section
open GlobalTheory
variable {X : Scheme.{u}}
namespace GlobalTheory
theorem _root_.solution (F : X.Modules) (r : Γ(X, ⊤)) : smulHom F r = r • 𝟙 F :=
  (Category.id_comp _).symm
end GlobalTheory
