-- Prove2me | solution 1 for GlobalTheory.restrictGlobal_top
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:11:22.203051+00:00
-- url     : https://prove2.me/submissions/13c5d72f-f786-4769-9ad1-75f202b840b6

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
theorem _root_.solution (r : Γ(X, ⊤)) : restrictGlobal X ⊤ r = r := by
  have : (homOfLE le_top : (⊤ : X.Opens) ⟶ ⊤) = 𝟙 _ := rfl
  rw [restrictGlobal, this, op_id, X.presheaf.map_id]
  rfl
end GlobalTheory
