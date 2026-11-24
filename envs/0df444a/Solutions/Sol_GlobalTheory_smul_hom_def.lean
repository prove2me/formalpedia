-- Prove2me | solution 1 for GlobalTheory.smul_hom_def
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:33:49.504677+00:00
-- url     : https://prove2.me/submissions/7419c054-ae36-4bbd-b3bd-413d2d181be3

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
theorem _root_.solution {F G : X.Modules} (r : Γ(X, ⊤)) (φ : F ⟶ G) : r • φ = φ ≫ smulHom G r := rfl
end GlobalTheory
