-- Prove2me | solution 1 for GlobalTheory.coh.zeroEquiv_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:31:55.033738+00:00
-- url     : https://prove2.me/submissions/7894a7b4-e6fa-4839-a202-c6b5e4a58970

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_ToAbSheafPreservesFiniteLimits
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_HdimEqZeroOfSubsingleton
import Theorems.Thm_GlobalTheory_cohOn_zeroEquiv_map
import Theorems.Thm_GlobalTheory_SiteCoh_zeroEquiv_map


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite Limits
universe t v u
noncomputable section
open GlobalTheory
variable {X : Scheme.{u}}
open GlobalTheory.coh
namespace GlobalTheory.coh
theorem _root_.solution {F G : X.Modules} (φ : F ⟶ G) (x : coh F 0) :
    zeroEquiv G (cohOn.map Γ(X, ⊤) φ ⊤ 0 x) = φ.app ⊤ (zeroEquiv F x) :=
  congrArg (sectionsOn.toΓ G ⊤) (cohOn.zeroEquiv_map Γ(X, ⊤) φ x)
end GlobalTheory.coh
