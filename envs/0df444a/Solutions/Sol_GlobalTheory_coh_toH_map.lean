-- Prove2me | solution 1 for GlobalTheory.coh.toH_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T04:36:47.963161+00:00
-- url     : https://prove2.me/submissions/c2fa3f38-d932-448d-b129-9b6c650222ae

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_ToAbSheafPreservesFiniteLimits
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_HdimEqZeroOfSubsingleton
import Theorems.Thm_GlobalTheory_SiteCoh_terminalEquiv_map


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
theorem _root_.solution (R : Type v) [CommRing R] [Algebra R Γ(X, ⊤)] {F G : X.Modules} (φ : F ⟶ G)
    (n : ℕ) (x : coh F n) :
    toH G n (cohOn.map R φ ⊤ n x) = Sheaf.H.map ((toAbSheaf X).map φ) n (toH F n x) :=
  SiteCoh.terminalEquiv_map ((toAbSheaf X).map φ) n isTerminalTop (cohOn.toH' F ⊤ n x)
end GlobalTheory.coh
