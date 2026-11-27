-- Prove2me | solution 1 for GlobalTheory.cohOn.subsingleton_of_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T04:37:34.651578+00:00
-- url     : https://prove2.me/submissions/d64155f8-c243-4765-9d27-5eaf2da350f3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_ToAbSheafPreservesFiniteLimits
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_HdimEqZeroOfSubsingleton

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
open GlobalTheory.cohOn
namespace GlobalTheory.cohOn
theorem _root_.solution (F : X.Modules) [Injective ((toAbSheaf X).obj F)] (U : X.Opens)
    (n : ℕ) : Subsingleton (cohOn F U (n + 1)) :=
  SiteCoh.subsingleton_of_injective ((toAbSheaf X).obj F) n U
end GlobalTheory.cohOn
