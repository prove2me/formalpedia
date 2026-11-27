-- Prove2me | solution 1 for GlobalTheory.hdim_biprod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T04:38:42.75027+00:00
-- url     : https://prove2.me/submissions/6eae3edc-fe32-4be3-9431-5c7993325c20

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
variable (k : Type v) [Field k] [Algebra k Γ(X, ⊤)] {F G : X.Modules} (n : ℕ)
namespace GlobalTheory
theorem _root_.solution [Module.Finite k (coh F n)] [Module.Finite k (coh G n)] :
    hdim k (F ⊞ G) n = hdim k F n + hdim k G n :=
  (cohOn.biprodEquiv k ⊤ n F G).finrank_eq.trans Module.finrank_prod
end GlobalTheory
