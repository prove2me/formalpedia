-- Prove2me | solution 1 for GlobalTheory.hdim_pi
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:59:05.470861+00:00
-- url     : https://prove2.me/submissions/9458de07-77fa-41c6-8edb-4db64208dc78

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
theorem _root_.solution {ι : Type t} [Fintype ι] (F : ι → X.Modules) [∀ i, Module.Finite k (coh (F i) n)] :
    hdim k (∏ᶜ F) n = ∑ i, hdim k (F i) n :=
  (cohOn.piEquiv k ⊤ n F).finrank_eq.trans (Module.finrank_pi_fintype k)
end GlobalTheory
