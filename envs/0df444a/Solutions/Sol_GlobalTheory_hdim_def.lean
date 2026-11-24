-- Prove2me | solution 1 for GlobalTheory.hdim_def
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T21:30:02.957104+00:00
-- url     : https://prove2.me/submissions/3296f1f0-3a59-4f1f-8ae8-19a203dd97a5

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
theorem _root_.solution (F : X.Modules) : hdim k F n = Module.finrank k (coh F n) := rfl
end GlobalTheory
