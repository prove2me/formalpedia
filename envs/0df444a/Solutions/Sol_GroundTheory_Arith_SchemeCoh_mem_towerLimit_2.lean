-- Prove2me | solution 2 for GroundTheory.Arith.SchemeCoh.mem_towerLimit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T04:42:48.721257+00:00
-- url     : https://prove2.me/submissions/d7d05e75-52f5-43d3-b0e5-31979c1c080b

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ProperCohomology_FormalLimit

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Arith GroundTheory.Arith.SchemeCoh
universe u
noncomputable section
variable {A : Type u} [CommRing A] {E : ℕ → Type u} [∀ n, AddCommGroup (E n)]
  [∀ n, Module A (E n)] (τ : ∀ n, E (n + 1) →ₗ[A] E n)
namespace GroundTheory.Arith.SchemeCoh
theorem _root_.solution (x : ∀ n, E n) : x ∈ towerLimit τ ↔ ∀ n, τ n (x (n + 1)) = x n :=
  Iff.rfl
end GroundTheory.Arith.SchemeCoh
