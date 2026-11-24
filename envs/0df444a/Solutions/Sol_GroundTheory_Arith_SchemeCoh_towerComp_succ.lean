-- Prove2me | solution 1 for GroundTheory.Arith.SchemeCoh.towerComp_succ
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:59:35.17657+00:00
-- url     : https://prove2.me/submissions/d0568c1e-da79-4446-ba75-fcdd9fec5166

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
theorem _root_.solution (n k : ℕ) : towerComp τ n (k + 1) = (towerComp τ n k).comp (τ (n + k)) :=
  rfl
end GroundTheory.Arith.SchemeCoh
