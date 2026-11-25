-- Prove2me | solution 1 for GroundTheory.Arith.SchemeCoh.range_towerComp_succ_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:47:56.709309+00:00
-- url     : https://prove2.me/submissions/687b9ec1-67f8-4109-b939-bd2d2ffb693e

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ProperCohomology_FormalLimit
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_towerComp_succ

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
theorem _root_.solution (n k : ℕ) :
    LinearMap.range (towerComp τ n (k + 1)) ≤ LinearMap.range (towerComp τ n k) := by
  rw [towerComp_succ, LinearMap.range_comp]
  exact LinearMap.map_le_range
end GroundTheory.Arith.SchemeCoh
