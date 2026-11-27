-- Prove2me | solution 1 for GroundTheory.Arith.SchemeCoh.range_towerComp_antitone
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T04:42:58.64468+00:00
-- url     : https://prove2.me/submissions/3712c1de-ba40-435c-8511-66c526daa1d9

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ProperCohomology_FormalLimit
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_range_towerComp_succ_le

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
theorem _root_.solution (n : ℕ) {k l : ℕ} (h : k ≤ l) :
    LinearMap.range (towerComp τ n l) ≤ LinearMap.range (towerComp τ n k) := by
  induction l, h using Nat.le_induction with
  | base => exact le_rfl
  | succ l _ ih => exact (range_towerComp_succ_le τ n l).trans ih
end GroundTheory.Arith.SchemeCoh
