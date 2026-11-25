-- Prove2me | solution 1 for GroundTheory.Arith.SchemeCoh.towerComp_eq_zero_of_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:47:51.494783+00:00
-- url     : https://prove2.me/submissions/d50bf77e-f2d7-4d3f-9f6a-e2f2aabc1178

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
theorem _root_.solution {c : ℕ} (hc : ∀ n, towerComp τ n c = 0) (n j : ℕ) :
    towerComp τ n (c + j) = 0 := by
  induction j with
  | zero => exact hc n
  | succ j ih =>
    change (towerComp τ n (c + j)).comp (τ (n + (c + j))) = 0
    rw [ih, LinearMap.zero_comp]
end GroundTheory.Arith.SchemeCoh
