-- Prove2me | solution 1 for GroundTheory.Arith.SchemeCoh.towerComp_comp_of_comm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:59:34.918542+00:00
-- url     : https://prove2.me/submissions/5cd18fb0-1393-40c0-8b2e-c098ef9efdf7

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
variable {A : Type u} [CommRing A]
  {P E Q : ℕ → Type u} [∀ n, AddCommGroup (P n)] [∀ n, Module A (P n)]
  [∀ n, AddCommGroup (E n)] [∀ n, Module A (E n)] [∀ n, AddCommGroup (Q n)]
  [∀ n, Module A (Q n)]
  (τP : ∀ n, P (n + 1) →ₗ[A] P n) (τE : ∀ n, E (n + 1) →ₗ[A] E n) (τQ : ∀ n, Q (n + 1) →ₗ[A] Q n)
  (ι : ∀ n, P n →ₗ[A] E n) (π : ∀ n, E n →ₗ[A] Q n)
  (hι : ∀ n, (τE n).comp (ι (n + 1)) = (ι n).comp (τP n))
  (hπ : ∀ n, (τQ n).comp (π (n + 1)) = (π n).comp (τE n))
include hι
namespace GroundTheory.Arith.SchemeCoh
theorem _root_.solution (n k : ℕ) :
    (towerComp τE n k).comp (ι (n + k)) = (ι n).comp (towerComp τP n k) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change ((towerComp τE n k).comp (τE (n + k))).comp (ι (n + k + 1)) =
      (ι n).comp ((towerComp τP n k).comp (τP (n + k)))
    rw [LinearMap.comp_assoc, hι (n + k), ← LinearMap.comp_assoc, ih, LinearMap.comp_assoc]
end GroundTheory.Arith.SchemeCoh
