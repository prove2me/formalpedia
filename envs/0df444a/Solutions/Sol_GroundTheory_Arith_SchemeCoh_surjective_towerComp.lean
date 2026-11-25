-- Prove2me | solution 1 for GroundTheory.Arith.SchemeCoh.surjective_towerComp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:48:02.657945+00:00
-- url     : https://prove2.me/submissions/984cf5f1-a56c-4e0b-9413-5e9cef20c1bf

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
variable {A : Type u} [CommRing A]
  {P E Q : ℕ → Type u} [∀ n, AddCommGroup (P n)] [∀ n, Module A (P n)]
  [∀ n, AddCommGroup (E n)] [∀ n, Module A (E n)] [∀ n, AddCommGroup (Q n)]
  [∀ n, Module A (Q n)]
  (τP : ∀ n, P (n + 1) →ₗ[A] P n) (τE : ∀ n, E (n + 1) →ₗ[A] E n) (τQ : ∀ n, Q (n + 1) →ₗ[A] Q n)
  (ι : ∀ n, P n →ₗ[A] E n) (π : ∀ n, E n →ₗ[A] Q n)
  (hι : ∀ n, (τE n).comp (ι (n + 1)) = (ι n).comp (τP n))
  (hπ : ∀ n, (τQ n).comp (π (n + 1)) = (π n).comp (τE n))
variable (hinj : ∀ n, Function.Injective (ι n))
  (hex : ∀ n, LinearMap.range (ι n) = LinearMap.ker (π n))
omit [∀ n, AddCommGroup (E n)] [∀ n, Module A (E n)] [∀ n, AddCommGroup (Q n)]
  [∀ n, Module A (Q n)]
namespace GroundTheory.Arith.SchemeCoh
theorem _root_.solution (hsurj : ∀ n, Function.Surjective (τP n)) (n k : ℕ) :
    Function.Surjective (towerComp τP n k) := by
  induction k with
  | zero => exact Function.surjective_id
  | succ k ih =>
    rw [towerComp_succ, LinearMap.coe_comp]
    exact ih.comp (hsurj (n + k))
end GroundTheory.Arith.SchemeCoh
