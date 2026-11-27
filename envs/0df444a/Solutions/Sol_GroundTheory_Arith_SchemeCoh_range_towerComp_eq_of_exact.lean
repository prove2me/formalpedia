-- Prove2me | solution 1 for GroundTheory.Arith.SchemeCoh.range_towerComp_eq_of_exact
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T04:43:02.33612+00:00
-- url     : https://prove2.me/submissions/61327b65-f0f1-48fc-a232-87170d606d01

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ProperCohomology_FormalLimit
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_towerComp_eq_zero_of_le
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_towerComp_comp_of_comm
import Theorems.Thm_P2M_GroundTheory_Arith_SchemeCoh_towerComp_comp_of_comm__9e39104e9438
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_surjective_towerComp

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
include hι hπ hex
namespace GroundTheory.Arith.SchemeCoh
theorem _root_.solution (hsurj : ∀ n, Function.Surjective (τP n)) {c : ℕ}
    (hc : ∀ n, towerComp τQ n c = 0) (n k : ℕ) (hk : c ≤ k) :
    LinearMap.range (towerComp τE n k) = LinearMap.range (ι n) := by
  apply le_antisymm
  · rintro _ ⟨e, rfl⟩
    rw [hex n, LinearMap.mem_ker]
    obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hk
    have := congrArg (fun f => f e) (towerComp_comp_of_comm' τE τQ π hπ n (c + j))
    simp only [LinearMap.comp_apply] at this
    rw [← this, towerComp_eq_zero_of_le τQ hc n j, LinearMap.zero_apply]
  · rintro _ ⟨p, rfl⟩
    obtain ⟨p', rfl⟩ := surjective_towerComp τP hsurj n k p
    refine ⟨ι (n + k) p', ?_⟩
    have := congrArg (fun f => f p') (towerComp_comp_of_comm τP τE ι hι n k)
    simpa only [LinearMap.comp_apply] using this
end GroundTheory.Arith.SchemeCoh
