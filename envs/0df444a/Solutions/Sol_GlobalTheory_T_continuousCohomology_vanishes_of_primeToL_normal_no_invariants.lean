-- Prove2me | solution 1 for GlobalTheory.T.continuousCohomology_vanishes_of_primeToL_normal_no_invariants
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:05:21.811003+00:00
-- url     : https://prove2.me/submissions/1bc36ffd-2c97-4f8e-8f25-fbd72cea83b6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ContinuousCohomologyVanishesOfPrimeToLNormalNoIn
import Definitions.Def_ReciprocityTheory_GaloisValuations_ContinuousConstSMulQuotient
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ContinuousCohomologyVanishesOfPrimeToLNormalNoInStatement
import Theorems.Thm_GlobalTheory_PrimeToNormalVanishing_cohomology_vanishes


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.Gal
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (Γ : Type) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] [T2Space Γ] [TotallyDisconnectedSpace Γ] (R M : Type) [CommRing R] [AddCommGroup M] [Module R M] [TopologicalSpace M] [DiscreteTopology M] [ContinuousConstSMul R M] (ρ : Representation R Γ M) (l : ℕ) (J : Subgroup Γ), l.Prime → J.Normal → IsClosed (J : Set Γ) → (∀ U : Subgroup Γ, U.Normal → IsOpen (U : Set Γ) → ∀ j ∈ J, ∃ n, Nat.Coprime n l ∧ j ^ n ∈ U) → ContAction ρ → (∀ m : M, ∃ n, l ^ n • m = 0) → (∀ m : M, (∀ j ∈ J, ρ j m = m) → m = 0) → H0 ρ = ⊥ ∧ Subsingleton (H1 ρ) ∧ Subsingleton (H2 ρ) := by
  first | exact @GlobalTheory.PrimeToNormalVanishing.cohomology_vanishes | exact GlobalTheory.PrimeToNormalVanishing.cohomology_vanishes | (intros; apply GlobalTheory.PrimeToNormalVanishing.cohomology_vanishes <;> assumption)
end _root_.GlobalTheory.T
