-- Prove2me | solution 1 for GlobalTheory.FreeQuotient.tame_descent
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T16:55:18.912937+00:00
-- url     : https://prove2.me/submissions/4ee441ae-a76e-4523-aabe-589d242271b2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsUnitSmulEqOfBijectiveToSpanSingleton
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsFreeRingActionIffInertiaEqBotOfIsPrime
import Theorems.Thm_GlobalTheory_FreeQuotient_exists_sum_smul_eq_one
import Theorems.Thm_GlobalTheory_FreeQuotient_span_fixed_eq_top
import Theorems.Thm_GlobalTheory_FreeQuotient_exists_invariant_dual_basis
import Theorems.Thm_GlobalTheory_FreeQuotient_descent_of_invariant_dual_basis

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
open GlobalTheory
open GlobalTheory.FreeQuotient
variable {G : Type*} [Group G] [Finite G] {A : Type*} [CommRing A] [MulSemiringAction G A]
  (B : Type*) [CommRing B] [Algebra B A] [SMulCommClass G B A]
  [FaithfulSMul B A] [Algebra.IsInvariant B A G]
  (M : Type*) [AddCommGroup M] [Module A M] [DistribMulAction G M] [SMulDistribClass G A M]
  [Module B M] [IsScalarTower B A M] [SMulCommClass G B M]
namespace GlobalTheory.FreeQuotient
theorem _root_.solution [Module.Finite A M] [Module.Projective A M]
    (h : ∀ P : Ideal A, P.IsMaximal → (Nat.card (P.inertia G) : A) ∉ P)
    (hM : ∀ P : Ideal A, P.IsMaximal → ∀ g ∈ P.inertia G, ∀ m : M,
      g • m - m ∈ P • (⊤ : Submodule A M)) :
    IsBaseChange A (Representation.ofDistribMulAction B G M).invariants.subtype ∧
      Module.Finite B (Representation.ofDistribMulAction B G M).invariants ∧
      Module.Projective B (Representation.ofDistribMulAction B G M).invariants := by
  cases nonempty_fintype G
  obtain ⟨c, hc⟩ := exists_sum_smul_eq_one G A h
  obtain ⟨n, v, f, hv, hf, hfv⟩ := exists_invariant_dual_basis hc (span_fixed_eq_top h hM)
  exact descent_of_invariant_dual_basis B v f hv hf hfv
end GlobalTheory.FreeQuotient
