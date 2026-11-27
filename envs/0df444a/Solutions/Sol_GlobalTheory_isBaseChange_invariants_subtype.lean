-- Prove2me | solution 1 for GlobalTheory.isBaseChange_invariants_subtype
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T04:41:26.632065+00:00
-- url     : https://prove2.me/submissions/6edd9535-d660-4842-bb1f-98a37477a8d4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsUnitSmulEqOfBijectiveToSpanSingleton
import Theorems.Thm_GlobalTheory_bijective_toSpanSingleton_invariants

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct Pointwise
open GlobalTheory
variable {G : Type*} [Group G] (A : Type*) [CommRing A] [MulSemiringAction G A]
variable (M : Type*) [AddCommGroup M] [Module A M] [DistribMulAction G M] [SMulDistribClass G A M]
variable {A M}
variable (B : Type*) [CommRing B] [Algebra B A] [FaithfulSMul B A] [SMulCommClass G B A]
  [Algebra.IsInvariant B A G] [Module B M] [IsScalarTower B A M] [SMulCommClass G B M]
namespace GlobalTheory
theorem _root_.solution {n : M}
    (hn : Function.Bijective (LinearMap.toSpanSingleton A M n)) (hn' : ∀ g : G, g • n = n) :
    IsBaseChange A (Representation.ofDistribMulAction B G M).invariants.subtype := by
  refine (IsBaseChange.iff_of_equiv_comm (f := Algebra.linearMap B A)
    (LinearEquiv.ofBijective _ (bijective_toSpanSingleton_invariants B hn hn'))
    (LinearEquiv.ofBijective _ hn) ?_).mp (IsBaseChange.linearMap B A)
  ext
  simp
end GlobalTheory
