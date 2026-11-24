-- Prove2me | solution 1 for GlobalTheory.bijective_toSpanSingleton_invariants
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:24:39.913993+00:00
-- url     : https://prove2.me/submissions/dcedc492-d720-405b-ba6b-bd073ce1fc5c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsUnitSmulEqOfBijectiveToSpanSingleton
import Theorems.Thm_GlobalTheory_forall_smul_eq_iff_of_invariant_generator

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
    Function.Bijective (LinearMap.toSpanSingleton B
      (Representation.ofDistribMulAction B G M).invariants ⟨n, hn'⟩) := by
  constructor
  · intro a b hab
    apply FaithfulSMul.algebraMap_injective B A
    apply hn.1
    simpa using congrArg Subtype.val hab
  · rintro ⟨y, hy⟩
    obtain ⟨a, ha, rfl⟩ := (forall_smul_eq_iff_of_invariant_generator hn hn' y).mp hy
    obtain ⟨b, rfl⟩ := Algebra.IsInvariant.isInvariant (A := B) (G := G) a ha
    exact ⟨b, Subtype.ext (by simp)⟩
end GlobalTheory
