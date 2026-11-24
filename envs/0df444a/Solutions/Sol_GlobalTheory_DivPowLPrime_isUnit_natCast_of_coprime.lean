-- Prove2me | solution 1 for GlobalTheory.DivPowLPrime.isUnit_natCast_of_coprime
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T14:24:53.15751+00:00
-- url     : https://prove2.me/submissions/6b58d13a-f28a-4e0f-91d8-fd1dc03aa496

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_ConjugateOrderData
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DividedPowersPrimeUnique

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain TensorProduct GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations
open Classical
noncomputable section
open GlobalTheory GlobalTheory.DivPowLPrime
namespace GlobalTheory.DivPowLPrime
theorem _root_.solution {O : Type} [CommRing O] [IsLocalRing O] {l c : ℕ}
    (hl : (l : O) ∈ IsLocalRing.maximalIdeal O) (hc : Nat.Coprime l c) : IsUnit (c : O) := by
  obtain ⟨a, b, hab⟩ := Nat.isCoprime_iff_coprime.2 hc
  by_contra hu
  have hm : (c : O) ∈ IsLocalRing.maximalIdeal O := (IsLocalRing.mem_maximalIdeal _).2 hu
  have h1 : (1 : O) ∈ IsLocalRing.maximalIdeal O := by
    have h := congrArg (Int.cast : ℤ → O) hab
    push_cast at h
    rw [← h]
    exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hl) (Ideal.mul_mem_left _ _ hm)
  exact (IsLocalRing.maximalIdeal.isMaximal O).ne_top ((Ideal.eq_top_iff_one _).2 h1)
end GlobalTheory.DivPowLPrime
