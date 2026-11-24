-- Prove2me | solution 1 for GlobalTheory.Proof.clears_idempotent_of_exponent_bound.clearsIdem_condC
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T20:28:29.102156+00:00
-- url     : https://prove2.me/submissions/8baf52f3-3763-46ab-8546-a202ed7b0fb3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_ConjugateOrderData
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ClearsIdempotentOfExponentBound
import Theorems.Thm_GlobalTheory_Proof_clears_idempotent_of_exponent_bound_exists_coprime_mul_pow_mem
import Theorems.Thm_GlobalTheory_Proof_clears_idempotent_of_exponent_bound_isUnit_natCast_of_coprime
import Theorems.Thm_GlobalTheory_Proof_clears_idempotent_of_exponent_bound_coordAt_map
import Theorems.Thm_GlobalTheory_CMVal_coe_latticeSub
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.CMVal.coe_latticeSub



set_option autoImplicit false
open NumberField IsDedekindDomain TensorProduct GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations
open Classical
open GlobalTheory.Proof.clears_idempotent_of_exponent_bound
namespace GlobalTheory.Proof.clears_idempotent_of_exponent_bound
theorem _root_.solution :
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (𝔣 : Ideal (OF E)), 𝔣 ≠ ⊥ → ∀ (l : ℕ), l.Prime → ∀ k : ℕ, (∀ v : HeightOneSpectrum (OF E), (l : OF E) ∈ v.asIdeal → expIn 𝔣 v ≤ k) → ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] (K : Type) [Field K] [Algebra O K] [IsFractionRing O K], (l : O) ∈ IsLocalRing.maximalIdeal O → ∀ D : O, ClearsIdem K (⊤ : Ideal (OF E)) D → ClearsIdem K 𝔣 ((l : O) ^ k * D) := by
  intro E _ _ _ 𝔣 h𝔣 l hl k hk O _ _ _ _ K _ _ _ hlO D hD σ
  obtain ⟨m, hm, hmem⟩ := exists_coprime_mul_pow_mem h𝔣 hl hk
  obtain ⟨u, hu⟩ := isUnit_natCast_of_coprime (O := O) hm hlO
  obtain ⟨t, ht⟩ := hD σ
  refine ⟨TensorProduct.map (mulMap hmem) (LinearMap.mulLeft ℤ ((u⁻¹ : Oˣ) : O)) t, fun σ' => ?_⟩
  rw [coordAt_map, ht]
  have hw : algebraMap O K (m : O) * algebraMap O K ((u⁻¹ : Oˣ) : O) = 1 := by
    rw [← map_mul, ← hu, Units.mul_inv, map_one]
  simp only [map_mul, map_pow, map_natCast] at hw ⊢
  split_ifs
  · linear_combination ((l : K) ^ k * algebraMap O K D) * hw
  · simp
end GlobalTheory.Proof.clears_idempotent_of_exponent_bound
