-- Prove2me | solution 1 for GlobalTheory.Proof.clears_idempotent_of_exponent_bound.exists_not_mem_mul_pow_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T19:38:45.571389+00:00
-- url     : https://prove2.me/submissions/48c71c9c-c048-4455-9787-e41169b519f2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_ConjugateOrderData
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ClearsIdempotentOfExponentBound

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
open GlobalTheory GlobalTheory.Proof GlobalTheory.Proof.clears_idempotent_of_exponent_bound
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
namespace GlobalTheory.Proof.clears_idempotent_of_exponent_bound
theorem _root_.solution {𝔣 : Ideal (OF E)} (h𝔣 : 𝔣 ≠ ⊥) (v : HeightOneSpectrum (OF E)) {c : OF E}
    (hc : c ∈ v.asIdeal) {k : ℕ} (hk : expIn 𝔣 v ≤ k) : ∃ x : OF E, x ∉ v.asIdeal ∧ x * c ^ k ∈ 𝔣 := by
  set e := multiplicity v.asIdeal 𝔣 with he
  obtain ⟨𝔤, h𝔤⟩ := pow_multiplicity_dvd v.asIdeal 𝔣
  have hnu : ¬ IsUnit v.asIdeal := by
    rw [Ideal.isUnit_iff]; exact v.isPrime.ne_top
  have hfin : FiniteMultiplicity v.asIdeal 𝔣 := FiniteMultiplicity.of_not_isUnit hnu h𝔣
  have hndvd : ¬ v.asIdeal ∣ 𝔤 := by
    rintro ⟨𝔥, rfl⟩
    apply hfin.not_pow_dvd_of_multiplicity_lt (Nat.lt_succ_self e)
    exact ⟨𝔥, by rw [h𝔤, pow_succ, mul_assoc]⟩
  rw [Ideal.dvd_iff_le, SetLike.not_le_iff_exists] at hndvd
  obtain ⟨x, hx𝔤, hxv⟩ := hndvd
  refine ⟨x, hxv, ?_⟩
  rw [h𝔤, mul_comm x]
  refine Ideal.mul_mem_mul ?_ hx𝔤
  exact Ideal.pow_le_pow_right hk (Ideal.pow_mem_pow hc k)
end GlobalTheory.Proof.clears_idempotent_of_exponent_bound
