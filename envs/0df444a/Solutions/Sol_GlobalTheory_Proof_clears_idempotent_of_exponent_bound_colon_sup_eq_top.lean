-- Prove2me | solution 1 for GlobalTheory.Proof.clears_idempotent_of_exponent_bound.colon_sup_eq_top
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T19:53:03.229889+00:00
-- url     : https://prove2.me/submissions/bda00d6f-88ad-4007-bbd6-7df4f000189f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_ConjugateOrderData
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ClearsIdempotentOfExponentBound
import Theorems.Thm_GlobalTheory_Proof_clears_idempotent_of_exponent_bound_exists_not_mem_mul_pow_mem

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
theorem _root_.solution {𝔣 : Ideal (OF E)} (h𝔣 : 𝔣 ≠ ⊥) {l : ℕ} (hl : l ≠ 0) {k : ℕ}
    (hk : ∀ v : HeightOneSpectrum (OF E), (l : OF E) ∈ v.asIdeal → expIn 𝔣 v ≤ k) :
    𝔣.colon {((l : OF E) ^ k)} ⊔ Ideal.span {(l : OF E)} = ⊤ := by
  by_contra hne
  obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ hne
  have hMb : M ≠ ⊥ := Ideal.IsMaximal.ne_bot_of_isIntegral_int M
  let v : HeightOneSpectrum (OF E) := ⟨M, hM.isPrime, hMb⟩
  have hlv : (l : OF E) ∈ v.asIdeal := hle (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))
  obtain ⟨x, hxv, hx⟩ := exists_not_mem_mul_pow_mem h𝔣 v hlv (hk v hlv)
  apply hxv
  apply hle
  apply Ideal.mem_sup_left
  rw [Submodule.mem_colon_singleton, smul_eq_mul]
  exact hx
end GlobalTheory.Proof.clears_idempotent_of_exponent_bound
