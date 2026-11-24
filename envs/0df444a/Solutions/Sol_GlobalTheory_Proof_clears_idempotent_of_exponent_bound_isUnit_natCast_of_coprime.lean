-- Prove2me | solution 1 for GlobalTheory.Proof.clears_idempotent_of_exponent_bound.isUnit_natCast_of_coprime
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T19:38:46.484152+00:00
-- url     : https://prove2.me/submissions/681f3ca6-209d-4bb7-98b5-09152887487e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_ConjugateOrderData
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ClearsIdempotentOfExponentBound
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
open GlobalTheory GlobalTheory.Proof GlobalTheory.Proof.clears_idempotent_of_exponent_bound
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
namespace GlobalTheory.Proof.clears_idempotent_of_exponent_bound
theorem _root_.solution {O : Type} [CommRing O] [IsLocalRing O] {m l : ℕ} (h : m.Coprime l)
    (hl : (l : O) ∈ IsLocalRing.maximalIdeal O) : IsUnit (m : O) := by
  have hc : IsCoprime (m : O) (l : O) := by
    have := (Nat.isCoprime_iff_coprime.2 h).map (Int.castRingHom O)
    simpa using this
  by_contra hm
  obtain ⟨u, w, huw⟩ := hc
  have hm' : (m : O) ∈ IsLocalRing.maximalIdeal O := (IsLocalRing.mem_maximalIdeal _).2 hm
  have : (1 : O) ∈ IsLocalRing.maximalIdeal O := by
    rw [← huw]
    exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hm') (Ideal.mul_mem_left _ _ hl)
  exact (IsLocalRing.maximalIdeal.isMaximal O).ne_top ((Ideal.eq_top_iff_one _).2 this)
end GlobalTheory.Proof.clears_idempotent_of_exponent_bound
