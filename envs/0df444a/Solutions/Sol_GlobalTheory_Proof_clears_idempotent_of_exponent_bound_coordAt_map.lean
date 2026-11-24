-- Prove2me | solution 1 for GlobalTheory.Proof.clears_idempotent_of_exponent_bound.coordAt_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T19:38:44.695029+00:00
-- url     : https://prove2.me/submissions/c6d4dc3e-b611-4ae9-9b2f-8f673805ca7f

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
theorem _root_.solution {𝔣 : Ideal (OF E)} {c : OF E} (hc : c ∈ 𝔣) {O : Type} [CommRing O] {K : Type} [Field K]
    [Algebra O K] (w : O) (σ : E →+* K) (t : orderC (⊤ : Ideal (OF E)) ⊗[ℤ] O) :
    coordAt O 𝔣 σ (TensorProduct.map (mulMap hc) (LinearMap.mulLeft ℤ w) t) =
      σ (algebraMap (OF E) E c) * algebraMap O K w * coordAt O ⊤ σ t := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul x y =>
    simp only [TensorProduct.map_tmul, LinearMap.mulLeft_apply]
    change σ (algebraMap (OF E) E c * x) * algebraMap O K (w * y) = _ * (σ x * algebraMap O K y)
    rw [map_mul, map_mul]; ring
  | add s t hs ht => rw [map_add, map_add, hs, ht, map_add, mul_add]
end GlobalTheory.Proof.clears_idempotent_of_exponent_bound
