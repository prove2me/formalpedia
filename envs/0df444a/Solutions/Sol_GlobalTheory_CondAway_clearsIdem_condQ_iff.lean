-- Prove2me | solution 1 for GlobalTheory.CondAway.clearsIdem_condQ_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T14:18:07.493998+00:00
-- url     : https://prove2.me/submissions/e6d28c47-0bf9-41be-8b7c-44e9b804dd5a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_ConjugateOrderData
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ClearsIdempotentConductorIff
import Theorems.Thm_GlobalTheory_CondAway_isUnit_absNorm_of_not_mem
import Theorems.Thm_GlobalTheory_CondAway_coordAt_rTensor
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
noncomputable section
open GlobalTheory GlobalTheory.CondAway
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
namespace GlobalTheory.CondAway
theorem _root_.solution : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (𝔣 : Ideal (OF E))
    (Q : Finset (HeightOneSpectrum (OF E))) (l : ℕ), l.Prime → (∀ q ∈ Q, (l : OF E) ∉ q.asIdeal) →
    ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] (K : Type) [Field K] [Algebra O K]
    [IsFractionRing O K], (l : O) ∈ IsLocalRing.maximalIdeal O → ∀ D : O,
    ClearsIdem K (condQ 𝔣 Q) D ↔ ClearsIdem K 𝔣 D := by
  intro E _ _ _ 𝔣 Q l hl hQ O _ _ _ _ K _ _ _ hlO D
  have hle : condQ 𝔣 Q ≤ 𝔣 := Ideal.mul_le_inf.trans inf_le_left
  constructor
  · intro h σ
    obtain ⟨t, ht⟩ := h σ
    let g : orderC (condQ 𝔣 Q) →ₗ[ℤ] orderC 𝔣 := AddMonoidHom.toIntLinearMap
      { toFun := fun x => ⟨(1 : E) * x, by rw [one_mul]; exact orderC_mono hle x.2⟩,
        map_zero' := Subtype.ext (by simp), map_add' := fun x y => Subtype.ext (by simp [mul_add]) }
    refine ⟨g.rTensor O t, fun σ' => ?_⟩
    rw [coordAt_rTensor O (1 : E) g (fun x => rfl), map_one, one_mul, ht]
  · intro h σ
    obtain ⟨t, ht⟩ := h σ
    set m : ℕ := ∏ q ∈ Q, Ideal.absNorm q.asIdeal with hm
    have hmI : (m : OF E) ∈ ∏ q ∈ Q, q.asIdeal := by
      rw [hm, Nat.cast_prod]
      exact Ideal.prod_mem_prod fun q _ => Ideal.absNorm_mem q.asIdeal
    have hmul : ∀ x ∈ orderC 𝔣, (m : E) * x ∈ orderC (condQ 𝔣 Q) := by
      intro x hx
      obtain ⟨a, b, hb, rfl⟩ := mem_orderC.1 hx
      refine mem_orderC.2 ⟨m * a, b * algebraMap (OF E) (𝓞 E) m, ?_, ?_⟩
      · rw [condQ, Ideal.map_mul]
        exact Ideal.mul_mem_mul hb (Ideal.mem_map_of_mem _ hmI)
      · simp only [map_mul, map_natCast]
        ring
    let g : orderC 𝔣 →ₗ[ℤ] orderC (condQ 𝔣 Q) := AddMonoidHom.toIntLinearMap
      { toFun := fun x => ⟨(m : E) * x, hmul x x.2⟩,
        map_zero' := Subtype.ext (by simp), map_add' := fun x y => Subtype.ext (by simp [mul_add]) }
    have hu : IsUnit (m : O) := by
      rw [hm, Nat.cast_prod]
      exact Finset.prod_induction _ IsUnit (fun a b ha hb => ha.mul hb) isUnit_one
        (fun q hq => isUnit_absNorm_of_not_mem q l hl (hQ q hq) O hlO)
    obtain ⟨u, hu'⟩ := hu.exists_left_inv
    refine ⟨g.rTensor O t * (1 ⊗ₜ u), fun σ' => ?_⟩
    rw [map_mul, coordAt_rTensor O (m : E) g (fun x => rfl), ht]
    have h1 : coordAt O (condQ 𝔣 Q) σ' (1 ⊗ₜ u) = algebraMap O K u := by
      show σ' ((1 : orderC (condQ 𝔣 Q)) : E) * algebraMap O K u = _
      simp
    have h2 : algebraMap O K u * (m : K) = 1 := by
      rw [← map_natCast (algebraMap O K), ← map_mul, hu', map_one]
    rw [h1, map_natCast]
    split_ifs
    · linear_combination (algebraMap O K D) * h2
    · simp
end GlobalTheory.CondAway
