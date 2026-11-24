-- Prove2me | solution 1 for GlobalTheory.DualCrit.clearsIdem_top_of_dual
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T15:27:15.215829+00:00
-- url     : https://prove2.me/submissions/a223ebbb-03cd-40ad-844e-90ce705b77dc

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_ConjugateOrderData
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ClearsIdempotentOfTraceDual
import Theorems.Thm_GlobalTheory_DualCrit_sum_basis_mul_dual
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
open GlobalTheory GlobalTheory.DualCrit
namespace GlobalTheory.DualCrit
theorem _root_.solution : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] (K : Type) [Field K] [Algebra O K] [IsFractionRing O K], Nat.card (E →+* K) = Module.finrank ℚ E → ∀ D : O, (∀ (σ : E →+* K) (y : E), (∀ x : 𝓞 E, ∃ n : ℤ, Algebra.trace ℚ E (y * x) = n) → ∃ z : O, algebraMap O K z = algebraMap O K D * σ y) → ClearsIdem K (⊤ : Ideal (OF E)) D := by
  intro E _ _ _ O _ _ _ _ K _ _ _ hcard D hD σ
  haveI : CharZero K := charZero_of_injective_algebraMap (IsFractionRing.injective O K)
  haveI : Finite (E →+* K) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; exact Module.finrank_pos.ne')
  letI : Fintype (E →+* K) := Fintype.ofFinite _
  have hcard' : Fintype.card (E →+* K) = Module.finrank ℚ E := by
    rw [← Nat.card_eq_fintype_card, hcard]
  set b := RingOfIntegers.basis E
  set bQ := integralBasis E
  set bd := (Algebra.traceForm ℚ E).dualBasis (traceForm_nondegenerate ℚ E) bQ
  have hint : ∀ j (x : 𝓞 E), ∃ n : ℤ, Algebra.trace ℚ E (bd j * x) = n := by
    intro j x
    refine ⟨b.repr x j, ?_⟩
    have h1 : Algebra.trace ℚ E (bd j * x) = bQ.repr (x : E) j := by
      rw [← Algebra.traceForm_apply]
      conv_lhs => rw [← bQ.sum_repr (x : E)]
      rw [map_sum]
      simp only [bd, map_smul, LinearMap.BilinForm.apply_dualBasis_left, smul_eq_mul, mul_ite, mul_one, mul_zero,
        Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rw [h1]
    exact (integralBasis_repr_apply E x j).trans (eq_intCast _ _)
  choose z hz using fun j => hD σ (bd j) (hint j)
  have hmem : ∀ j, ((b j : 𝓞 E) : E) ∈ orderC (⊤ : Ideal (OF E)) := fun j =>
    mem_orderC.2 ⟨0, b j, by rw [Ideal.map_top]; exact Submodule.mem_top, by simp⟩
  refine ⟨∑ j, (⟨((b j : 𝓞 E) : E), hmem j⟩ : orderC (⊤ : Ideal (OF E))) ⊗ₜ[ℤ] z j, fun σ' => ?_⟩
  have hc : ∀ j, coordAt O (⊤ : Ideal (OF E)) σ'
      ((⟨((b j : 𝓞 E) : E), hmem j⟩ : orderC (⊤ : Ideal (OF E))) ⊗ₜ[ℤ] z j) =
        algebraMap O K D * (σ' (bQ j) * σ (bd j)) := by
    intro j
    show σ' ((b j : 𝓞 E) : E) * algebraMap O K (z j) = _
    rw [hz j, integralBasis_apply]
    simp only [b]
    rw [← RingOfIntegers.coe_eq_algebraMap]
    ring
  rw [map_sum, Finset.sum_congr rfl fun j _ => hc j, ← Finset.mul_sum, sum_basis_mul_dual hcard' bQ σ σ']
  split_ifs <;> simp
end GlobalTheory.DualCrit
