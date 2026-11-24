-- Prove2me | solution 1 for GlobalTheory.QNorm.two_pow_card_le_index_iInf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T19:43:51.231735+00:00
-- url     : https://prove2.me/submissions/48c7763b-c0fd-4b1b-b96e-cca2a966b934

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_SqSubLeNormSub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_TwoPowCardLeIndexIInf

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero
open GlobalTheory GlobalTheory.QNorm
namespace GlobalTheory.QNorm
theorem _root_.solution :
    ∀ (G ι : Type) [CommGroup G] [Fintype ι] (K : ι → Subgroup G),
      (∀ i, ∃ x, x ∉ K i ∧ ∀ j, j ≠ i → x ∈ K j) → (⨅ i, K i).index ≠ 0 →
        2 ^ Fintype.card ι ≤ (⨅ i, K i).index := by
  intro G ι _ _ K h hidx
  classical
  choose x hx hx' using h
  have key : ∀ (A : Finset ι) (j : ι), (∏ i ∈ A, x i) ∈ K j ↔ j ∉ A := by
    intro A j
    constructor
    · intro hm hj
      rw [← Finset.mul_prod_erase A x hj] at hm
      have h2 : (∏ i ∈ A.erase j, x i) ∈ K j :=
        Subgroup.prod_mem _ fun i hi => hx' i j (Finset.ne_of_mem_erase hi).symm
      exact hx j ((Subgroup.mul_mem_cancel_right _ h2).1 hm)
    · intro hj
      exact Subgroup.prod_mem _ fun i hi => hx' i j (fun e => hj (e ▸ hi))
  haveI : Finite (G ⧸ ⨅ i, K i) := Nat.finite_of_card_ne_zero hidx
  have inj : Function.Injective
      (fun A : Finset ι => ((∏ i ∈ A, x i : G) : G ⧸ ⨅ i, K i)) := by
    intro A B hAB
    have hm : (∏ i ∈ A, x i)⁻¹ * (∏ i ∈ B, x i) ∈ ⨅ i, K i := QuotientGroup.eq.1 hAB
    ext j
    have hj : (∏ i ∈ A, x i)⁻¹ * (∏ i ∈ B, x i) ∈ K j := (Subgroup.mem_iInf.1 hm) j
    have hiff : (∏ i ∈ A, x i) ∈ K j ↔ (∏ i ∈ B, x i) ∈ K j := by
      constructor
      · intro ha
        exact (Subgroup.mul_mem_cancel_left _ (inv_mem ha)).1 hj
      · intro hb
        exact inv_mem_iff.1 ((Subgroup.mul_mem_cancel_right _ hb).1 hj)
    rw [key, key] at hiff
    exact not_iff_not.1 hiff
  have := Nat.card_le_card_of_injective _ inj
  rwa [Nat.card_eq_fintype_card, Fintype.card_finset] at this
end GlobalTheory.QNorm
