-- Prove2me | solution 1 for GlobalTheory.TorsionFreeDividedPowers.exists_factorial_mul_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T21:39:04.422994+00:00
-- url     : https://prove2.me/submissions/5524cfed-5642-46c1-9549-d33d5291415b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_ConjugateOrderData
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsDividedPowersPrime
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
open GlobalTheory GlobalTheory.TorsionFreeDividedPowers
open DividedPowers
namespace GlobalTheory.TorsionFreeDividedPowers
theorem _root_.solution (l : ℕ) (hl : l.Prime) {O : Type} [CommRing O] [IsLocalRing O]
    (hlm : (l : O) ∈ IsLocalRing.maximalIdeal O) (n : ℕ) (hn : n ≠ 0) :
    ∃ q : O, (n.factorial : O) * q = (l : O) ^ (n - 1) := by
  haveI := Fact.mk hl
  have hN : n.factorial ≠ 0 := Nat.factorial_ne_zero n
  have hfac := Nat.ordProj_mul_ordCompl_eq_self n.factorial l
  have hcop := Nat.coprime_ordCompl hl hN
  have hv : n.factorial.factorization l < n := by
    rw [Nat.factorization_def _ hl]
    exact padicValNat_factorial_lt_of_ne_zero l hn
  set v := n.factorial.factorization l
  set u := n.factorial / l ^ v
  have hu : IsUnit (u : O) := by
    by_contra hnu
    have hum : (u : O) ∈ IsLocalRing.maximalIdeal O := (IsLocalRing.mem_maximalIdeal _).mpr hnu
    obtain ⟨a, b, hab⟩ := (Nat.isCoprime_iff_coprime.mpr hcop).map (Int.castRingHom O)
    simp only [eq_intCast, Int.cast_natCast] at hab
    have h1 : (1 : O) ∈ IsLocalRing.maximalIdeal O := by
      rw [← hab]
      exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hlm) (Ideal.mul_mem_left _ _ hum)
    exact (IsLocalRing.maximalIdeal.isMaximal O).ne_top ((Ideal.eq_top_iff_one _).mpr h1)
  obtain ⟨w, hw⟩ := hu
  refine ⟨(↑w⁻¹ : O) * (l : O) ^ (n - 1 - v), ?_⟩
  rw [← hfac]
  push_cast
  have e : (l : O) ^ v * (u : O) * ((↑w⁻¹ : O) * (l : O) ^ (n - 1 - v))
      = (l : O) ^ v * (l : O) ^ (n - 1 - v) * ((u : O) * ↑w⁻¹) := by ring
  rw [e, ← hw, Units.mul_inv, mul_one, ← pow_add, Nat.add_sub_cancel' (by omega)]
end GlobalTheory.TorsionFreeDividedPowers
