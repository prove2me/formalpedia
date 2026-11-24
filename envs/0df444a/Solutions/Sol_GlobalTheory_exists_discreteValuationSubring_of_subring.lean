-- Prove2me | solution 1 for GlobalTheory.exists_discreteValuationSubring_of_subring
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:27:11.858584+00:00
-- url     : https://prove2.me/submissions/963859d7-bd45-41c6-a188-3148ed75150e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_RangeAlgebraMapEqIInfDiscreteValuationSubring
import Theorems.Thm_GlobalTheory_krullAkizuki_of_birational

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
open GlobalTheory
variable {L : Type*} [Field L]
namespace GlobalTheory
theorem _root_.solution (B : Subring L) [IsNoetherianRing B]
    (hB : ∀ z : L, ∃ c ∈ B, c ≠ 0 ∧ c * z ∈ B) {y : L} (hy : y ∈ B) (hy0 : y ≠ 0)
    (hy1 : y⁻¹ ∉ B) :
    ∃ V : ValuationSubring L, IsDiscreteValuationRing V ∧ B ≤ V.toSubring ∧ y ∈ V.nonunits := by
  set y' : B := ⟨y, hy⟩ with hy'
  have hyu : ¬ IsUnit y' := by
    intro h
    obtain ⟨z, hz⟩ := h.exists_right_inv
    have hz' : y * (z : L) = 1 := congrArg Subtype.val hz
    apply hy1
    rw [← eq_inv_of_mul_eq_one_right hz']
    exact z.2
  have hspan : Ideal.span {y'} ≠ ⊤ := by
    rwa [Ne, Ideal.span_singleton_eq_top]
  obtain ⟨p, hp⟩ : Nonempty (Ideal.span {y'}).minimalPrimes := Ideal.nonempty_minimalPrimes hspan
  haveI hpp : p.IsPrime := hp.1.1
  have hyp : y' ∈ p := hp.1.2 (Ideal.mem_span_singleton_self y')
  have hht : p.height ≤ 1 := Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes _ p hp
  set A0 := (LocalSubring.ofPrime B p).toSubring with hA0
  haveI : IsNoetherianRing A0 := IsLocalization.isNoetherianRing p.primeCompl A0 inferInstance
  haveI : Ring.KrullDimLE 1 A0 := by
    rw [Ring.krullDimLE_iff, IsLocalization.AtPrime.ringKrullDim_eq_height p A0]
    exact_mod_cast hht
  haveI : Ring.DimensionLEOne A0 := ⟨fun hq hq' => Ideal.IsPrime.isMaximal_of_ne_bot hq' hq⟩
  set y'' : A0 := algebraMap B A0 y' with hy''
  have hy''m : y'' ∈ IsLocalRing.maximalIdeal A0 := by
    rw [← IsLocalization.AtPrime.map_eq_maximalIdeal p A0]
    exact Ideal.mem_map_of_mem _ hyp
  have hspan2 : Ideal.span {y''} ≠ ⊤ := by
    rw [Ne, Ideal.span_singleton_eq_top]
    exact (IsLocalRing.mem_maximalIdeal _).mp hy''m
  obtain ⟨V, hAV, hVy⟩ := Ideal.image_subset_nonunits_valuationSubring _ hspan2
  have hyV : y ∈ V.nonunits := hVy ⟨y'', Ideal.mem_span_singleton_self _, rfl⟩
  have hBV : B ≤ V.toSubring := (LocalSubring.le_ofPrime B p).trans hAV
  letI : Algebra A0 V := (Subring.inclusion hAV).toAlgebra
  haveI : FaithfulSMul A0 V := (faithfulSMul_iff_algebraMap_injective A0 V).mpr
    fun a b h => Subtype.ext (show (a : L) = b from congrArg (fun v : V => (v : L)) h)
  have hbir : ∀ x : V, ∃ c : A0, c ≠ 0 ∧ ∃ b : A0, algebraMap A0 V c * x = algebraMap A0 V b := by
    intro x
    obtain ⟨c, hc, hc0, hcx⟩ := hB x
    refine ⟨⟨c, LocalSubring.le_ofPrime B p hc⟩, fun h => hc0 (congrArg Subtype.val h),
      ⟨c * x, LocalSubring.le_ofPrime B p hcx⟩, Subtype.ext rfl⟩
  have hKA := krullAkizuki_of_birational (A := A0) (B := V) hbir
  haveI : IsNoetherianRing V := hKA.1
  haveI : IsPrincipalIdealRing V := ((IsBezout.TFAE (R := V)).out 0 1).mp hKA.1
  have hVy0 : y ∈ V := hBV hy
  have hne : IsLocalRing.maximalIdeal V ≠ ⊥ := by
    intro h
    have hm : (⟨y, hVy0⟩ : V) ∈ IsLocalRing.maximalIdeal V :=
      (ValuationSubring.valuation_lt_one_iff V _).mpr ((ValuationSubring.mem_nonunits_iff V).mp hyV)
    rw [h, Ideal.mem_bot] at hm
    exact hy0 (congrArg Subtype.val hm)
  exact ⟨V, IsDiscreteValuationRing.mk hne, hBV, hyV⟩
end GlobalTheory
