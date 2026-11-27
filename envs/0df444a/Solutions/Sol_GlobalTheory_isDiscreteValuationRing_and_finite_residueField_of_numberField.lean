-- Prove2me | solution 1 for GlobalTheory.isDiscreteValuationRing_and_finite_residueField_of_numberField
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T04:38:44.077545+00:00
-- url     : https://prove2.me/submissions/5a0fa3ff-92f1-4d91-8822-ebefa6d15561

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_RangeAlgebraMapEqIInfDiscreteValuationSubring
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_IsDiscreteValuationRingAndFiniteResidueFieldValu
import Theorems.Thm_GlobalTheory_isDiscreteValuationRing_and_finite_residueField_valuationSubringAtPrime
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open IsLocalRing NumberField IsDedekindDomain
namespace GlobalTheory
open IsLocalRing IsDedekindDomain NumberField in
private theorem eq_of_le_of_mem_nonunits_of_dvr {K : Type*} [Field K]
    (A W : ValuationSubring K) (h : A ≤ W) [IsDiscreteValuationRing A]
    (a : A) (ha0 : a ≠ 0) (haW : (a : K) ∈ W.nonunits) : A = W := by
  have hmem : ∀ (B : ValuationSubring K) (hB : A ≤ B) (x : A),
      x ∈ A.idealOfLE B hB ↔ (x : K) ∈ B.nonunits := by
    intro B hB x
    rw [ValuationSubring.mem_nonunits_iff]
    unfold ValuationSubring.idealOfLE
    rw [Ideal.mem_comap, ValuationSubring.valuation_lt_one_iff]
    rfl
  have hmax : ∀ (B : ValuationSubring K) (hB : A ≤ B), (a : K) ∈ B.nonunits →
      A.idealOfLE B hB = maximalIdeal A := by
    intro B hB haB
    have hne : A.idealOfLE B hB ≠ ⊥ := by
      intro hbot
      have : a ∈ A.idealOfLE B hB := (hmem B hB a).2 haB
      rw [hbot, Ideal.mem_bot] at this
      exact ha0 this
    have := (inferInstance : (A.idealOfLE B hB).IsPrime).isMaximal hne
    exact IsLocalRing.eq_maximalIdeal this
  have haA : (a : K) ∈ A.nonunits := (ValuationSubring.nonunits_le_nonunits.2 h) haW
  have hcongr : ∀ (P Q : Ideal A) [P.IsPrime] [Q.IsPrime], P = Q → A.ofPrime P = A.ofPrime Q := by
    rintro P Q _ _ rfl; rfl
  calc A = A.ofPrime (A.idealOfLE A le_rfl) := (A.ofPrime_idealOfLE A le_rfl).symm
    _ = A.ofPrime (A.idealOfLE W h) := hcongr _ _ ((hmax A le_rfl haA).trans (hmax W h haW).symm)
    _ = W := A.ofPrime_idealOfLE W h
end GlobalTheory
end

set_option autoImplicit false
open IsLocalRing NumberField IsDedekindDomain
open GlobalTheory
open IsLocalRing IsDedekindDomain NumberField
namespace GlobalTheory
namespace _root_.GlobalTheory
theorem _root_.solution {L : Type*} [Field L]
    [NumberField L] (W : ValuationSubring L) {n : ℕ} (hn : n ≠ (0 : ℕ))
    (hW : (↑n : L) ∈ W.nonunits) :
      IsDiscreteValuationRing ↥W ∧ Finite (IsLocalRing.ResidueField ↥W) := by
  have hnW := hW
  have hint : ∀ x : 𝓞 L, algebraMap (𝓞 L) L x ∈ W := by
    intro x
    have h : IsIntegral W (x : L) := (RingOfIntegers.isIntegral_coe x).tower_top
    obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.mp h
    show (x : L) ∈ W
    rw [← hy]; exact y.2
  let f : 𝓞 L →+* W := (algebraMap (𝓞 L) L).codRestrict W hint
  have hf : ∀ x : 𝓞 L, ((f x : W) : L) = (x : L) := fun x => rfl
  let P : Ideal (𝓞 L) := (maximalIdeal W).comap f
  have hPmem : ∀ x : 𝓞 L, x ∈ P ↔ (x : L) ∈ W.nonunits := by
    intro x
    rw [Ideal.mem_comap, ValuationSubring.valuation_lt_one_iff, ValuationSubring.mem_nonunits_iff, hf]
  have hnP : (n : 𝓞 L) ∈ P := by
    rw [hPmem]; simpa using hnW
  have hPne : P ≠ ⊥ := by
    intro hbot
    rw [hbot, Ideal.mem_bot] at hnP
    exact hn (by exact_mod_cast hnP)
  let v : HeightOneSpectrum (𝓞 L) := ⟨P, Ideal.comap_isPrime f (maximalIdeal W), hPne⟩
  have hfin : Finite (𝓞 L ⧸ v.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ hPne
  let A := HeightOneSpectrum.valuationSubringAtPrime L v
  have hAW : A ≤ W := by
    intro x hx
    let S := Localization.subalgebra.ofField L _ v.asIdeal.primeCompl_le_nonZeroDivisors
    haveI : IsLocalization.AtPrime S v.asIdeal := Localization.subalgebra.isLocalization_ofField L _ _
    obtain ⟨⟨a, s⟩, hy⟩ := IsLocalization.mk'_surjective v.asIdeal.primeCompl (⟨x, hx⟩ : S)
    have hspec := congrArg Subtype.val (IsLocalization.mk'_spec S a s)
    simp only at hy
    rw [hy] at hspec
    change x * ((s : 𝓞 L) : L) = (a : L) at hspec
    have hsu : IsUnit (f s) := by
      by_contra hns
      exact s.2 (show (s : 𝓞 L) ∈ P from (IsLocalRing.mem_maximalIdeal _).2 hns)
    obtain ⟨t, ht⟩ := hsu.exists_right_inv
    have h1 : ((s : 𝓞 L) : L) * (t : L) = 1 := by
      rw [← hf]; exact congrArg Subtype.val ht
    have hx' : x = (a : L) * (t : L) := by
      calc x = x * (((s : 𝓞 L) : L) * (t : L)) := by rw [h1, mul_one]
        _ = (a : L) * (t : L) := by rw [← mul_assoc, hspec]
    rw [hx']
    exact mul_mem (hint a) t.2
  obtain ⟨hD, hF⟩ :=
    _root_.GlobalTheory.isDiscreteValuationRing_and_finite_residueField_valuationSubringAtPrime L v hfin
  have hnA : (n : L) ∈ A := natCast_mem A n
  have heq : A = W := eq_of_le_of_mem_nonunits_of_dvr A W hAW ⟨(n : L), hnA⟩
    (by
      intro h0
      have := congrArg Subtype.val h0
      simp only [ZeroMemClass.coe_zero] at this
      exact hn (by exact_mod_cast this)) hnW
  rw [← heq]
  exact ⟨hD, hF⟩
end _root_.GlobalTheory
end GlobalTheory
