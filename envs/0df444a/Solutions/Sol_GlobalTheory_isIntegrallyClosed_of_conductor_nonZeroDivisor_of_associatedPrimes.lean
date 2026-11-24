-- Prove2me | solution 1 for GlobalTheory.isIntegrallyClosed_of_conductor_nonZeroDivisor_of_associatedPrimes
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:03:38.27523+00:00
-- url     : https://prove2.me/submissions/083d366a-3a38-4564-b55b-bfad6d96ffa4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsBasicOpenEqZeroOfMemIInfPowSmul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_IsIntegrallyClosedOfConductorNonZeroDivisorOfAss
import Theorems.Thm_GlobalTheory_eq_zero_of_forall_associatedPrimes_exists_smul_eq_zero


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
namespace GlobalTheory
theorem _root_.solution
    (R : Type) [CommRing R] [IsNoetherianRing R] (x : R) (hx : x ∈ nonZeroDivisors R)
    (hloc : ∀ (P : Ideal R) [P.IsPrime], P ∈ associatedPrimes R (R ⧸ Ideal.span {x}) →
      ∃ _ : IsDomain (Localization.AtPrime P), IsIntegrallyClosed (Localization.AtPrime P))
    (hcond : ∀ c : FractionRing R, IsIntegral R c →
      ∃ s : R, algebraMap R (FractionRing R) s = algebraMap R (FractionRing R) x * c) :
    IsIntegrallyClosed R := by
  rw [isIntegrallyClosed_iff (FractionRing R)]
  intro c hc
  obtain ⟨s, hs⟩ := hcond c hc

  suffices hmem : Ideal.Quotient.mk (Ideal.span {x}) s = 0 by
    rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton'] at hmem
    obtain ⟨w, rfl⟩ := hmem
    refine ⟨w, ?_⟩
    have hu : IsUnit (algebraMap R (FractionRing R) x) :=
      IsLocalization.map_units (FractionRing R) ⟨x, hx⟩
    apply hu.mul_left_cancel
    rw [← hs, map_mul, mul_comm]
  have key := eq_zero_of_forall_associatedPrimes_exists_smul_eq_zero
    (A := R) (M := R ⧸ Ideal.span {x}) (x := Ideal.Quotient.mk (Ideal.span {x}) s)
  apply key
  intro P hP
  haveI hPp : P.IsPrime := hP.isPrime
  obtain ⟨hdom, hic⟩ := hloc P hP
  let RP := Localization.AtPrime P
  let K := FractionRing RP

  have hreg : ∀ b ∈ nonZeroDivisors R, IsUnit (algebraMap R K b) := by
    intro b hb
    rw [IsScalarTower.algebraMap_apply R RP K]
    refine IsLocalization.map_units K (⟨algebraMap R RP b, ?_⟩ : nonZeroDivisors RP)
    refine mem_nonZeroDivisors_of_ne_zero fun h0 ↦ ?_
    obtain ⟨t, ht⟩ := (IsLocalization.map_eq_zero_iff P.primeCompl RP b).1 h0
    have : (t : R) = 0 := (mem_nonZeroDivisors_iff_right.1 hb) t ht
    exact t.2 (this ▸ P.zero_mem)
  let φ : FractionRing R →+* K :=
    IsLocalization.lift (M := nonZeroDivisors R) (g := algebraMap R K) fun b ↦ hreg b b.2
  have hφ : ∀ r : R, φ (algebraMap R (FractionRing R) r) = algebraMap RP K (algebraMap R RP r) :=
    fun r ↦ by
      rw [IsLocalization.lift_eq, IsScalarTower.algebraMap_apply R RP K]
  have hint : IsIntegral RP (φ c) := by
    refine IsIntegral.map_of_comp_eq (algebraMap R RP) φ ?_ hc
    ext r
    simp only [RingHom.comp_apply]
    rw [hφ]
  obtain ⟨u, hu⟩ := (isIntegrallyClosed_iff K).1 hic hint
  have hxu : algebraMap R RP x * u = algebraMap R RP s := by
    apply IsFractionRing.injective RP K
    rw [map_mul, hu, ← hφ, ← hφ, hs, map_mul]
  obtain ⟨⟨r, t⟩, hrt⟩ := IsLocalization.surj P.primeCompl u
  have h2 : algebraMap R RP (x * r) = algebraMap R RP (s * t) := by
    simp only at hrt
    rw [map_mul, map_mul, ← hxu, ← hrt]
    ring
  obtain ⟨t', ht'⟩ := (IsLocalization.eq_iff_exists P.primeCompl RP).1 h2
  refine ⟨t' * t, P.primeCompl.mul_mem t'.2 t.2, ?_⟩
  rw [Algebra.smul_def, Ideal.Quotient.algebraMap_eq, ← map_mul, Ideal.Quotient.eq_zero_iff_mem,
    Ideal.mem_span_singleton']
  refine ⟨t' * r, ?_⟩
  linear_combination ht'
end GlobalTheory
