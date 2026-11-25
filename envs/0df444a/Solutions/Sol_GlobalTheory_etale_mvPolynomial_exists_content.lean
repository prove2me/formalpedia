-- Prove2me | solution 1 for GlobalTheory.etale_mvPolynomial_exists_content
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:00:25.798138+00:00
-- url     : https://prove2.me/submissions/664be2d1-1b33-4d4b-8548-e0fa32761a7e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_MvPolynomialMapMaximalIdealIsPrime
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ValuationRingOfFlatOfFormallyUnramified
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ValuationRingExistsAssociatedOfSumEqZero
import Theorems.Thm_GlobalTheory_exists_associated_of_isAlgebraic
import Theorems.Thm_GlobalTheory_dvd_of_dvd_mul_of_flat
import Theorems.Thm_GlobalTheory_map_liesOver_of_flat_of_isPrime
import Theorems.Thm_GlobalTheory_gaussLocalization_exists_associated
import Theorems.Thm_GlobalTheory_mvPolynomial_content_valuationRing
import Theorems.Thm_GlobalTheory_valuationRing_of_flat_of_formallyUnramified


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution :
    ∀ (O K : Type) [CommRing O] [IsDomain O] [ValuationRing O] [Ring.DimensionLEOne O] [Field K] [IsAlgClosed K] [Algebra O K] [IsFractionRing O K] (g : ℕ) (B : Type) [CommRing B] [IsDomain B] [Algebra O B] [Algebra (MvPolynomial (Fin g) O) B] [IsScalarTower O (MvPolynomial (Fin g) O) B] [Algebra.Etale (MvPolynomial (Fin g) O) B], ((IsLocalRing.maximalIdeal O).map (algebraMap O B)).IsPrime → ∀ b : B, b ≠ 0 → ∃ (π : O) (b' : B), b = algebraMap O B π * b' ∧ b' ∉ (IsLocalRing.maximalIdeal O).map (algebraMap O B) := by
  intro O K _ _ _ _ _ _ _ _ g B _ _ _ _ _ _ hη b hb
  obtain ⟨hpp, -, hcanc⟩ := mvPolynomial_content_valuationRing O g
  set p := (IsLocalRing.maximalIdeal O).map (MvPolynomial.C : O →+* MvPolynomial (Fin g) O)
    with hp
  have hC : ∀ π : O, algebraMap (MvPolynomial (Fin g) O) B (MvPolynomial.C π)
      = algebraMap O B π := fun π =>
    (IsScalarTower.algebraMap_apply O (MvPolynomial (Fin g) O) B π).symm
  have hηp : (IsLocalRing.maximalIdeal O).map (algebraMap O B)
      = p.map (algebraMap (MvPolynomial (Fin g) O) B) := by
    rw [hp, Ideal.map_map]
    congr 1
    exact RingHom.ext fun π => (hC π).symm
  rw [hηp] at hη ⊢
  set η := p.map (algebraMap (MvPolynomial (Fin g) O) B) with hηdef
  have hlo : η.LiesOver p := map_liesOver_of_flat_of_isPrime p

  have step1 : ∃ (π : O) (s t : B), s ∉ η ∧ t ∉ η ∧ s * b = algebraMap O B π * t := by
    let := Localization.AtPrime.algebraOfLiesOver p η
    have : Algebra.EssFiniteType (Localization.AtPrime p) (Localization.AtPrime η) :=
      .of_comp (MvPolynomial (Fin g) O) _ _
    have : Algebra.FormallyUnramified (Localization.AtPrime p) (Localization.AtPrime η) :=
      .of_restrictScalars (MvPolynomial (Fin g) O) _ _
    have hW := gaussLocalization_exists_associated O g p hp
    have : ValuationRing (Localization.AtPrime p) := by
      refine ValuationRing.iff_dvd_total.2 ⟨fun x y => ?_⟩
      by_cases hx : x = 0
      · right; rw [hx]; exact dvd_zero _
      by_cases hy : y = 0
      · left; rw [hy]; exact dvd_zero _
      obtain ⟨a, ha⟩ := hW x hx
      obtain ⟨c, hc⟩ := hW y hy
      rcases ValuationRing.dvd_total a c with h | h
      · left; exact (ha.dvd.trans (map_dvd _ (map_dvd _ h))).trans hc.symm.dvd
      · right; exact (hc.dvd.trans (map_dvd _ (map_dvd _ h))).trans ha.symm.dvd
    obtain ⟨hV, halg⟩ := GlobalTheory.valuationRing_of_flat_of_formallyUnramified (Localization.AtPrime p) (Localization.AtPrime η)
    have hBinj : Function.Injective (algebraMap B (Localization.AtPrime η)) :=
      IsLocalization.injective _ η.primeCompl_le_nonZeroDivisors
    obtain ⟨π, hπ⟩ := exists_associated_of_isAlgebraic O K (Localization.AtPrime p)
      (Localization.AtPrime η)
      ((algebraMap (MvPolynomial (Fin g) O) (Localization.AtPrime p)).comp MvPolynomial.C)
      (fun w hw h0 => by
        have := Module.Flat.isSMulRegular_of_nonZeroDivisors (M := Localization.AtPrime η)
          (mem_nonZeroDivisors_of_ne_zero hw)
        exact one_ne_zero (this.right_eq_zero_of_smul (by rw [Algebra.smul_def, h0, zero_mul])))
      hW (algebraMap B _ b) (fun h => hb (hBinj (h.trans (map_zero _).symm)))
      (halg.isAlgebraic _)
    rw [RingHom.comp_apply, ← IsScalarTower.algebraMap_apply,
      IsScalarTower.algebraMap_apply (MvPolynomial (Fin g) O) B (Localization.AtPrime η), hC] at hπ
    obtain ⟨v, hv⟩ := hπ
    obtain ⟨⟨s, t⟩, hst⟩ := IsLocalization.mk'_surjective η.primeCompl
      (v : Localization.AtPrime η)
    simp only at hst
    have hs : s ∈ η.primeCompl :=
      (IsLocalization.AtPrime.isUnit_mk'_iff (Localization.AtPrime η) η s t).1 (hst ▸ v.isUnit)
    refine ⟨π, s, t, hs, t.2, hBinj ?_⟩
    rw [map_mul, map_mul, ← hv, ← hst, mul_assoc, IsLocalization.mk'_spec, mul_comm]
  obtain ⟨π, s, t, hs, ht, hst⟩ := step1
  have step2 : algebraMap O B π ∣ b := by
    by_cases hu : IsUnit π
    · exact (hu.map _).dvd
    have hs0 : s ≠ 0 := fun h => hs (h ▸ η.zero_mem)
    have hπ0 : π ≠ 0 := by
      rintro rfl
      rw [map_zero, zero_mul] at hst
      exact mul_ne_zero hs0 hb hst
    have hnd : ¬ Disjoint (Ideal.span {s, algebraMap O B π} : Set B)
        (p.primeCompl.map (algebraMap (MvPolynomial (Fin g) O) B) : Set B) := by
      intro hd
      obtain ⟨Q, hQ, hle, hdis⟩ := Ideal.exists_le_prime_disjoint _ _ hd
      have hsQ : s ∈ Q := hle (Ideal.subset_span (by simp))
      have hπQ : algebraMap O B π ∈ Q := hle (Ideal.subset_span (by simp))
      have hmax : (Q.comap (algebraMap O B)).IsMaximal :=
        Ring.DimensionLEOne.maximalOfPrime
          (fun h => hπ0 (by rw [← Ideal.mem_bot, ← h]; exact hπQ)) inferInstance
      have hηQ : η ≤ Q := by
        rw [← hηp, Ideal.map_le_iff_le_comap, IsLocalRing.eq_maximalIdeal hmax]
      have hunder : η.under (MvPolynomial (Fin g) O) = Q.under (MvPolynomial (Fin g) O) := by
        refine le_antisymm (Ideal.comap_mono hηQ) fun x hx => ?_
        rw [← hlo.over]
        by_contra hxp
        exact Set.disjoint_left.1 hdis hx ⟨x, hxp, rfl⟩
      have := Algebra.QuasiFinite.eq_of_le_of_under_eq η Q hηQ hunder
      exact hs (this ▸ hsQ)
    obtain ⟨_, hy, u, hu, rfl⟩ := Set.not_disjoint_iff.1 hnd
    obtain ⟨c, d, hcd⟩ := Ideal.mem_span_pair.1 hy
    rw [← hC]
    refine dvd_of_dvd_mul_of_flat _ u (fun F => hcanc π u F hu) b ?_
    rw [hC]
    refine ⟨c * t + d * b, ?_⟩
    rw [← hcd]
    linear_combination c * hst
  obtain ⟨b', rfl⟩ := step2
  refine ⟨π, b', rfl, fun hb' => ht ?_⟩
  have : s * b' = t := by
    apply mul_left_cancel₀ (left_ne_zero_of_mul hb)
    rw [← hst]; ring
  rw [← this]
  exact η.mul_mem_left _ hb'
end GlobalTheory
