-- Prove2me | solution 1 for GlobalTheory.exists_den_not_mem_of_count_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T04:37:04.655462+00:00
-- url     : https://prove2.me/submissions/028ed69e-fcc9-4db2-ad4c-76692be2c22c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsDenNotMemOfCountEqZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsDedekindDomain
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {R K : Type} [CommRing R] [IsDedekindDomain R]
    [Field K] [Algebra R K] [IsFractionRing R K] (P : IsDedekindDomain.HeightOneSpectrum R)
    (I : FractionalIdeal (nonZeroDivisors R) K) (hI : FractionalIdeal.count K P I = 0)
    {a : K} (ha : a ∈ I) :
    ∃ b c : R, c ∉ P.asIdeal ∧ algebraMap R K c * a = algebraMap R K b := by
  classical
  by_cases ha0 : a = 0
  · exact ⟨0, 1, fun h => P.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h), by simp [ha0]⟩
  have hle : FractionalIdeal.spanSingleton (nonZeroDivisors R) a ≤ I :=
    FractionalIdeal.spanSingleton_le_iff_mem.2 ha
  have hne : FractionalIdeal.spanSingleton (nonZeroDivisors R) a ≠ 0 :=
    FractionalIdeal.spanSingleton_ne_zero_iff.2 ha0
  have hc : 0 ≤ FractionalIdeal.count K P (FractionalIdeal.spanSingleton (nonZeroDivisors R) a) :=
    hI ▸ FractionalIdeal.count_mono K P hne hle
  obtain ⟨x, y, hy, rfl⟩ := IsFractionRing.div_surjective (A := R) a
  have hy0 : y ≠ 0 := nonZeroDivisors.ne_zero hy
  have hyK : algebraMap R K y ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hy
  have hx0 : x ≠ 0 := by rintro rfl; simp at ha0
  have hcoe : ∀ r : R, r ≠ 0 → FractionalIdeal.count K P
      (FractionalIdeal.spanSingleton (nonZeroDivisors R) (algebraMap R K r)) =
      ((Associates.mk P.asIdeal).count (Associates.mk (Ideal.span {r} : Ideal R)).factors : ℤ) := by
    intro r hr
    rw [← FractionalIdeal.coeIdeal_span_singleton, FractionalIdeal.count_coe K P]
    simpa using hr
  have hmul : FractionalIdeal.spanSingleton (nonZeroDivisors R) (algebraMap R K x / algebraMap R K y)
      * FractionalIdeal.spanSingleton (nonZeroDivisors R) (algebraMap R K y) =
      FractionalIdeal.spanSingleton (nonZeroDivisors R) (algebraMap R K x) := by
    rw [FractionalIdeal.spanSingleton_mul_spanSingleton, div_mul_cancel₀ _ hyK]
  have hcnt := congrArg (FractionalIdeal.count K P) hmul
  rw [FractionalIdeal.count_mul K P hne (FractionalIdeal.spanSingleton_ne_zero_iff.2 hyK),
    hcoe x hx0, hcoe y hy0] at hcnt
  have hval : P.valuation K (algebraMap R K x / algebraMap R K y) ≤ 1 := by
    rw [map_div₀, HeightOneSpectrum.valuation_of_algebraMap,
      HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_if_neg _ hx0,
      HeightOneSpectrum.intValuation_if_neg _ hy0, div_le_one₀ (zero_lt_iff.2 WithZero.exp_ne_zero),
      WithZero.exp_le_exp]
    omega
  have hmem : algebraMap R K x / algebraMap R K y ∈ P.valuationSubringAtPrime K := by
    rw [HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring]; exact hval
  obtain ⟨⟨b, c⟩, hbc⟩ := IsLocalization.surj P.asIdeal.primeCompl
    (⟨_, hmem⟩ : P.valuationSubringAtPrime K)
  refine ⟨b, c, c.2, ?_⟩
  have := congrArg (algebraMap (P.valuationSubringAtPrime K) K) hbc
  rw [map_mul, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply] at this
  rw [mul_comm]; exact this
end GlobalTheory
