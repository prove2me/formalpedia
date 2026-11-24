-- Prove2me | solution 1 for GlobalTheory.InvDiffLocal.exists_not_mem_mul_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T17:53:56.475685+00:00
-- url     : https://prove2.me/submissions/50d328d3-267e-4f63-846f-626009c5af44

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ValuationMulLeOneOfTraceApproxIdempotentIntegral

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain
open Classical
open GlobalTheory GlobalTheory.InvDiffLocal
open IsDedekindDomain.HeightOneSpectrum
namespace GlobalTheory.InvDiffLocal
theorem _root_.solution {R : Type} [CommRing R] [IsDedekindDomain R] {K : Type} [Field K]
    [Algebra R K] [IsFractionRing R K] (v : HeightOneSpectrum R) (t : K)
    (ht : v.valuation K t ≤ 1) :
    ∃ s : R, s ∉ v.asIdeal ∧ ∃ r : R, algebraMap R K s * t = algebraMap R K r := by
  obtain ⟨⟨a, ⟨b, hb⟩⟩, rfl⟩ := IsLocalization.mk'_surjective (nonZeroDivisors R) t
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  rw [valuation_of_mk'] at ht
  set n := (Associates.mk v.asIdeal).count (Associates.mk (Ideal.span {b})).factors with hn
  have hvb : v.intValuation b = WithZero.exp (-(n : ℤ)) := v.intValuation_if_neg hb0
  have hpos : (0 : WithZero (Multiplicative ℤ)) < v.intValuation b := by
    rw [hvb]; exact WithZero.exp_pos
  have hva : v.intValuation a ≤ WithZero.exp (-(n : ℤ)) := by
    rw [← hvb]; exact (div_le_one₀ hpos).1 ht
  have haI : a ∈ v.asIdeal ^ n := (v.intValuation_le_pow_iff_mem a n).1 hva
  have hbI : b ∈ v.asIdeal ^ n := (v.intValuation_le_pow_iff_mem b n).1 hvb.le
  have hbI' : b ∉ v.asIdeal ^ (n + 1) := by
    intro h
    have := (v.intValuation_le_pow_iff_mem b (n + 1)).2 h
    rw [hvb] at this
    have h2 := WithZero.exp_le_exp.1 this
    push_cast at h2
    omega
  have hdvd : v.asIdeal ^ n ∣ Ideal.span {b} :=
    Ideal.dvd_iff_le.2 ((Ideal.span_singleton_le_iff_mem _).2 hbI)
  obtain ⟨B', hB'⟩ := hdvd
  have hB'p : ¬ B' ≤ v.asIdeal := by
    intro hle
    apply hbI'
    have : Ideal.span {b} ≤ v.asIdeal ^ (n + 1) := by
      rw [hB', pow_succ]; exact Ideal.mul_mono_right hle
    exact this (Ideal.mem_span_singleton_self b)
  obtain ⟨s, hsB, hsp⟩ := Set.not_subset.1 hB'p
  refine ⟨s, hsp, ?_⟩
  have hmem : a * s ∈ Ideal.span {b} := by
    rw [hB']; exact Ideal.mul_mem_mul haI hsB
  obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.1 hmem
  refine ⟨r, ?_⟩
  show algebraMap R K s * IsLocalization.mk' K a ⟨b, hb⟩ = algebraMap R K r
  rw [IsFractionRing.mk'_eq_div]
  have hbK : algebraMap R K b ≠ 0 := by
    rw [Ne, ← map_zero (algebraMap R K), (IsFractionRing.injective R K).eq_iff]; exact hb0
  rw [mul_div_assoc', div_eq_iff hbK, ← map_mul, ← map_mul, hr, mul_comm a s]
end GlobalTheory.InvDiffLocal
