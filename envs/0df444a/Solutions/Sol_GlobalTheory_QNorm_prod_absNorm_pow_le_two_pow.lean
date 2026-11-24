-- Prove2me | solution 1 for GlobalTheory.QNorm.prod_absNorm_pow_le_two_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T19:43:50.269247+00:00
-- url     : https://prove2.me/submissions/dc304526-5577-42ef-af52-cdc02c553919

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_SqSubLeNormSub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ProdAbsNormPowValuationTwoLe

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
    ∀ (F : Type) [Field F] [NumberField F] (S : Finset (HeightOneSpectrum (𝓞 F))) (e : HeightOneSpectrum (𝓞 F) → ℕ), (∀ v ∈ S, v.valuation F 2 = WithZero.exp (-(e v : ℤ))) → ∏ v ∈ S, Ideal.absNorm v.asIdeal ^ e v ≤ 2 ^ Module.finrank ℚ F := by
  intro F _ _ S e h
  have hdvd : ∀ v ∈ S, v.asIdeal ^ e v ∣ Ideal.span {(2 : 𝓞 F)} := by
    intro v hv
    rw [← HeightOneSpectrum.intValuation_le_pow_iff_dvd]
    have h2 : v.valuation F (algebraMap (𝓞 F) F 2) = v.intValuation 2 :=
      HeightOneSpectrum.valuation_of_algebraMap v 2
    rw [map_ofNat, h v hv] at h2
    exact h2.ge
  have hprod : ∏ v ∈ S, v.asIdeal ^ e v ∣ Ideal.span {(2 : 𝓞 F)} := by
    refine Finset.prod_dvd_of_coprime ?_ hdvd
    intro v _ w _ hvw
    refine IsCoprime.pow ?_
    rw [Ideal.isCoprime_iff_sup_eq]
    exact Ideal.IsMaximal.coprime_of_ne v.isMaximal w.isMaximal
      (fun hh => hvw (HeightOneSpectrum.ext hh))
  have hn : Ideal.absNorm (Ideal.span {(2 : 𝓞 F)}) = 2 ^ Module.finrank ℚ F := by
    rw [Ideal.absNorm_span_singleton]
    have : (2 : 𝓞 F) = algebraMap ℤ (𝓞 F) 2 := by simp
    rw [this, Algebra.norm_algebraMap, RingOfIntegers.rank]
    simp [Int.natAbs_pow]
  have h3 := map_dvd Ideal.absNorm hprod
  rw [hn, map_prod] at h3
  simp only [map_pow] at h3
  exact Nat.le_of_dvd (by positivity) h3
end GlobalTheory.QNorm
