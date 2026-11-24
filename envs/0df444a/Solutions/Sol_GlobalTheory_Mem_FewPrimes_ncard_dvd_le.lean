-- Prove2me | solution 1 for GlobalTheory.Mem.FewPrimes.ncard_dvd_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T18:55:45.537165+00:00
-- url     : https://prove2.me/submissions/b6790809-4c83-4f3f-96ff-a993f61f358e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsPrimeMemHeightOneSpectrum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_PrimeIdealsCountingBounds
import Theorems.Thm_GlobalTheory_Mem_FewPrimes_prod_absNorm_dvd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain
open GlobalTheory GlobalTheory.Mem GlobalTheory.Mem.FewPrimes
variable {K : Type} [Field K] [NumberField K]
namespace GlobalTheory.Mem.FewPrimes
theorem _root_.solution (𝔮 : Ideal (𝓞 K)) (hq : 𝔮 ≠ ⊥) :
    ({v : HeightOneSpectrum (𝓞 K) | v.asIdeal ∣ 𝔮}.ncard : ℝ) ≤
      3 * Real.log (4 * Ideal.absNorm 𝔮) := by
  have hf : {v : HeightOneSpectrum (𝓞 K) | v.asIdeal ∣ 𝔮}.Finite := Ideal.finite_factors hq
  have hN : Ideal.absNorm 𝔮 ≠ 0 := fun h => hq (Ideal.absNorm_eq_zero_iff.1 h)
  have h := Nat.le_of_dvd (Nat.pos_of_ne_zero hN)
    (prod_absNorm_dvd hf.toFinset 𝔮 (fun v hv => by simpa using hv))
  have h2 : 2 ^ hf.toFinset.card ≤ Ideal.absNorm 𝔮 :=
    le_trans (Finset.pow_card_le_prod _ _ _
      (fun v _ => NumberField.HeightOneSpectrum.one_lt_absNorm v)) h
  rw [Set.ncard_eq_toFinset_card _ hf]
  have h3 : (2 : ℝ) ^ hf.toFinset.card ≤ 4 * Ideal.absNorm 𝔮 := by
    have : ((2 ^ hf.toFinset.card : ℕ) : ℝ) ≤ Ideal.absNorm 𝔮 := by exact_mod_cast h2
    push_cast at this
    have h0 : (0 : ℝ) ≤ Ideal.absNorm 𝔮 := Nat.cast_nonneg _
    linarith
  have h4 := Real.log_le_log (by positivity) h3
  rw [Real.log_pow] at h4
  have h5 := Real.log_two_gt_d9
  have h6 : (0 : ℝ) ≤ hf.toFinset.card := Nat.cast_nonneg _
  nlinarith
end GlobalTheory.Mem.FewPrimes
