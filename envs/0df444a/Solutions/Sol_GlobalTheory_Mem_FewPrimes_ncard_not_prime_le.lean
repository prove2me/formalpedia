-- Prove2me | solution 1 for GlobalTheory.Mem.FewPrimes.ncard_not_prime_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T20:51:57.77305+00:00
-- url     : https://prove2.me/submissions/9946b345-ee71-4b08-b2c9-4dcfea4a2dae

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsPrimeMemHeightOneSpectrum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_PrimeIdealsCountingBounds
import Theorems.Thm_GlobalTheory_Mem_FewPrimes_exists_eq_span

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
theorem _root_.solution (hK : Module.finrank ℚ K = 2) (X : ℝ) :
    ({v : HeightOneSpectrum (𝓞 K) | (Ideal.absNorm v.asIdeal : ℝ) ≤ X ∧
      ¬ (Ideal.absNorm v.asIdeal).Prime}.ncard : ℝ) ≤ Real.sqrt X := by
  have h : {v : HeightOneSpectrum (𝓞 K) | (Ideal.absNorm v.asIdeal : ℝ) ≤ X ∧
      ¬ (Ideal.absNorm v.asIdeal).Prime}.ncard ≤
      ((Finset.Icc 1 ⌊Real.sqrt X⌋₊ : Finset ℕ) : Set ℕ).ncard := by
    refine Set.ncard_le_ncard_of_injOn (fun v => Nat.sqrt (Ideal.absNorm v.asIdeal)) ?_ ?_
      (Finset.finite_toSet _)
    · rintro v ⟨hX, hv⟩
      obtain ⟨p, hp, -, h3⟩ := exists_eq_span hK v hv
      rw [h3] at hX
      simp only [h3, Nat.sqrt_eq', Finset.coe_Icc, Set.mem_Icc]
      refine ⟨hp.pos, Nat.le_floor ?_⟩
      apply Real.le_sqrt_of_sq_le
      exact_mod_cast hX
    · rintro v ⟨-, hv⟩ w ⟨-, hw⟩ hvw
      obtain ⟨p, hp, e1, h3⟩ := exists_eq_span hK v hv
      obtain ⟨q, hq, e2, h4⟩ := exists_eq_span hK w hw
      simp only [h3, h4, Nat.sqrt_eq'] at hvw
      apply HeightOneSpectrum.ext
      rw [e1, e2, hvw]
  rw [Set.ncard_coe_finset, Nat.card_Icc, Nat.add_sub_cancel] at h
  exact le_trans (by exact_mod_cast h) (Nat.floor_le (Real.sqrt_nonneg X))
end GlobalTheory.Mem.FewPrimes
