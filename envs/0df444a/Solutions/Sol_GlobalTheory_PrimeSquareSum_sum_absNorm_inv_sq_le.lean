-- Prove2me | solution 1 for GlobalTheory.PrimeSquareSum.sum_absNorm_inv_sq_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T19:46:36.661035+00:00
-- url     : https://prove2.me/submissions/3dabbbb4-6c4f-4790-bba1-d2b7d4ac6338

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ExistsIdealInClassOfNormLeSqrtDiscr
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SummableAbsNormInvSq
import Theorems.Thm_GlobalTheory_PrimeSquareSum_sum_inv_sq_le_one
import Theorems.Thm_GlobalTheory_exists_colouring_maximal_ideals


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory IsDedekindDomain NumberField
open GlobalTheory GlobalTheory.PrimeSquareSum
namespace GlobalTheory.PrimeSquareSum
theorem _root_.solution (K : Type) [Field K] [NumberField K]
    (s : Finset (HeightOneSpectrum (𝓞 K))) :
    ∑ w ∈ s, (((Ideal.absNorm w.asIdeal : ℕ) : ℝ) ^ 2)⁻¹ ≤ (Module.finrank ℚ K : ℝ) := by
  classical
  obtain ⟨c, hc⟩ := GlobalTheory.exists_colouring_maximal_ideals K
  have hp : ∀ w : HeightOneSpectrum (𝓞 K), ∃ p : ℕ, p.Prime ∧ (p : 𝓞 K) ∈ w.asIdeal ∧
      p ≤ Ideal.absNorm w.asIdeal := by
    intro w
    haveI := w.isMaximal
    obtain ⟨q, n, hn, hqP, hq, H⟩ := Ideal.exists_prime_and_absNorm_eq_pow w.asIdeal
    exact ⟨q, hq, hqP, H ▸ Nat.le_self_pow hn.ne' q⟩
  choose p hp hpm hple using hp
  rw [← Finset.sum_fiberwise s (fun w => c w.asIdeal)]
  calc _ ≤ ∑ _i : Fin (Module.finrank ℚ K), (1 : ℝ) := by
        refine Finset.sum_le_sum fun i _ => ?_
        have hinj : Set.InjOn p (s.filter fun w => c w.asIdeal = i) := by
          intro v hv w hw h
          simp only [Finset.coe_filter, Set.mem_setOf_eq] at hv hw
          exact HeightOneSpectrum.ext (hc (p v) (hp v) _ _ v.isMaximal w.isMaximal (hpm v)
            (h ▸ hpm w) (hv.2.trans hw.2.symm))
        calc _ ≤ ∑ w ∈ s.filter (fun w => c w.asIdeal = i), ((p w : ℝ) ^ 2)⁻¹ := by
              refine Finset.sum_le_sum fun w _ => ?_
              have h0 : (0 : ℝ) < p w := by exact_mod_cast (hp w).pos
              have h1 : (p w : ℝ) ≤ (Ideal.absNorm w.asIdeal : ℕ) := by exact_mod_cast hple w
              gcongr
          _ = ∑ n ∈ (s.filter (fun w => c w.asIdeal = i)).image p, ((n : ℝ) ^ 2)⁻¹ :=
              (Finset.sum_image (f := fun n : ℕ => ((n : ℝ) ^ 2)⁻¹) hinj).symm
          _ ≤ 1 := by
              refine sum_inv_sq_le_one _ fun n hn => ?_
              obtain ⟨w, -, rfl⟩ := Finset.mem_image.1 hn
              exact (hp w).two_le
    _ = _ := by simp
end GlobalTheory.PrimeSquareSum
