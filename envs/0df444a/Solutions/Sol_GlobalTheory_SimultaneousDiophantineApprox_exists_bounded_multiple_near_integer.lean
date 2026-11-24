-- Prove2me | solution 1 for GlobalTheory.SimultaneousDiophantineApprox.exists_bounded_multiple_near_integer
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T21:02:50.053461+00:00
-- url     : https://prove2.me/submissions/d5b556e8-f6f5-4ebe-b6a2-db8d4d290ccf

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsBoundedMultipleNearInteger
import Theorems.Thm_GlobalTheory_SimultaneousDiophantineApprox_simultaneous_approx

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.SimultaneousDiophantineApprox
open NumberField
namespace GlobalTheory.SimultaneousDiophantineApprox
theorem _root_.solution (E : Type) [Field E] [NumberField E] :
    ∃ M : ℕ, ∀ x : E, ∃ (m : ℕ) (y : E), 0 < m ∧ m ≤ M ∧ IsIntegral ℤ y ∧
      ‖canonicalEmbedding E ((m : E) * x - y)‖ < 1 := by
  classical
  set b := integralBasis E

  set C : ℝ := ∑ i, ∑ σ : E →+* ℂ, ‖σ (b i)‖ with hC
  have hC0 : 0 ≤ C := Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun σ _ => norm_nonneg _
  obtain ⟨N, hN⟩ := exists_nat_gt C
  have hN0 : 0 < N := by exact_mod_cast hC0.trans_lt hN
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN0
  refine ⟨N ^ Fintype.card (Module.Free.ChooseBasisIndex ℤ (𝓞 E)), fun x => ?_⟩
  obtain ⟨m, hm0, hmN, z, hz⟩ := simultaneous_approx N hN0 (b.repr x)
  refine ⟨m, ∑ i, (z i : E) * b i, hm0, hmN, ?_, ?_⟩
  · refine IsIntegral.sum _ fun i _ => IsIntegral.mul ?_ ?_
    · simpa using (isIntegral_algebraMap : IsIntegral ℤ (algebraMap ℤ E (z i)))
    · rw [integralBasis_apply]
      exact RingOfIntegers.isIntegral_coe _
  ·
    have hx : (m : E) * x - ∑ i, (z i : E) * b i =
        ∑ i, ((((m : ℚ) * b.repr x i - z i : ℚ)) : E) * b i := by
      conv_lhs => rw [← b.sum_repr x]
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Rat.smul_def]
      push_cast
      ring
    rw [hx, pi_norm_lt_iff one_pos]
    intro σ
    rw [canonicalEmbedding.apply_at, map_sum]
    refine lt_of_le_of_lt (norm_sum_le _ _) ?_
    refine lt_of_le_of_lt (Finset.sum_le_sum (g := fun i => 1 / (N : ℝ) * ∑ τ : E →+* ℂ, ‖τ (b i)‖)
      fun i _ => ?_) ?_
    · rw [map_mul, norm_mul, map_ratCast, Complex.norm_ratCast]
      refine mul_le_mul ?_ (Finset.single_le_sum (f := fun τ : E →+* ℂ => ‖τ (b i)‖)
        (fun _ _ => norm_nonneg _) (Finset.mem_univ σ)) (norm_nonneg _) (by positivity)
      have h := Rat.cast_le (K := ℝ) |>.mpr (hz i)
      rwa [Rat.cast_div, Rat.cast_one, Rat.cast_natCast, Rat.cast_abs] at h
    · rw [← Finset.mul_sum, ← hC, one_div_mul_eq_div, div_lt_one hNr]
      exact hN
end GlobalTheory.SimultaneousDiophantineApprox
