-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.BB.GaussReg.exists_lower_family
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T13:49:08.391814+00:00
-- url     : https://prove2.me/submissions/cb4df1df-e40c-4f0d-af32-d35b33a5267e

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_GaussQ
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_InfiniteAdelesLocalRingTotallyRealStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_TensorLocallyCompactRingStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_GaussianContinuousRapidDecay
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_BB_GaussReg_posdef_quadratic_lower_bound_l1

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.BB NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.BB GlobalTheory.CompanionTheory.SW.BB.GaussReg
namespace GlobalTheory.CompanionTheory.SW.BB.GaussReg
theorem _root_.solution {ι n : Type} [Fintype ι] [Fintype n] [DecidableEq n]
    {P : ι → Matrix n n ℝ} (hP : ∀ i, (P i).PosDef) :
    ∃ c : ℝ, 0 < c ∧ ∀ y : ι → n → ℝ,
      c * (∑ i, ∑ p, |y i p|) ^ 2 ≤ ∑ i, y i ⬝ᵥ (P i *ᵥ y i) := by
  choose c hc h using fun i => posdef_quadratic_lower_bound_l1 (hP i)
  obtain ⟨c0, hc0, hle⟩ : ∃ c0 : ℝ, 0 < c0 ∧ ∀ i, c0 ≤ c i := by
    rcases isEmpty_or_nonempty ι with hι | hι
    · exact ⟨1, one_pos, fun i => (hι.false i).elim⟩
    · obtain ⟨i, hi⟩ := Finite.exists_min c
      exact ⟨c i, hc i, hi⟩
  set W : ℝ := (Fintype.card ι : ℝ)
  have hW : 0 ≤ W := Nat.cast_nonneg _
  refine ⟨c0 / (W + 1), by positivity, fun y => ?_⟩
  have h1 : (∑ i, ∑ p, |y i p|) ^ 2 ≤ W * ∑ i, (∑ p, |y i p|) ^ 2 := by
    simpa [W] using sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun i => ∑ p, |y i p|)
  have hS : 0 ≤ ∑ i, (∑ p, |y i p|) ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have h2 : c0 * ∑ i, (∑ p, |y i p|) ^ 2 ≤ ∑ i, y i ⬝ᵥ (P i *ᵥ y i) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun i _ =>
      (mul_le_mul_of_nonneg_right (hle i) (sq_nonneg _)).trans (h i (y i))
  refine le_trans ?_ h2
  rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
  have h3 : (∑ i, ∑ p, |y i p|) ^ 2 ≤ (W + 1) * ∑ i, (∑ p, |y i p|) ^ 2 := by nlinarith
  nlinarith [mul_le_mul_of_nonneg_left h3 hc0.le]
end GlobalTheory.CompanionTheory.SW.BB.GaussReg
