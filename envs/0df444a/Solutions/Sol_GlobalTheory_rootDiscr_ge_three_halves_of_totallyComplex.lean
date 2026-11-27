-- Prove2me | solution 1 for GlobalTheory.rootDiscr_ge_three_halves_of_totallyComplex
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T04:40:53.42119+00:00
-- url     : https://prove2.me/submissions/1f88120e-a917-4743-b21d-190493f76510

import Mathlib
import Definitions.Def_Formalism_HermitianLattices_StatementMass
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_RootDiscrGeThreeHalvesOfIsTotallyComplex

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory NumberField Finset
open GlobalTheory
open MeasureTheory NumberField Finset
namespace GlobalTheory
namespace _root_.GlobalTheory
theorem _root_.solution :
    ∀ (K : Type) [Field K] [NumberField K], IsTotallyComplex K →
      Module.finrank ℚ K = 2 * _root_.Formalism.HermitianLatticesTheory.fDeg K ∧ 1 ≤ _root_.Formalism.HermitianLatticesTheory.fDeg K ∧
      (3 / 2 : ℝ) ≤ 2 * _root_.Formalism.HermitianLatticesTheory.vInv K ∧
      Real.sqrt |(discr K : ℝ)| = (2 * _root_.Formalism.HermitianLatticesTheory.vInv K) ^ _root_.Formalism.HermitianLatticesTheory.fDeg K := by
  intro K _ _ hK
  have hf : _root_.Formalism.HermitianLatticesTheory.fDeg K = InfinitePlace.nrComplexPlaces K := by
    unfold _root_.Formalism.HermitianLatticesTheory.fDeg
    rw [InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces,
      IsTotallyComplex.nrRealPlaces_eq_zero, zero_add]
  have hn : Module.finrank ℚ K = 2 * _root_.Formalism.HermitianLatticesTheory.fDeg K := by
    rw [hf]; exact IsTotallyComplex.finrank K
  have hpos : 0 < Module.finrank ℚ K := Module.finrank_pos
  have h1 : 1 ≤ _root_.Formalism.HermitianLatticesTheory.fDeg K := by omega
  have hv : 2 * _root_.Formalism.HermitianLatticesTheory.vInv K = |(discr K : ℝ)| ^ (1 / (2 * (_root_.Formalism.HermitianLatticesTheory.fDeg K : ℝ))) := by
    unfold _root_.Formalism.HermitianLatticesTheory.vInv; ring
  have hD0 : 0 ≤ |(discr K : ℝ)| := abs_nonneg _
  have hbound : (3 / 2 : ℝ) ^ (2 * _root_.Formalism.HermitianLatticesTheory.fDeg K) ≤ |(discr K : ℝ)| := by
    have hd := abs_discr_ge (K := K) (by omega)
    rw [hn, Int.cast_abs] at hd
    refine le_trans ?_ hd
    obtain ⟨m, hm⟩ : ∃ m, _root_.Formalism.HermitianLatticesTheory.fDeg K = m + 1 := ⟨_root_.Formalism.HermitianLatticesTheory.fDeg K - 1, by omega⟩
    rw [hm, pow_mul, pow_mul, pow_succ ((3 / 2 : ℝ) ^ 2), pow_succ ((3 * Real.pi / 4) ^ 2)]
    have hpi := Real.pi_gt_d2
    have hc : (11 / 2 : ℝ) ≤ (3 * Real.pi / 4) ^ 2 := by nlinarith
    have hm' : ((3 / 2 : ℝ) ^ 2) ^ m ≤ ((3 * Real.pi / 4) ^ 2) ^ m :=
      pow_le_pow_left₀ (by positivity) (by nlinarith) m
    have hc' : (3 / 2 : ℝ) ^ 2 ≤ 4 / 9 * (3 * Real.pi / 4) ^ 2 := by nlinarith
    have := mul_le_mul hm' hc' (by positivity) (by positivity)
    linarith
  have hne : (2 * _root_.Formalism.HermitianLatticesTheory.fDeg K) ≠ 0 := by omega
  have hexp : (1 / (2 * (_root_.Formalism.HermitianLatticesTheory.fDeg K : ℝ))) = (((2 * _root_.Formalism.HermitianLatticesTheory.fDeg K : ℕ) : ℝ))⁻¹ := by
    push_cast; rw [one_div]
  refine ⟨hn, h1, ?_, ?_⟩
  · rw [hv, hexp]
    calc (3 / 2 : ℝ) = ((3 / 2 : ℝ) ^ (2 * _root_.Formalism.HermitianLatticesTheory.fDeg K)) ^ (((2 * _root_.Formalism.HermitianLatticesTheory.fDeg K : ℕ) : ℝ))⁻¹ :=
          (Real.pow_rpow_inv_natCast (by norm_num) hne).symm
      _ ≤ |(discr K : ℝ)| ^ (((2 * _root_.Formalism.HermitianLatticesTheory.fDeg K : ℕ) : ℝ))⁻¹ :=
          Real.rpow_le_rpow (by positivity) hbound (by positivity)
  · rw [hv, ← Real.rpow_natCast, ← Real.rpow_mul hD0, Real.sqrt_eq_rpow]
    congr 1
    have : (_root_.Formalism.HermitianLatticesTheory.fDeg K : ℝ) ≠ 0 := by exact_mod_cast (by omega : _root_.Formalism.HermitianLatticesTheory.fDeg K ≠ 0)
    field_simp
end _root_.GlobalTheory
end GlobalTheory
