-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.BB.GaussReg.posdef_quadratic_lower_bound_l1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T13:28:01.772184+00:00
-- url     : https://prove2.me/submissions/624187b7-7b99-45cd-a164-946ec5df735e

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_GaussQ
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_InfiniteAdelesLocalRingTotallyRealStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_TensorLocallyCompactRingStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_GaussianContinuousRapidDecay
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_BB_GaussReg_exists_lower_sup

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
theorem _root_.solution {n : Type} [Fintype n] [DecidableEq n] {P : Matrix n n ℝ} (hP : P.PosDef) :
    ∃ c : ℝ, 0 < c ∧ ∀ x : n → ℝ, c * (∑ p, |x p|) ^ 2 ≤ x ⬝ᵥ (P *ᵥ x) := by
  obtain ⟨c, hc, h⟩ := exists_lower_sup hP
  set N : ℝ := (Fintype.card n : ℝ)
  have hN : 0 ≤ N := Nat.cast_nonneg _
  refine ⟨c / (N ^ 2 + 1), by positivity, fun x => (?_ : _ ≤ _).trans (h x)⟩
  have h1 : ∑ p, |x p| ≤ N * ‖x‖ := by
    calc ∑ p, |x p| ≤ ∑ _p : n, ‖x‖ := Finset.sum_le_sum fun p _ => norm_le_pi_norm x p
      _ = N * ‖x‖ := by simp [N]
  have h0 : 0 ≤ ∑ p, |x p| := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have h2 : (∑ p, |x p|) ^ 2 ≤ (N ^ 2 + 1) * ‖x‖ ^ 2 := by
    have := pow_le_pow_left₀ h0 h1 2
    nlinarith [sq_nonneg ‖x‖]
  rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
  nlinarith
end GlobalTheory.CompanionTheory.SW.BB.GaussReg
