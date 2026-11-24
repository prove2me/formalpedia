-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.BB.GaussReg.exp_mul_pow_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T13:12:13.287674+00:00
-- url     : https://prove2.me/submissions/add9df0f-9c32-4279-9706-83321c3d2bcc

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_GaussQ
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_InfiniteAdelesLocalRingTotallyRealStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_TensorLocallyCompactRingStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_GaussianContinuousRapidDecay

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
theorem _root_.solution {a : ℝ} (ha : 0 < a) (N : ℕ) {s : ℝ} (hs : 0 ≤ s) {q : ℝ} (hq : a * s ^ 2 ≤ q) :
    Real.exp (-q) * (1 + s) ^ N ≤ Real.exp ((N : ℝ) ^ 2 / (4 * a)) := by
  have h1 : (1 + s) ^ N ≤ Real.exp ((N : ℝ) * s) := by
    rw [mul_comm, Real.exp_mul, Real.rpow_natCast]
    exact pow_le_pow_left₀ (by linarith) (by linarith [Real.add_one_le_exp s]) N
  calc Real.exp (-q) * (1 + s) ^ N ≤ Real.exp (-q) * Real.exp ((N : ℝ) * s) :=
        mul_le_mul_of_nonneg_left h1 (Real.exp_pos _).le
    _ = Real.exp (-q + (N : ℝ) * s) := (Real.exp_add _ _).symm
    _ ≤ _ := by
      apply Real.exp_le_exp.2
      have h2 : (N : ℝ) * s ≤ a * s ^ 2 + (N : ℝ) ^ 2 / (4 * a) := by
        have : 0 ≤ (2 * a * s - N) ^ 2 / (4 * a) := by positivity
        have e : (2 * a * s - N) ^ 2 / (4 * a) = a * s ^ 2 + (N : ℝ) ^ 2 / (4 * a) - N * s := by
          field_simp
          ring
        linarith
      linarith
end GlobalTheory.CompanionTheory.SW.BB.GaussReg
