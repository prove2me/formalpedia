-- Prove2me | solution 1 for GlobalTheory.TorusElliptic.sum_fderiv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:11:53.825513+00:00
-- url     : https://prove2.me/submissions/5307593c-f5f9-41f3-a5a0-f714c7b82b29

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsRapidFourierSeriesOfIntPeriodic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ContDiffAndFderivTsumFourierOfRapid
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_FourierCoeffEqZeroOfTsumEqZeroFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_TorusEllipticSystemSolvable
import Theorems.Thm_GlobalTheory_TorusElliptic_Rapid_summable
import Theorems.Thm_GlobalTheory_TorusElliptic_Rapid_mul
import Theorems.Thm_GlobalTheory_TorusElliptic_summable_ch
import Theorems.Thm_GlobalTheory_contDiff_and_fderiv_tsum_fourier_of_rapid


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Matrix
open scoped ContDiff BigOperators Real
open GlobalTheory
open GlobalTheory.TorusElliptic
namespace GlobalTheory.TorusElliptic
theorem _root_.solution {n : ℕ} {c : (Fin n → ℤ) → ℂ} (h : Rapid c) (q : Fin n → ℂ) (x : Fin n → ℝ) :
    ∑ k, q k * fderiv ℝ (fun x : Fin n → ℝ => ∑' ν, c ν * ch ν x) x (Pi.single k 1)
      = ∑' ν, 2 * π * I * (∑ k, q k * (ν k : ℂ)) * c ν * ch ν x := by
  have h1 : ∀ k, q k * fderiv ℝ (fun x : Fin n → ℝ => ∑' ν, c ν * ch ν x) x (Pi.single k 1)
      = ∑' ν : Fin n → ℤ, (q k * (2 * π * I)) * (ν k : ℂ) * c ν * ch ν x := by
    intro k
    have := (GlobalTheory.contDiff_and_fderiv_tsum_fourier_of_rapid n c h).2 x k
    unfold ch
    rw [this, ← tsum_mul_left]
    exact tsum_congr fun ν => by ring
  simp_rw [h1]
  rw [← Summable.tsum_finsetSum fun k _ => summable_ch (h.mul _ k).summable x]
  refine tsum_congr fun ν => ?_
  rw [Finset.mul_sum, Finset.sum_mul, Finset.sum_mul]
  exact Finset.sum_congr rfl fun k _ => by ring
end GlobalTheory.TorusElliptic
