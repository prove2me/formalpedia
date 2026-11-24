-- Prove2me | solution 1 for GlobalTheory.TorusElliptic.Rapid.mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:05:25.284859+00:00
-- url     : https://prove2.me/submissions/dbb2039e-6c8c-44c1-a5eb-18dcc9ba271a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsRapidFourierSeriesOfIntPeriodic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ContDiffAndFderivTsumFourierOfRapid
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_FourierCoeffEqZeroOfTsumEqZeroFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_TorusEllipticSystemSolvable

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
namespace Rapid
theorem _root_.solution {n : ℕ} {c : (Fin n → ℤ) → ℂ} (h : Rapid c) (z : ℂ) (j : Fin n) :
    Rapid (fun ν => z * (ν j : ℂ) * c ν) := by
  intro N
  obtain ⟨C, hC⟩ := h (N + 1)
  refine ⟨‖z‖ * C, fun ν => ?_⟩
  have h1 : ‖(ν j : ℂ)‖ ≤ 1 + ∑ k, |(ν k : ℝ)| := by
    have := Finset.single_le_sum (f := fun k => |(ν k : ℝ)|) (fun _ _ => abs_nonneg _)
            (Finset.mem_univ j)
    rw [Complex.norm_intCast]
    linarith
  calc ‖z * (ν j : ℂ) * c ν‖ * (1 + ∑ k, |(ν k : ℝ)|) ^ N
      = ‖z‖ * (‖c ν‖ * ((1 + ∑ k, |(ν k : ℝ)|) ^ N * ‖(ν j : ℂ)‖)) := by
        simp only [norm_mul]; ring
    _ ≤ ‖z‖ * (‖c ν‖ * ((1 + ∑ k, |(ν k : ℝ)|) ^ N * (1 + ∑ k, |(ν k : ℝ)|))) := by gcongr
    _ ≤ ‖z‖ * C := by rw [← pow_succ]; gcongr; exact hC ν
end Rapid
end GlobalTheory.TorusElliptic
