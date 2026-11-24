-- Prove2me | solution 1 for GlobalTheory.TorusElliptic.summable_symb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:11:55.615159+00:00
-- url     : https://prove2.me/submissions/d708cf87-30cf-4496-800d-886d38248ce4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsRapidFourierSeriesOfIntPeriodic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ContDiffAndFderivTsumFourierOfRapid
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_FourierCoeffEqZeroOfTsumEqZeroFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_TorusEllipticSystemSolvable
import Theorems.Thm_GlobalTheory_TorusElliptic_Rapid_summable
import Theorems.Thm_GlobalTheory_TorusElliptic_Rapid_mul

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
theorem _root_.solution {n : ℕ} {c : (Fin n → ℤ) → ℂ} (h : Rapid c) (q : Fin n → ℂ) :
    Summable (fun ν : Fin n → ℤ => ‖2 * π * I * (∑ k, q k * (ν k : ℂ)) * c ν‖) := by
  have : Summable (fun ν : Fin n → ℤ => ∑ k, (q k * (2 * π * I)) * (ν k : ℂ) * c ν) :=
    summable_sum fun k _ => (h.mul _ k).summable.of_norm
  refine (summable_norm_iff.2 this).congr fun ν => ?_
  congr 1
  rw [Finset.mul_sum, Finset.sum_mul]
  exact Finset.sum_congr rfl fun k _ => by ring
end GlobalTheory.TorusElliptic
