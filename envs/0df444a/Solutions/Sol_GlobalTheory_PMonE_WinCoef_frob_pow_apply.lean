-- Prove2me | solution 1 for GlobalTheory.PMonE.WinCoef.frob_pow_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:39:11.712449+00:00
-- url     : https://prove2.me/submissions/80e28461-0546-4412-8c01-e0b47662fda9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_MooreNorm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_RowTEqRowS
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_WindowSummedRowPowEqAdditiveSystemPowerSum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.PMonE
open Finset
open GlobalTheory GlobalTheory.PMonE GlobalTheory.PMonE.WinCoef
variable {F : Type} [NormedField F] (p : ℕ) [Fact p.Prime] [CharP F p] [PerfectRing F p]
namespace GlobalTheory.PMonE.WinCoef
theorem _root_.solution (n : ℕ) (x : F) : ((frobAut (F := F) p) ^ n) x = x ^ p ^ n := by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, RingAut.mul_apply, ih]
    simp only [frobAut, frobeniusEquiv_apply, frobenius_def, ← pow_mul, pow_succ]
    rw [mul_comm]
end GlobalTheory.PMonE.WinCoef
