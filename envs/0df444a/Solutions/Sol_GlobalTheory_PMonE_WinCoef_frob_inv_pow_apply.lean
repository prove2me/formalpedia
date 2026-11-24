-- Prove2me | solution 1 for GlobalTheory.PMonE.WinCoef.frob_inv_pow_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T19:19:54.135271+00:00
-- url     : https://prove2.me/submissions/6181dc1e-8cc7-4331-90fb-aa1786c21f5d

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
theorem _root_.solution (n : ℕ) (x : F) :
    (((frobAut (F := F) p)⁻¹) ^ n) x = ((frobeniusEquiv F p).symm)^[n] x := by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, Function.iterate_succ_apply, RingAut.mul_apply, ih, RingAut.inv_apply]
end GlobalTheory.PMonE.WinCoef
