-- Prove2me | solution 1 for GlobalTheory.PMonE.WinCoef.pw_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T19:51:42.935047+00:00
-- url     : https://prove2.me/submissions/6b0e0af9-f5ea-4315-a532-c1f7008c3e02

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_MooreNorm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_RowTEqRowS
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_WindowSummedRowPowEqAdditiveSystemPowerSum
import Theorems.Thm_GlobalTheory_PMonE_WinCoef_pw_eq

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
theorem _root_.solution (k : ℤ) (a b : F) : pw p k (a * b) = pw p k a * pw p k b := by
  rw [pw_eq, pw_eq, pw_eq, map_mul]
end GlobalTheory.PMonE.WinCoef
