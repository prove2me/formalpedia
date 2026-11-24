-- Prove2me | solution 1 for GlobalTheory.PMonE.LinCount.lin_two_cast
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T19:17:29.480585+00:00
-- url     : https://prove2.me/submissions/3b89334d-3240-4e77-b9c6-381b0b14c96b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_MooreNorm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_AdditiveSystemIntegralSolutionCountOfOrderOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.PMonE GlobalTheory.PMonE.LinCount
open Finset GlobalTheory.PMonE
variable {F : Type*} [NormedField F] {m : Type*} [Fintype m] [DecidableEq m]
namespace GlobalTheory.PMonE.LinCount
theorem _root_.solution (K : ℕ) (M : ℕ → Matrix m m F) (k : ℕ) (Y : Fin (K + 1) × m → F) (i : Fin K) (a : m) :
    (lin K M (k + 1 + 1)).mulVec Y (i.castSucc, a) = 0 := by
  simp [Matrix.mulVec, dotProduct, lin, (Fin.castSucc_lt_last i).ne]
end GlobalTheory.PMonE.LinCount
