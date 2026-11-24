-- Prove2me | solution 1 for GlobalTheory.PMonE.LinCount.lin_one_cast
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T19:17:26.968947+00:00
-- url     : https://prove2.me/submissions/bf220875-e543-420c-8378-d723169d1af7

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
theorem _root_.solution (K : ℕ) (M : ℕ → Matrix m m F) (Y : Fin (K + 1) × m → F) (i : Fin K) (a : m) :
    (lin K M 1).mulVec Y (i.castSucc, a) = Y (i.castSucc, a) := by
  simp [Matrix.mulVec, dotProduct, lin, (Fin.castSucc_lt_last i).ne]
end GlobalTheory.PMonE.LinCount
