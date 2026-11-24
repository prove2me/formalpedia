-- Prove2me | solution 1 for GlobalTheory.PMonE.LinCount.lin_succ_last
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T19:17:27.976829+00:00
-- url     : https://prove2.me/submissions/1dd34f44-3093-4694-89f8-0edfba325301

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
theorem _root_.solution (K : ℕ) (M : ℕ → Matrix m m F) (k : ℕ) (Y : Fin (K + 1) × m → F) (a : m) :
    (lin K M (k + 1)).mulVec Y (Fin.last K, a) = (M (k + 1 + K)).mulVec (fun b => Y (Fin.last K, b)) a := by
  simp only [Matrix.mulVec, dotProduct, lin, Fintype.sum_prod_type]
  rw [Finset.sum_eq_single (Fin.last K)]
  · simp
  · intro j _ hj
    simp [hj]
  · simp
end GlobalTheory.PMonE.LinCount
