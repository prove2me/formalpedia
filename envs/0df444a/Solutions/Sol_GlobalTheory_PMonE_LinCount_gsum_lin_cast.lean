-- Prove2me | solution 1 for GlobalTheory.PMonE.LinCount.gsum_lin_cast
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T19:34:03.796783+00:00
-- url     : https://prove2.me/submissions/43b55e25-8815-4222-bf94-a85ab8b91b43

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_MooreNorm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_AdditiveSystemIntegralSolutionCountOfOrderOne
import Theorems.Thm_GlobalTheory_PMonE_LinCount_lin_zero_cast
import Theorems.Thm_GlobalTheory_PMonE_LinCount_lin_one_cast
import Theorems.Thm_GlobalTheory_PMonE_LinCount_lin_two_cast

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
theorem _root_.solution (q K E : ℕ) (M : ℕ → Matrix m m F) (X : Fin (K + 1) × m → F) (i : Fin K) (a : m) :
    gsum q (E + 1) (lin K M) X (i.castSucc, a) = X (i.castSucc, a) ^ q - X (i.succ, a) := by
  simp only [gsum, Finset.sum_apply]
  rw [Finset.sum_range_succ', Finset.sum_range_succ']
  simp only [lin_two_cast, zero_add, lin_one_cast, lin_zero_cast]
  simp [sub_eq_add_neg]
end GlobalTheory.PMonE.LinCount
