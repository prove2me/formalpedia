-- Prove2me | solution 1 for GlobalTheory.PMonE.LinCount.lin_zero_cast
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:36:24.488182+00:00
-- url     : https://prove2.me/submissions/7b019407-dc3c-4a7d-9814-4ebac348473e

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
    (lin K M 0).mulVec Y (i.castSucc, a) = - Y (i.succ, a) := by
  simp only [Matrix.mulVec, dotProduct]
  rw [Finset.sum_eq_single (i.succ, a)]
  · simp [lin, (Fin.castSucc_lt_last i).ne]
  · rintro ⟨j, b⟩ _ hne
    have : ¬ ((j : ℕ) = i + 1 ∧ a = b) := by
      rintro ⟨h1, rfl⟩
      exact hne (by congr 1; exact Fin.ext (by simpa using h1))
    simp [lin, (Fin.castSucc_lt_last i).ne, this]
  · simp
end GlobalTheory.PMonE.LinCount
