-- Prove2me | solution 1 for GlobalTheory.PMonE.norm_adjugate_le_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T19:34:08.590689+00:00
-- url     : https://prove2.me/submissions/bb9d6c2d-5af4-4680-9f02-22fd2dbc2cb3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_MooreNorm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_RowTEqRowS
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormalOfInvMul
import Theorems.Thm_GlobalTheory_PMonE_norm_det_le_one_of_entries

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.PMonE
open GlobalTheory GlobalTheory.PMonE
open Finset
namespace GlobalTheory.PMonE
theorem _root_.solution {F : Type} [NormedField F] [IsUltrametricDist F] {m : Type} [Fintype m]
    [DecidableEq m] (A : Matrix m m F) (hA : ∀ i j, ‖A i j‖ ≤ 1) (i j : m) : ‖A.adjugate i j‖ ≤ 1 := by
  rw [Matrix.adjugate_apply]
  refine norm_det_le_one_of_entries _ fun a b => ?_
  by_cases h : a = j
  · subst h
    rw [Matrix.updateRow_self]
    by_cases hb : b = i
    · subst hb; simp
    · simp [Pi.single_apply, hb]
  · rw [Matrix.updateRow_ne h]; exact hA a b
end GlobalTheory.PMonE
