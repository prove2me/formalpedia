-- Prove2me | solution 1 for GlobalTheory.PMonE.norm_inv_le_one_of_det
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T19:51:43.752805+00:00
-- url     : https://prove2.me/submissions/e941d9b0-381b-4957-a85a-c8d7558a7747

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_MooreNorm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_RowTEqRowS
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormalOfInvMul
import Theorems.Thm_GlobalTheory_PMonE_norm_adjugate_le_one

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
    [DecidableEq m] (A : Matrix m m F) (hA : ∀ i j, ‖A i j‖ ≤ 1) (hd : ‖A.det‖ = 1) (i j : m) :
    ‖A⁻¹ i j‖ ≤ 1 := by
  rw [Matrix.inv_def, Ring.inverse_eq_inv', Matrix.smul_apply, smul_eq_mul, norm_mul, norm_inv, hd, inv_one, one_mul]
  exact norm_adjugate_le_one A hA i j
end GlobalTheory.PMonE
