-- Prove2me | solution 1 for GlobalTheory.norm_mul_sub_one_le_of_norm_sub_one_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:35:07.980192+00:00
-- url     : https://prove2.me/submissions/642724f5-b773-47b9-9959-90f0d8e9eab9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UltrametricMatrixInvNearOneStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_MatrixMulEntryNormLeUltrametricStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CongruenceSubgroupsGLPadic
import Theorems.Thm_GlobalTheory_T_norm_mul_apply_le_of_ultrametric


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {E : Type} [NormedField E] [IsUltrametricDist E]
    {n : Type} [Fintype n] [DecidableEq n] (X Y : Matrix n n E) (t : ℝ) (h0 : 0 ≤ t) (h1 : t ≤ 1)
    (hX : ∀ i j, ‖(X - 1) i j‖ ≤ t) (hY : ∀ i j, ‖(Y - 1) i j‖ ≤ t) :
    ∀ i j, ‖(X * Y - 1) i j‖ ≤ t := by
  intro i j
  have hXY : X * Y - 1 = (X - 1) + (Y - 1) + (X - 1) * (Y - 1) := by
    simp only [sub_mul, mul_sub, mul_one, one_mul]; abel
  have hp := GlobalTheory.T.norm_mul_apply_le_of_ultrametric E n (X - 1) (Y - 1) t t h0 h0 hX hY i j
  have htt : t * t ≤ t := by nlinarith
  rw [hXY, Matrix.add_apply, Matrix.add_apply]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ (hp.trans htt))
  exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hX i j) (hY i j))
end GlobalTheory
