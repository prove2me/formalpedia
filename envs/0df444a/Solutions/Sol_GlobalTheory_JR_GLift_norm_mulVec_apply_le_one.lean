-- Prove2me | solution 1 for GlobalTheory.JR.GLift.norm_mulVec_apply_le_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T17:59:51.517053+00:00
-- url     : https://prove2.me/submissions/fd00043e-c4c7-4404-8029-266ae6b8842f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormMulApplyLeOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnitIndicatorGLBlockGlBorderedConjugationActionI

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
noncomputable section
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.GLift
namespace GlobalTheory.JR.GLift
theorem _root_.solution {F : Type} [NormedField F] [IsUltrametricDist F] {n : ℕ}
    (A : Matrix (Fin n) (Fin n) F) (v : Fin n → F) (hA : ∀ i j, ‖A i j‖ ≤ 1) (hv : ∀ i, ‖v i‖ ≤ 1)
    (i : Fin n) : ‖(A *ᵥ v) i‖ ≤ 1 := by
  rw [Matrix.mulVec, dotProduct]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun k _ => ?_
  rw [norm_mul]
  exact mul_le_one₀ (hA i k) (norm_nonneg _) (hv k)
end GlobalTheory.JR.GLift
