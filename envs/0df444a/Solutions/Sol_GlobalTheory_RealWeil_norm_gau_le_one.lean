-- Prove2me | solution 1 for GlobalTheory.RealWeil.norm_gau_le_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T18:12:00.165106+00:00
-- url     : https://prove2.me/submissions/faed15a9-7829-482b-8482-ca093281b6dc

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousFourierGau
import Theorems.Thm_GlobalTheory_RealWeil_norm_gau

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Complex Matrix
open scoped RealInnerProductSpace ContDiff Real FourierTransform
open GlobalTheory GlobalTheory.RealWeil
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] {B : Type} [NormedAddCommGroup B] [NormedSpace ℂ B]
namespace GlobalTheory.RealWeil
theorem _root_.solution (u : V) : ‖gau u‖ ≤ 1 := by
  rw [norm_gau, Real.exp_le_one_iff]
  have := Real.pi_pos
  nlinarith [sq_nonneg ‖u‖]
end GlobalTheory.RealWeil
