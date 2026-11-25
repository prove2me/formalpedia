-- Prove2me | solution 1 for GlobalTheory.T.exists_etale_chart_smooth_algebra_local_point
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T18:18:51.713459+00:00
-- url     : https://prove2.me/submissions/be5e94ba-4012-4433-8b8e-78aebd6af400

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsEtaleChartSmoothAlgebraLocalPoint
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_EtChart
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsEtaleChartSmoothAlgebraLocalPointStatement
import Theorems.Thm_GlobalTheory_DenseSec_exists_etChart


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (R : Type) [CommRing R] [IsLocalRing R] (A : Type) [CommRing A] [Algebra R A] [Algebra.Smooth R A] (ε : A →ₐ[R] R), ∃ (g : ℕ) (t : Fin g → A) (h : A), (∀ i, ε (t i) = 0) ∧ IsUnit (ε h) ∧ GlobalTheory.DenseSec.EtChart R A t h := by
  first | exact @GlobalTheory.DenseSec.exists_etChart | exact GlobalTheory.DenseSec.exists_etChart | (intros; apply GlobalTheory.DenseSec.exists_etChart <;> assumption)
end _root_.GlobalTheory.T
