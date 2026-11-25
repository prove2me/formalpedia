-- Prove2me | solution 1 for GlobalTheory.RiemannThetaModel.not_isSiegel_zero_nat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T18:06:17.464417+00:00
-- url     : https://prove2.me/submissions/cf8007a2-935a-4c96-9398-ee3687ce81e0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_ExistsEventuallyNormRiemannThetaTermLe
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Change
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsLieBasis
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_NormSqRiemannThetaMulExpPeriodic
import Theorems.Thm_GlobalTheory_isSiegel_diagonal_iff


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Matrix
open scoped Real
noncomputable section
open GlobalTheory GlobalTheory.RiemannThetaModel
variable {ι : Type*} [Fintype ι]
namespace GlobalTheory.RiemannThetaModel
theorem _root_.solution : ¬ IsSiegel (0 : Matrix ℕ ℕ ℂ) := by
  have : (0 : Matrix ℕ ℕ ℂ) = diagonal fun _ => 0 := by simp
  rw [this, isSiegel_diagonal_iff]
  simp
end GlobalTheory.RiemannThetaModel
