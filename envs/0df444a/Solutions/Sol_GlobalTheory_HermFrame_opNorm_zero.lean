-- Prove2me | solution 1 for GlobalTheory.HermFrame.opNorm_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:02:24.892831+00:00
-- url     : https://prove2.me/submissions/ca515ad4-8a66-4f87-9844-f20367bf28f7

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_MaIntEmpty
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_EventuallyDifferentiableAtOfContDiffAtTwo
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_LeTwoMulOfForallScale

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex ComplexConjugate
open scoped ComplexOrder MatrixOrder
noncomputable section
open GlobalTheory GlobalTheory.HermFrame
variable {m n l : Type*} [Fintype m] [Fintype n] [Fintype l]
variable {H : Matrix m m ℂ} {K : Matrix n n ℂ} {L : Matrix l l ℂ}
namespace GlobalTheory.HermFrame
theorem _root_.solution (H : Matrix m m ℂ) (K : Matrix n n ℂ) : opNorm H K 0 = 0 :=
  le_antisymm (opNorm_le_of_bound le_rfl fun v => by simp) (opNorm_nonneg _ _ _)
end GlobalTheory.HermFrame
