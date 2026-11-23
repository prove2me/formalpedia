-- Prove2me | solution 1 for GlobalTheory.HermFrame.norm_form_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:13:48.140989+00:00
-- url     : https://prove2.me/submissions/36efdfdb-3adf-406f-b46c-76d7550630c3

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
namespace GlobalTheory.HermFrame
theorem _root_.solution {H : Matrix n n ℂ} (hH : H.PosSemidef) (v w : n → ℂ) :
    ‖form H v w‖ ≤ gnorm H v * gnorm H w := by
  obtain ⟨R, h1, h2⟩ := exists_root hH
  rw [h1, h2, h2, mul_comm]; exact norm_inner_le_norm _ _
end GlobalTheory.HermFrame
