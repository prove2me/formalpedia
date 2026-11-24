-- Prove2me | solution 1 for GlobalTheory.HermFrame.form_self
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:47:41.895197+00:00
-- url     : https://prove2.me/submissions/c78aa19a-0573-49ce-a531-03cb54639c46

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
theorem _root_.solution {H : Matrix n n ℂ} (hH : H.PosSemidef) (v : n → ℂ) :
    form H v v = ((gnorm H v ^ 2 : ℝ) : ℂ) := by
  obtain ⟨R, h1, h2⟩ := exists_root hH
  rw [h1, h2, inner_self_eq_norm_sq_to_K]; simp
end GlobalTheory.HermFrame
