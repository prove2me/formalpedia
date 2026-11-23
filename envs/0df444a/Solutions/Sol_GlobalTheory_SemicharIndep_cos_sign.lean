-- Prove2me | solution 1 for GlobalTheory.SemicharIndep.cos_sign
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:52:41.229251+00:00
-- url     : https://prove2.me/submissions/76be67bf-da34-4a64-ac43-8126c1a998b7

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_TorusAtData
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainPointBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_ModerateCoefficientPositivity
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_TorusAtEpsIndep

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.I2
open GlobalTheory GlobalTheory.SemicharIndep
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
namespace GlobalTheory.SemicharIndep
theorem _root_.solution {s : ℝ} (hs : s = 1 ∨ s = -1) (k : ℤ) :
    Real.cos (Real.pi * (s * (((k : ℚ)) : ℝ))) = ((k.negOnePow : ℤ) : ℝ) := by
  have h := Real.cos_int_mul_pi k
  rw [← Int.cast_negOnePow] at h
  rcases hs with rfl | rfl
  · rw [← h]; congr 1; push_cast; ring
  · rw [← h, ← Real.cos_neg]; congr 1; push_cast; ring
end GlobalTheory.SemicharIndep
