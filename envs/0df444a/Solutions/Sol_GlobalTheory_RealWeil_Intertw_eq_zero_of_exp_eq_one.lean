-- Prove2me | solution 1 for GlobalTheory.RealWeil.Intertw.eq_zero_of_exp_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:23:14.525277+00:00
-- url     : https://prove2.me/submissions/772854df-d6aa-4002-b918-fdda10109ffe

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_RealMetaplecticRepresentation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsSchwartzTranslate
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_GaussianSchwartz
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IntertwiningSymplecticAndGroupLaw

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.RealWeil MeasureTheory Complex
open scoped SchwartzMap Matrix Real RealInnerProductSpace
open GlobalTheory GlobalTheory.RealWeil GlobalTheory.RealWeil.Intertw
variable {l : Type} [Fintype l]
namespace GlobalTheory.RealWeil.Intertw
theorem _root_.solution (D : ℝ) (h : ∀ r : ℝ, exp (((π * (r * D) : ℝ) : ℂ) * I) = 1) : D = 0 := by
  by_contra hD
  have := h D⁻¹
  rw [inv_mul_cancel₀ hD, mul_one, Complex.exp_pi_mul_I] at this
  norm_num at this
end GlobalTheory.RealWeil.Intertw
