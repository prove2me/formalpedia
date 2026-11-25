-- Prove2me | solution 1 for GlobalTheory.MaxCusp.continuous_Zb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T18:03:27.742563+00:00
-- url     : https://prove2.me/submissions/c41a2dd3-3a1c-479d-9d90-f00beb0e59cb

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FourierCoefficientSupportHolds
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FixedPointImaginarySpan
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_IsHermOfMemLZ

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.MaxCusp
open NumberField Complex MeasureTheory Matrix ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r d : ℕ}
variable (X : Data E r)
namespace GlobalTheory.MaxCusp
theorem _root_.solution (u : Fin d → Fin r → E) (y : Frame X.Ψ r) :
    Continuous fun b : X.Ψ → Fin d → Fin d → ℂ => Zb X u b y := by
  refine continuous_pi fun τ => ?_
  show Continuous fun b : X.Ψ → Fin d → Fin d → ℂ =>
    (zmat X u b τ * mat y τ : Matrix (Fin r) (Fin r) ℂ)
  refine Continuous.matrix_mul ?_ continuous_const
  refine continuous_pi fun a => continuous_pi fun j => ?_
  simp only [zmat, Matrix.of_apply]
  fun_prop
end GlobalTheory.MaxCusp
