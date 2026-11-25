-- Prove2me | solution 1 for GlobalTheory.MaxCusp.Zb_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T18:07:23.279786+00:00
-- url     : https://prove2.me/submissions/36f7b545-237d-4248-adcf-1e5f78f3cb2d

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FourierCoefficientSupportHolds
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FixedPointImaginarySpan
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_IsHermOfMemLZ
import Theorems.Thm_GlobalTheory_MaxCusp_zmat_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_FourierCoefficientMatrices_zmat_zero


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
theorem _root_.solution (u : Fin d → Fin r → E) (x : Frame X.Ψ r) : Zb X u 0 x = x := by
  funext τ
  show zmat X u 0 τ * mat x τ = mat x τ
  rw [zmat_zero, Matrix.one_mul]
end GlobalTheory.MaxCusp
