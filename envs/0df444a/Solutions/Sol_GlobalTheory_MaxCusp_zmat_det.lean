-- Prove2me | solution 1 for GlobalTheory.MaxCusp.zmat_det
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T13:44:28.890819+00:00
-- url     : https://prove2.me/submissions/f169dfbf-1ff9-48a1-b676-1a97f69d0561

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FourierCoefficientSupportHolds
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FixedPointImaginarySpan
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_IsHermOfMemLZ
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_Data_Cm_mul_Am
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_Data_zmat_eq


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
theorem _root_.solution (u : Fin d → Fin r → E) (hu : ∀ i k, herm X.Gm (u i) (u k) = 0)
    (b : X.Ψ → Fin d → Fin d → ℂ) (τ : X.Ψ) : (zmat X u b τ).det = 1 := by
  rw [zmat_eq, Matrix.det_one_add_mul_comm, Cm_mul_Am X u hu, add_zero, Matrix.det_one]
end GlobalTheory.MaxCusp
