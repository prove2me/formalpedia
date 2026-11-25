-- Prove2me | solution 1 for GlobalTheory.MaxCusp.Zb_Zb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T18:00:33.127467+00:00
-- url     : https://prove2.me/submissions/7a9c0142-4003-487d-a62f-ee4e5519bd28

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FourierCoefficientSupportHolds
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FixedPointImaginarySpan
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_IsHermOfMemLZ
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_Data_zmat_mul


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
    (b b' : X.Ψ → Fin d → Fin d → ℂ) (x : Frame X.Ψ r) :
    Zb X u b (Zb X u b' x) = Zb X u (b + b') x := by
  funext τ
  show zmat X u b τ * (zmat X u b' τ * mat x τ) = zmat X u (b + b') τ * mat x τ
  rw [← Matrix.mul_assoc, zmat_mul X u hu]
end GlobalTheory.MaxCusp
