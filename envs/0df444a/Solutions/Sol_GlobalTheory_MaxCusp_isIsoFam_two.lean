-- Prove2me | solution 1 for GlobalTheory.MaxCusp.isIsoFam_two
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T18:04:34.824019+00:00
-- url     : https://prove2.me/submissions/c97b9e5f-f808-4334-888c-a1d3202fbc5e

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
theorem _root_.solution (G : Matrix (Fin r) (Fin r) E) (u : Fin 2 → Fin r → E) :
    IsIsoFam G u ↔ IsIsoPair G u := Iff.rfl
end GlobalTheory.MaxCusp
