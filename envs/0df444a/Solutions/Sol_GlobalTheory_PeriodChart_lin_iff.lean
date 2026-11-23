-- Prove2me | solution 1 for GlobalTheory.PeriodChart.lin_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:41:51.470023+00:00
-- url     : https://prove2.me/submissions/526571e8-8329-41a0-9236-3365280c44e9

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsContraction

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Matrix Module
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.PeriodChart
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {g : ℕ}
variable {D : Datum H} {ty : Fin g → (E →+* ℂ)}
namespace GlobalTheory.PeriodChart
theorem _root_.solution (P : D.La →+ (Fin g → ℂ)) :
    (∀ (a : 𝓞 E) x i, P (a • x) i = ty i (a : E) * P x i) ↔ ∀ (a : 𝓞 E) x, P (a • x) = dg ty a *ᵥ P x := by
  constructor
  · intro h a x
    funext i
    rw [h]
    simp only [dg, Matrix.mulVec_diagonal]
  · intro h a x i
    rw [h]
    simp only [dg, Matrix.mulVec_diagonal]
end GlobalTheory.PeriodChart
