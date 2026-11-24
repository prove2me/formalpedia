-- Prove2me | solution 1 for GlobalTheory.PeriodCompare.mem_domain
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T19:42:40.933324+00:00
-- url     : https://prove2.me/submissions/118d9582-ce2f-43d8-9906-74f1adef3022

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_CMModuli_PeriodMapPresentation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsEquivOfSumEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsIsDerivAt0NotIsDerivAlong
import Theorems.Thm_GlobalTheory_PeriodCompare_finiteDimensional
import Theorems.Thm_GlobalTheory_PeriodCompare_trace_eq_of_pos
import Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_PeriodMapPresentation_domain_nonempty


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.PeriodCompare
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding IsTypeFn IsThetaFrame
open GlobalTheory.IndefiniteRowSideFullHecke.PeriodMapPresentation hiding IsTypeFn IsThetaFrame
open scoped TensorProduct Topology
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
namespace GlobalTheory.PeriodCompare
theorem _root_.solution (D : Datum H) {J : ℝ ⊗[ℤ] D.La →ₗ[ℝ] ℝ ⊗[ℤ] D.La} (h1 : ∀ x, J (J x) = -x)
    (h2 : ∀ a : 𝓞 E, J ∘ₗ actR D a = actR D a ∘ₗ J)
    (h3 : ∀ x y, D.EF.baseChange ℝ (J x) (J y) = D.EF.baseChange ℝ x y)
    (h4 : ∀ x, x ≠ 0 → 0 < D.EF.baseChange ℝ (J x) x) : J ∈ domain D := by
  obtain ⟨_, _⟩ := finiteDimensional D
  obtain ⟨J', k1, k2, -, k4, k5⟩ := domain_nonempty D
  refine ⟨h1, h2, h3, h4, fun a => ?_⟩
  rw [trace_eq_of_pos _ J J' _ h1 k1 h4 k4 (h2 a) (k2 a), k5]
end GlobalTheory.PeriodCompare
