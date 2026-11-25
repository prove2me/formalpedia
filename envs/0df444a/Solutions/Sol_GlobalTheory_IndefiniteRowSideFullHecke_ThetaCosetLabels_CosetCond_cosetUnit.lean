-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.ThetaCosetLabels.CosetCond.cosetUnit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:55:41.141559+00:00
-- url     : https://prove2.me/submissions/f661fc6b-a377-4029-8712-efc8b12b46b5

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_CMModuli_ThetaCosetLabels

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.ThetaCosetLabels
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] MvPolynomial.gradedAlgebra
variable {g : ℕ}
namespace GlobalTheory.IndefiniteRowSideFullHecke.ThetaCosetLabels
namespace CosetCond
theorem _root_.solution {n N' : ℕ} {R : Type} [CommRing R] [IsLocalRing R] {v : Lab g (N' ^ 2) → R}
    (h : CosetCond n N' v) : CosetUnit n N' v := fun c => by
  by_contra hc
  have : Ideal.span (v '' {a | SameCoset n N' a c}) ≤ IsLocalRing.maximalIdeal R := by
    rw [Ideal.span_le]
    rintro _ ⟨a, ha, rfl⟩
    exact fun hu => hc ⟨a, ha, hu⟩
  rw [h c] at this
  exact (IsLocalRing.maximalIdeal.isMaximal R).ne_top (top_le_iff.1 this)
end CosetCond
end GlobalTheory.IndefiniteRowSideFullHecke.ThetaCosetLabels
