-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.PeriodMapPresentation.domain_nonempty
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T17:40:18.588336+00:00
-- url     : https://prove2.me/submissions/d2f7d5c4-0804-4289-bce9-c2aba0c7e0f8

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Clauses
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_CMModuli_PeriodMapPresentation

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.PeriodMapPresentation
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped TensorProduct Topology
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
namespace GlobalTheory.IndefiniteRowSideFullHecke.PeriodMapPresentation
theorem _root_.solution (D : Datum H) : (domain D).Nonempty := by
  obtain ⟨J, h1, h2, h3, h4⟩ := D.dom
  have key := fun a : 𝓞 E => h4 a (actR D a) (sigTrace D a) (fun x => rfl) rfl
  refine ⟨J, h1, fun a => (key a).1, h2, h3, fun a => ?_⟩
  rw [(key a).2.1, (key a).2.2]
  apply Complex.ext
  · simp
  · simp; ring
end GlobalTheory.IndefiniteRowSideFullHecke.PeriodMapPresentation
