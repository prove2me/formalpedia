-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.PeriodMapPresentation.IsPeriodMap.map_smul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:43:48.239812+00:00
-- url     : https://prove2.me/submissions/e047b6ff-8e8d-4393-b397-092023ca2deb

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
namespace IsPeriodMap
theorem _root_.solution {D : Datum H} {g : ℕ} {ty : Fin g → (E →+* ℂ)} {P : D.La →+ (Fin g → ℂ)}
    (h : IsPeriodMap D ty P) (a : 𝓞 E) (x : D.La) : P (a • x) = tyAct ty a (P x) := by
  obtain ⟨-, J, -, φ, h1, -, h3⟩ := h
  rw [← h1, ← h1, ← h3]
  rfl
end IsPeriodMap
end GlobalTheory.IndefiniteRowSideFullHecke.PeriodMapPresentation
