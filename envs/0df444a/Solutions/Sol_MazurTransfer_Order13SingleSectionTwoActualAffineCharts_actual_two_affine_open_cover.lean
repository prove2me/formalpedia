-- Prove2me | solution 1 for MazurTransfer.Order13SingleSectionTwoActualAffineCharts.actual_two_affine_open_cover
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-17T06:45:01.783589+00:00
-- url     : https://prove2.me/submissions/ea5d388f-34f4-45cb-b878-7a7aa0e04f2e

/- Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the original first section complement and actual inverse finite-chart open cover the whole actual order-thirteen curve.
Named downstream consumers: actual chart overlap and unchanged integral FiniteMapData. Reuses the Proved public first-chart complement identity. -/
import Mathlib
import Definitions.Def_MazurTransfer_Order13FirstFiniteChartCanonicalOpen
import Definitions.Def_MazurTransfer_Order13InverseChartOpen
noncomputable section
universe u
open CategoryTheory AlgebraicGeometry
open MazurTorsion.XOneThirteenProjectiveCurve
open MazurTransfer
open MazurTransfer.Order13ActualPositiveInfinityComplement
open MazurTransfer.Order13InverseParameterFiniteAlgebra
namespace ActualTwoAffineOpenCoverPublicProof20261017
variable (R : Type u) [CommRing R]
theorem positiveInfinitySection_range_subset_inverseChart (h2 : IsUnit (2 : R)) :
    Set.range (Order13IntegralSections.positiveInfinitySection R).val ⊆
      (inverseChartOpen R : Set (curveScheme R)) := by
  rintro p ⟨a,rfl⟩
  right
  refine ⟨positiveInfinityPatchMorphism R h2 a, ?_⟩
  have he := positiveInfinityPatchMorphism_curve R h2
  exact congrArg (fun f : Spec (.of R) ⟶ curveScheme R => f a) he
end ActualTwoAffineOpenCoverPublicProof20261017
open ActualTwoAffineOpenCoverPublicProof20261017

theorem solution (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R]
    (h104 : IsUnit (104 : R)) : sectionComplementOpen R ⊔ inverseChartOpen R = ⊤ := by
  apply TopologicalSpace.Opens.ext
  ext p
  change (p ∈ sectionComplementOpen R ∨ p ∈ inverseChartOpen R) ↔ True
  constructor
  · intro _; trivial
  · intro _
    by_cases hp : p ∈ Set.range (Order13IntegralSections.positiveInfinitySection R).val
    · exact Or.inr (positiveInfinitySection_range_subset_inverseChart R (two_isUnit_of_104 R h104) hp)
    · left
      exact (Order13FirstFiniteChartFromPublicTheorem.mem_chartOpen_iff R h104 p).mpr hp
#print axioms solution
