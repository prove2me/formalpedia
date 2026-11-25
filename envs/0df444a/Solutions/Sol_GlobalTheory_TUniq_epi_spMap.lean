-- Prove2me | solution 1 for GlobalTheory.TUniq.epi_spMap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T15:09:03.473377+00:00
-- url     : https://prove2.me/submissions/9f21f2e1-13cb-444a-9f2d-b7c535b160de

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_FiniteHomogeneousInf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsLiftClosedImmersionOfDense
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsReducedAlgebraOfSmoothOfIsNoetherianRing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsCompatOfLocal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
noncomputable section
open GlobalTheory GlobalTheory.TUniq
variable {o : Type} [CommRing o] {g k : ℕ} {J : Type} {b : TBase o k} {S S' : Scheme.{0}} {s : S ⟶ Sp o} {s' : S' ⟶ Sp o}
namespace GlobalTheory.TUniq
theorem _root_.solution {K Ω : Type} [Field K] [Field Ω] (i : K →+* Ω) : Epi (spMap i) := by
  have : Flat (spMap i) := by
    refine (HasRingHomProperty.Spec_iff (P := @Flat)).2 ?_
    letI := i.toAlgebra
    exact (inferInstance : Module.Flat K Ω)
  have : Surjective (spMap i) := ⟨fun p => ⟨(default : PrimeSpectrum Ω), Subsingleton.elim (α := PrimeSpectrum K) _ _⟩⟩
  exact Flat.epi_of_flat_of_surjective _
end GlobalTheory.TUniq
