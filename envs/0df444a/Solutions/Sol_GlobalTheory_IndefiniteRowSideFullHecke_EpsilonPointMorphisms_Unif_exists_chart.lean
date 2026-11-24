-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPointMorphisms.Unif.exists_chart
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T17:38:39.786795+00:00
-- url     : https://prove2.me/submissions/7e85eeba-f1f3-4746-8dc4-07c61cf5ac7f

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_TwoWeightEqOneAddRoot
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ThickTransComp
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_CMModuli_ExponentialDifferential

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
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped Real
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPointMorphisms
open GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPointMorphisms.Unif
variable {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (F : Unif A L g)
namespace GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPointMorphisms.Unif
theorem _root_.solution (z : Fin g → ℂ) : ∃ i, z ∈ pre F.exp (L.U i) := by
  have hx : (F.exp z).mor.base (default : PrimeSpectrum ℂ) ∈ (⨆ i, L.U i) := by
    rw [F.isLB.cover]; trivial
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hx
  refine ⟨i, fun p _ => ?_⟩
  have hp : p = (default : PrimeSpectrum ℂ) := Subsingleton.elim (α := PrimeSpectrum ℂ) _ _
  subst hp
  exact hi
end GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPointMorphisms.Unif
