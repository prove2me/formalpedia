-- Prove2me | solution 1 for GlobalTheory.locallyQuasiFinite_of_finite_fibres_closedPoints
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T15:09:36.334802+00:00
-- url     : https://prove2.me/submissions/f48aebdd-c388-4bcf-9315-d42785cbc232

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_FlatImageOfOverFractionFieldOfValuationRing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_BijectiveAlgebraMapIntegralClosureOfBirational
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_FiniteResidueFieldOfIsClosedOfLocallyOfFiniteTyp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_MemPadicAlgClValuationSubringIffNormLeOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_FiniteOfIsClosedOfFiniteInterClosedPoints
import Theorems.Thm_GlobalTheory_subset_of_isOpen_of_closedPoints
import Theorems.Thm_P2M_UpperTheory_Reformulated_B_Qk17_isPrecomplete_finite_module__f12f74bf6019


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
local notation "OO" p:max => (Valuation.valuationSubring (Valued.v : Valuation (PadicAlgCl p) NNReal))
local notation "cPt" p:max => (IsLocalRing.closedPoint (OO p) : Sp (OO p))
local notation "gPt" p:max => spMap (ValuationSubring.subtype (OO p))
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {Y X : Scheme.{0}} (f : Y ⟶ X)
    [LocallyOfFiniteType f] [JacobsonSpace Y]
    (h : ∀ y : Y, IsClosed ({y} : Set Y) → (f ⁻¹' {f y}).Finite) : LocallyQuasiFinite f := by
  rw [← Scheme.Hom.quasiFiniteLocus_eq_top_iff, eq_top_iff]
  refine subset_of_isOpen_of_closedPoints isOpen_univ f.quasiFiniteLocus.isOpen fun y hy _ ↦ ?_
  have : Finite (f.fiber (f y)) := (f.fiberHomeo (f y)).finite_iff.mpr (h y hy)
  exact Scheme.Hom.quasiFiniteAt_iff_isOpen_singleton_asFiber.mpr (isOpen_discrete _)
end GlobalTheory
