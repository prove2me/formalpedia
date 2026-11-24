-- Prove2me | solution 1 for GlobalTheory.interior_closure_eq_empty_of_isConstructible_of_disjoint_dense
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:01:27.946899+00:00
-- url     : https://prove2.me/submissions/ea375783-7049-491c-b521-1333d09f83e1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_FiniteOfIsClosedTorusZariskiOfPowEqOne
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsIsAffineOpenDisjointImageOfIsConstructible
import Theorems.Thm_GlobalTheory_interior_frontier_preimage_of_isConstructible


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
theorem _root_.solution
    {Y : Type*} [TopologicalSpace Y] {D Sg : Set Y} (hD : Topology.IsConstructible D)
    (hSg : Dense Sg) (h : Disjoint D Sg) : interior (closure D) = ∅ := by
  have h1 : interior (frontier D) = ∅ :=
    interior_frontier_preimage_of_isConstructible (f := id) continuous_id hD
  have h2 : interior D = ∅ :=
    interior_eq_empty_iff_dense_compl.2 (hSg.mono h.subset_compl_left)
  rwa [frontier, h2, Set.diff_empty] at h1
end GlobalTheory
