-- Prove2me | solution 1 for GlobalTheory.exists_isAffineOpen_disjoint_image_of_isConstructible_of_disjoint_dense
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:20:01.704972+00:00
-- url     : https://prove2.me/submissions/90f634ba-b9eb-4b0d-87c6-c2a1fa831268

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_FiniteOfIsClosedTorusZariskiOfPowEqOne
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsIsAffineOpenDisjointImageOfIsConstructible
import Theorems.Thm_GlobalTheory_interior_closure_eq_empty_of_isConstructible_of_disjoint_dense

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
theorem _root_.solution :
    ∀ (X S : Scheme.{0}) [IsIntegral S] [IsNoetherian S] (f : X ⟶ S) [LocallyOfFiniteType f] [QuasiCompact f] (C : Set X) (Sg : Set S), Topology.IsConstructible C → Dense Sg → Disjoint (f '' C) Sg → ∃ V : S.Opens, (V : Set S).Nonempty ∧ IsAffineOpen V ∧ Disjoint (f '' C) V := by
  intro X S _ _ f _ _ C Sg hC hSg h
  have hD : Topology.IsConstructible (f '' C) := f.isConstructible_image hC
  have h1 := interior_closure_eq_empty_of_isConstructible_of_disjoint_dense hD hSg h
  obtain ⟨x, hx⟩ : ((closure (f '' C))ᶜ).Nonempty :=
    (interior_eq_empty_iff_dense_compl.1 h1).nonempty
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVU⟩ :=
    S.isBasis_affineOpens.exists_subset_of_mem_open hx isClosed_closure.isOpen_compl
  refine ⟨V, ⟨x, hxV⟩, hV, ?_⟩
  exact Set.disjoint_left.2 fun y hy hyV => hVU hyV (subset_closure hy)
end GlobalTheory
