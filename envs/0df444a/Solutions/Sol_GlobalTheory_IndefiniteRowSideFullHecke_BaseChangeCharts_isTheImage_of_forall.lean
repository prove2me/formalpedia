-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.BaseChangeCharts.isTheImage_of_forall
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:49:41.646611+00:00
-- url     : https://prove2.me/submissions/ed7d5c03-dc3e-4d9a-942e-d9145c51b1fd

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_DegExp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GtPtBridgeSt
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_UniformisationCharts_BaseChangeCharts

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
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.BaseChangeCharts
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]
variable (F : Type) [Field F] [Algebra (FractionRing R) F]
namespace GlobalTheory.IndefiniteRowSideFullHecke.BaseChangeCharts
theorem _root_.solution {U : Unif I D A G} {k : ℕ} (hk : 1 ≤ k) {p : QkPt D.toPre F k}
    {x : TFK (R := R) F ⟶ A.A}
    (h : ∀ w : Ident U.toUnifPre, QkToAk D.toPre F A k (ExpandsF F U.toUnifPre w k) p x) :
    IsTheImage F U k p x :=
  ⟨hk, Classical.arbitrary _, h _⟩
end GlobalTheory.IndefiniteRowSideFullHecke.BaseChangeCharts
