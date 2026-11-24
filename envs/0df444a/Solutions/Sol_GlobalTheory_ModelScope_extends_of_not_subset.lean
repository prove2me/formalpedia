-- Prove2me | solution 1 for GlobalTheory.ModelScope.extends_of_not_subset
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T18:58:25.538787+00:00
-- url     : https://prove2.me/submissions/c01317e8-d8b4-4337-aa23-0a7c767c8bf2

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_PushInvertible
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_ModuliSurvey_RangeJSubsetAbLocus

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.ModelScope
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}
namespace GlobalTheory.ModelScope
theorem _root_.solution (Y : Model Xo c β) (U : Y.X.Opens) (hU : ¬ Set.range Y.j ⊆ (U : Set Y.X))
    (σ : 𝟙_ (Over (Xo.XF c)) ⟶ Y.oF.t.G) : Y.Extends U σ := by
  refine ⟨U.ι ≫ (show Y.X ⟶ Y.t.G.left from (η[Y.t.G]).left), ?_, fun j' hj => (hU ?_).elim⟩
  · have h : (show Y.X ⟶ Y.t.G.left from (η[Y.t.G]).left) ≫ Y.t.G.hom = 𝟙 _ := Over.w (η[Y.t.G])
    rw [Category.assoc, h, Category.comp_id]
  · rintro _ ⟨x, rfl⟩
    rw [← hj]
    exact (j' x).2
end GlobalTheory.ModelScope
