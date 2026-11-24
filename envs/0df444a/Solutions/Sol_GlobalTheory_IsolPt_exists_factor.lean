-- Prove2me | solution 1 for GlobalTheory.IsolPt.exists_factor
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T17:56:15.514409+00:00
-- url     : https://prove2.me/submissions/ed336f8e-af89-4fe9-9d00-9692cfac12ce

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_DegUnif
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsGrpPullback
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwoChartAtlas_TwoChartSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_HasChartsOfForallIsAffineOpen
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_ExistsUniversalThickening

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
open GlobalTheory GlobalTheory.IsolPt
namespace GlobalTheory.IsolPt
theorem _root_.solution {k A B : Type} [CommRing k] [CommRing A] [Algebra k A] [CommRing B] [Algebra k B]
    {X : Over (Spec (CommRingCat.of k))} (x : Chart.sp (R₀ := k) A ⟶ X) (v : Chart.sp (R₀ := k) B ⟶ X)
    [IsOpenImmersion v.left] (hsub : Set.range x.left ⊆ Set.range v.left) :
    ∃ ψ : B →ₐ[k] A, x = Chart.spMap ψ ≫ v := by
  have hl := IsOpenImmersion.lift_fac v.left _ hsub
  obtain ⟨ψ, hψ⟩ := NatFun.spMap_surjective (k := k) (A := B) (B := A)
    (Over.homMk (IsOpenImmersion.lift v.left _ hsub) (by
      rw [← Over.w v, ← Category.assoc, hl, Over.w]))
  refine ⟨ψ, Over.OverMorphism.ext ?_⟩
  rw [hψ]
  exact hl.symm
end GlobalTheory.IsolPt
