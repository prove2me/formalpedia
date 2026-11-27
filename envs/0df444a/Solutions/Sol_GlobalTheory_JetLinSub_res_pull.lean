-- Prove2me | solution 1 for GlobalTheory.JetLinSub.res_pull
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T04:35:14.236739+00:00
-- url     : https://prove2.me/submissions/34c8a743-4768-47c3-b6c8-37054e26eecb

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaValues_ThConst
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ThExprUniqOfChartIndep2
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_AnHolFamOfHolTo
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_JetReadingLinearSubstitutionPoints

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
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal
open scoped ContDiff
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.JetLinSub
namespace GlobalTheory.JetLinSub
theorem _root_.solution {Y Z : Scheme.{0}} (s : Z ⟶ Y) (W : Y.Opens) (W' : Z.Opens) (h : ⊤ ≤ W) (h' : ⊤ ≤ W')
    (le : W' ≤ s ⁻¹ᵁ W) (x : Γ(Y, W)) :
    (Z.presheaf.map (homOfLE h').op).hom ((Z.presheaf.map (homOfLE le).op).hom ((s.app W).hom x)) =
      s.appTop.hom ((Y.presheaf.map (homOfLE h).op).hom x) := by
  obtain rfl : W = ⊤ := top_le_iff.1 h
  obtain rfl : W' = ⊤ := top_le_iff.1 h'
  rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, ← CommRingCat.comp_apply,
    ← Functor.map_comp]
  have e1 : Y.presheaf.map (homOfLE h).op = 𝟙 _ := Y.presheaf.map_id _
  have e2 : Z.presheaf.map ((homOfLE le).op ≫ (homOfLE h').op) = 𝟙 _ := Z.presheaf.map_id _
  rw [e1, e2]
  rfl
end GlobalTheory.JetLinSub
