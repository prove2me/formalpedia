-- Prove2me | solution 1 for GlobalTheory.AnVal.JetAlg.map_res_val
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T04:42:12.716393+00:00
-- url     : https://prove2.me/submissions/b3b4a490-2574-48fc-bab3-fc03a17ae696

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaValues_ThConst
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ThExprUniqOfChartIndep2
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_HolJetD
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_JetRdMulInvPow

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
attribute [local instance] Over.cartesianMonoidalCategory
open scoped ContDiff
open GlobalTheory GlobalTheory.AnVal GlobalTheory.AnVal.JetAlg
namespace GlobalTheory.AnVal.JetAlg
theorem _root_.solution {X : Scheme.{0}} {U V : X.Opens} (h : V ≤ U) (h' : ⊤ ≤ V) (u : Γ(X, U)ˣ) :
    (X.presheaf.map (homOfLE h').op).hom (Semi.res h u).val =
      (X.presheaf.map (homOfLE (h'.trans h)).op).hom u.val := by
  unfold Semi.res
  show (X.presheaf.map (homOfLE h).op ≫ X.presheaf.map (homOfLE h').op).hom u.val = _
  rw [← Functor.map_comp]
  rfl
end GlobalTheory.AnVal.JetAlg
