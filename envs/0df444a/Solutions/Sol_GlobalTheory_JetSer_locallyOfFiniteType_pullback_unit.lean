-- Prove2me | solution 1 for GlobalTheory.JetSer.locallyOfFiniteType_pullback_unit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T18:24:49.807853+00:00
-- url     : https://prove2.me/submissions/95ba1ed3-8db2-446d-a069-aa22a9aacb20

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_DegUnif
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsGrpPullback
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwoChartAtlas_TwoChartSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_ExistsToJetEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_RepJetAugCompTrunc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_PredMulSumPadicValNatFactorialAddCardLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_ExistsUniversalThickeningStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_LocallyOfFiniteTypePullbackUnit

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
open GlobalTheory GlobalTheory.JetSer
namespace GlobalTheory.JetSer
theorem _root_.solution {S : Scheme.{0}} (G : Over S) [GrpObj G] [LocallyOfFiniteType G.hom]
    (f : G ⟶ G) : LocallyOfFiniteType (pullback f η[G]).hom := by
  have h1 : LocallyOfFiniteType (f.left ≫ G.hom) := by rw [Over.w f]; infer_instance
  have h2 : LocallyOfFiniteType f.left := locallyOfFiniteType_of_comp f.left G.hom
  have h3 := (IsPullback.of_hasPullback f η[G]).map (Over.forget S)
  have h4 : LocallyOfFiniteType (pullback.snd f η[G]).left :=
    MorphismProperty.of_isPullback (P := @LocallyOfFiniteType) h3 h2
  have h5 : (pullback f η[G]).hom = (pullback.snd f η[G]).left := by
    rw [← Over.w (pullback.snd f η[G])]
    exact Category.comp_id _
  rw [h5]
  exact h4
end GlobalTheory.JetSer
