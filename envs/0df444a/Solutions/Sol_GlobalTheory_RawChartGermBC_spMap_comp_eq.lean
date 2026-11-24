-- Prove2me | solution 1 for GlobalTheory.RawChartGermBC.spMap_comp_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:27:33.260258+00:00
-- url     : https://prove2.me/submissions/367630c2-fced-4b99-95b7-e1e3b811b849

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ThShort
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_CIndBC
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ThExprUniqOfChartIndep2
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermCut
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_JetSubstPCompJetBC
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_LBPull
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermDVal
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermBPrim
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_RawChartBaseChangeRigGerm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp


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
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.RawChartGermBC
variable {S S' : Type} [CommRing S] [CommRing S'] (ψ : S →+* S')
namespace GlobalTheory.RawChartGermBC
theorem _root_.solution {A B C D : Type} [CommRing A] [CommRing B] [CommRing C] [CommRing D]
    (f : A →+* B) (g : B →+* D) (f' : A →+* C) (g' : C →+* D) (h : g.comp f = g'.comp f') :
    (spMap g ≫ spMap f : Sp D ⟶ Sp A) = spMap g' ≫ spMap f' := by
  simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp, h]
end GlobalTheory.RawChartGermBC
