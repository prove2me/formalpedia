-- Prove2me | solution 1 for GlobalTheory.LinkSec.gs_spMap_germAt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T03:08:12.61552+00:00
-- url     : https://prove2.me/submissions/80c4b03a-cbb9-464c-be37-02e45a8d1d80

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Jets_JetsOnCopiesCompatibleFrames
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_TwistBCPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_CartesianLiftThreeCompProjection
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DivCalc
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_FBIdJet
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_IsLawOfOfMatch
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_ValSerGermFnVal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_ExistsUniqueNormPrim
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_GsSpMapGermAt
import Theorems.Thm_P2M_GlobalTheory_LinkSec_gs_to__eq_9fe3707169ce

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation Formalism.MainNotions.ModuliIntegralCharts.H1.GSt
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.MainNotions.ModuliIntegralCharts.H1.BoxTuple Formalism.MainNotions.ModuliIntegralCharts.H1.BidegreeTwoJet GlobalTheory GlobalTheory.PowGerm
open ReciprocityTheory.ChartRestriction.G.TB (colM dAct)
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.LinkSec
namespace GlobalTheory.LinkSec
theorem _root_.solution {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (y : Sp B) (a : A) :
    gs (Geo.Tor.spMap f) y ⊤ (toΓ A a) = germAt B y (f a) := by
  have e := gs_pull (𝟙 _) (Geo.Tor.spMap f) y ⊤ trivial (toΓ A a)
  rw [Category.id_comp] at e
  refine e.symm.trans (Eq.trans ?_ (gs_toΓ_eq y _))
  exact congrArg (gs (𝟙 _) y ⊤)
    (congrArg (fun φ => φ.hom a) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom f))).symm
end GlobalTheory.LinkSec
