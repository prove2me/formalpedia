-- Prove2me | solution 1 for GlobalTheory.PowGerm.UnivPow.zV_pr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T01:05:31.765809+00:00
-- url     : https://prove2.me/submissions/885b46e8-d0da-4986-8999-e046b5b331c9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Jets_JetsOnCopiesCompatibleFrames
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_TwistBCPf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_UniversalJetsPowerProduct

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
open GlobalTheory GlobalTheory.PowGerm GlobalTheory.PowGerm.UnivPow
variable {V : Type} [CommRing V]
namespace GlobalTheory.PowGerm.UnivPow
theorem _root_.solution {G G' : Over (Sp V)} [GrpObj G] [GrpObj G'] {n d : ℕ} (pG : IsPowGrp G' G n)
    (xT : ∀ m, jOG (𝟙 (Sp V)) d m 1 ⟶ G) (m : ℕ) (i : Fin n) :
    zV pG xT m ≫ pG.pr i = Formalism.L2.Pj.homAt (𝟙 (Sp V)) (jetCopy d m i) ≫ xT m :=
  pG.lim.fac _ ⟨i⟩
end GlobalTheory.PowGerm.UnivPow
