-- Prove2me | solution 1 for GlobalTheory.RawChartGermBC.base_rjBC
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T19:52:54.333363+00:00
-- url     : https://prove2.me/submissions/8d87ef33-4724-4dee-9947-74b87564e547

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
import Theorems.Thm_GlobalTheory_RawChartGermBC_spMap_comp_eq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_jetBC_mk


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
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l}
variable {S S' : Type} [CommRing S] [CommRing S'] (ψ : S →+* S') (x0 : Sp S ⟶ Xo.X) (d : ℕ)
namespace GlobalTheory.RawChartGermBC
theorem _root_.solution (m n : ℕ) :
    rjBase (spMap ψ ≫ x0) d m n ≫ ptBC ψ x0 = rjBC ψ x0 d m n ≫ rjBase x0 d m n := by
  apply Over.OverMorphism.ext
  unfold rjBC ptBC rjBase
  simp only [Over.comp_left, Over.homMk_left]
  refine spMap_comp_eq _ _ _ _ (RingHom.ext fun a => ?_)
  simp only [RingHom.comp_apply]
  rw [show algebraMap S (Jet S (Fin n × Fin d) m) a = Ideal.Quotient.mk _ (MvPolynomial.C a) from rfl,
    PullbackSections.jetBC_mk, MvPolynomial.map_C]
  rfl
end GlobalTheory.RawChartGermBC
