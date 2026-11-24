-- Prove2me | solution 1 for GlobalTheory.RawChartGermBC.aug_rjBC
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T19:52:53.741584+00:00
-- url     : https://prove2.me/submissions/5f8e81f9-3d2c-49bc-b860-15326a7857d2

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
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_jetAug_comp_jetBC


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
    (Formalism.L2.Pj.homAt (spMap ψ ≫ x0) (jetAug : Jet S' (Fin n × Fin d) m →ₐ[S'] S')).left ≫ (rjBC ψ x0 d m n).left =
      spMap ψ ≫ (Formalism.L2.Pj.homAt x0 (jetAug : Jet S (Fin n × Fin d) m →ₐ[S] S)).left := by
  unfold rjBC Formalism.L2.Pj.homAt
  simp only [Over.homMk_left]
  exact spMap_comp_eq _ _ _ _ (PullbackSections.jetAug_comp_jetBC ψ (Fin n × Fin d) m)
end GlobalTheory.RawChartGermBC
