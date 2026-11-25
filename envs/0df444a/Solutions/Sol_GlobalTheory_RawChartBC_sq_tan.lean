-- Prove2me | solution 1 for GlobalTheory.RawChartBC.sq_tan
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T13:51:04.696185+00:00
-- url     : https://prove2.me/submissions/634a73b4-36cf-482c-a6d4-38a353c07956

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ThShort
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_CIndBC
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ThExprUniqOfChartIndep2
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermCut
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_JetSubstPCompJetBC
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_IsRawChartBaseChangeJetPoints
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_jetTan_comp_jetBC


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
open GlobalTheory GlobalTheory.RawChartBC
open ReciprocityTheory.ChartRestriction.G.PullbackSections
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l}
variable {S S' : Type} [CommRing S] [CommRing S'] (ψ : S →+* S') (x0 : Sp S ⟶ Xo.X)
namespace GlobalTheory.RawChartBC
theorem _root_.solution (d : ℕ) (ℓ : Fin 1 × Fin d) :
    homAt (spMap ψ ≫ x0) (jetTan ℓ : Jet S' (Fin 1 × Fin d) (0 + 1) →ₐ[S'] DualNumber S') ≫ rjBC ψ x0 d 1 1 =
      dualPtMap ψ x0 ≫ homAt x0 (jetTan ℓ : Jet S (Fin 1 × Fin d) (0 + 1) →ₐ[S] DualNumber S) := by
  apply Over.OverMorphism.ext
  show spMap _ ≫ spMap (jetBC ψ _ (0 + 1)) = spMap (dualMap ψ) ≫ spMap _
  rw [spMap_spMap, spMap_spMap]
  exact congrArg spMap (jetTan_comp_jetBC ψ ℓ 0)
end GlobalTheory.RawChartBC
