-- Prove2me | solution 1 for GlobalTheory.RawChartBC.sq_trunc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T13:53:53.801795+00:00
-- url     : https://prove2.me/submissions/4ec5e4d3-ba97-46dd-a594-17889109e358

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ThShort
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_CIndBC
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ThExprUniqOfChartIndep2
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermCut
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_JetSubstPCompJetBC
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_IsRawChartBaseChangeJetPoints
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_jetTrunc_comp_jetBC


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
theorem _root_.solution (d m : ℕ) :
    homAt (spMap ψ ≫ x0) (jetTrunc : Jet S' (Fin 1 × Fin d) (m + 1) →ₐ[S'] Jet S' (Fin 1 × Fin d) m) ≫
        rjBC ψ x0 d (m + 1) 1 =
      rjBC ψ x0 d m 1 ≫ homAt x0 (jetTrunc : Jet S (Fin 1 × Fin d) (m + 1) →ₐ[S] Jet S (Fin 1 × Fin d) m) := by
  apply Over.OverMorphism.ext
  show spMap _ ≫ spMap (jetBC ψ _ (m + 1)) = spMap (jetBC ψ _ m) ≫ spMap _
  rw [spMap_spMap, spMap_spMap]
  exact congrArg spMap (jetTrunc_comp_jetBC ψ _ m)
end GlobalTheory.RawChartBC
