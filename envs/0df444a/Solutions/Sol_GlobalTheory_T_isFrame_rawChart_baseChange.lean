-- Prove2me | solution 1 for GlobalTheory.T.isFrame_rawChart_baseChange
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T15:12:03.846811+00:00
-- url     : https://prove2.me/submissions/53293d15-58ce-4093-bc03-c67e14d320ab

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_IsFrameRawChartBaseChange
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ThShort
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_CIndBC
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ThExprUniqOfChartIndep2
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermCut
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_IsFrameRawChartBaseChangeStatement
import Theorems.Thm_GlobalTheory_isFrame_baseChange


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
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (S S' : Type) [CommRing S] [CommRing S'] (ψ : S →+* S') (x0 : Sp S ⟶ Xo.X) (d : ℕ) (F : Fin d → MvPowerSeries (Fin 2 × Fin d) S) (act : 𝓞 E → Fin d → MvPowerSeries (Fin 1 × Fin d) S) (x : ∀ m, rjO x0 d m 1 ⟶ Xo.univ.t.G) (x' : ∀ m, rjO (spMap ψ ≫ x0) d m 1 ⟶ Xo.univ.t.G), (∀ m, x' m = rjBC ψ x0 d m 1 ≫ x m) → ∀ (e : ∀ m, RFrTy x0 d x m) (e' : ∀ m, RFrTy (spMap ψ ≫ x0) d x' m), (∀ m, (e m).IsGen) → (∀ m, (e' m).IsGen) → (∀ m, LB.Gen.Corr Xo.univ.t.PP.L _ _ _ _ (e' m) (LB.pullGen Xo.univ.t.PP.L (cφ ![rjpt x0 d x m (0 : Fin 2), rjpt x0 d x m (1 : Fin 2)]) (cε 2) (e m) (rjBC ψ x0 d m 2).left)) → ∀ (ph1 ph2 : MvPowerSeries (Fin 3 × Fin d) S) (sy : MvPowerSeries (Fin 2 × Fin d) S) (ad : 𝓞 E → MvPowerSeries (Fin 2 × Fin d) S), RIsFrame x0 d x F act ph1 ph2 sy ad e → RIsFrame (spMap ψ ≫ x0) d x' (fun i => MvPowerSeries.map ψ (F i)) (fun a i => MvPowerSeries.map ψ (act a i)) (MvPowerSeries.map ψ ph1) (MvPowerSeries.map ψ ph2) (MvPowerSeries.map ψ sy) (fun a => MvPowerSeries.map ψ (ad a)) e' := by
  first | exact @GlobalTheory.isFrame_baseChange | exact GlobalTheory.isFrame_baseChange | (intros; apply GlobalTheory.isFrame_baseChange <;> assumption)
end _root_.GlobalTheory.T
