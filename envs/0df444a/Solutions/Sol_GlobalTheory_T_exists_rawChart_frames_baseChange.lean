-- Prove2me | solution 1 for GlobalTheory.T.exists_rawChart_frames_baseChange
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T15:14:55.954428+00:00
-- url     : https://prove2.me/submissions/75176c57-651f-4005-90d9-9fce0963000b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ExistsRawChartFramesBaseChange
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ThShort
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_CIndBC
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ThExprUniqOfChartIndep2
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermCut
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ExistsRawChartFramesBaseChangeStatement
import Theorems.Thm_GlobalTheory_RawFrameBC_exists_frames


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
theorem _root_.solution : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (S S' : Type) [CommRing S] [CommRing S'] (ψ : S →+* S') (x0 : Sp S ⟶ Xo.X) (d : ℕ) (F : Fin d → MvPowerSeries (Fin 2 × Fin d) S) (act : 𝓞 E → Fin d → MvPowerSeries (Fin 1 × Fin d) S) (x : ∀ m, rjO x0 d m 1 ⟶ Xo.univ.t.G) (x' : ∀ m, rjO (spMap ψ ≫ x0) d m 1 ⟶ Xo.univ.t.G), (∀ m, x' m = rjBC ψ x0 d m 1 ≫ x m) → ∀ (e : ∀ m, RFrTy x0 d x m), (∀ m, (e m).IsGen) → ∃ e' : ∀ m, RFrTy (spMap ψ ≫ x0) d x' m, (∀ m, (e' m).IsGen) ∧ (∀ m, LB.Gen.Corr Xo.univ.t.PP.L _ _ _ _ (e' m) (LB.pullGen Xo.univ.t.PP.L (cφ ![rjpt x0 d x m (0 : Fin 2), rjpt x0 d x m (1 : Fin 2)]) (cε 2) (e m) (rjBC ψ x0 d m 2).left)) ∧ ∀ (m n' : ℕ) (φ : Fin 2 → Fin d → MvPolynomial (Fin n' × Fin d) S), LB.Gen.Corr Xo.univ.t.PP.L _ _ _ _ (rpe (spMap ψ ≫ x0) d x' e' m (fun i j => MvPolynomial.map ψ (φ i j))) (LB.pullGen Xo.univ.t.PP.L _ _ (rpe x0 d x e m φ) (rjBC ψ x0 d m n').left) := by
  first | exact @GlobalTheory.RawFrameBC.exists_frames | exact GlobalTheory.RawFrameBC.exists_frames | (intros; apply GlobalTheory.RawFrameBC.exists_frames <;> assumption)
end _root_.GlobalTheory.T
