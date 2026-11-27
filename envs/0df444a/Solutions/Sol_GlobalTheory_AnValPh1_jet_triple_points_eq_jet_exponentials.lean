-- Prove2me | solution 1 for GlobalTheory.AnValPh1.jet_triple_points_eq_jet_exponentials
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T06:15:24.553061+00:00
-- url     : https://prove2.me/submissions/3d67e5b1-646b-4100-b934-5f383d9b176a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaValues_ThConst
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ThExprUniqOfChartIndep2
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_CubicalReadingOneAnalyticFrameStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_IsHolFamPullbackLiftOfCommonBase
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_JetRdMulInvPow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_CorrOfJetsOfAnalyticFrameProductsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_AppLESpMapJetPt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_CmFrameJetPointsAreExponentialJets
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_JetReadingLinearSubstitutionPoints
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_AnalyticFrameFirstPartialLawTrivial
import Theorems.Thm_GlobalTheory_AnValPh1_lift_jet
import Theorems.Thm_GlobalTheory_AnVal_jetPts_jetMap


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
open GlobalTheory GlobalTheory.AnValPh1
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal
open scoped ContDiff
attribute [local instance] Over.cartesianMonoidalCategory
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} [Algebra c.F ℂ] {y : FrPt Xo c ℂ} {g : ℕ} {ty : Fin g → (E →+* ℂ)}
  {el : Fin g ≃ Lt1 Dw} (Φ : AnPt y g ty el)
namespace GlobalTheory.AnValPh1
theorem _root_.solution (m : ℕ) {n : ℕ} (a b d : jO y g m n ⟶ Xo.univ.t.G)
    (Λa Λb Λd : (Fin n → Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)) (ha : Φ.toAnFr.JetMap m a.left Λa)
    (hb : Φ.toAnFr.JetMap m b.left Λb) (hd : Φ.toAnFr.JetMap m d.left Λd) :
    ∃ hq : IsHolFam (fun v : Fin (n * g) → ℂ => (lift (Φ.e (Λa (colsOf n g v)))
      (lift (Φ.e (Λb (colsOf n g v))) (Φ.e (Λd (colsOf n g v))))).left),
      (lift a (lift b d)).left =
        spMap (renN n g m : Jet ℂ (Fin 1 × Fin (n * g)) m →+* Jet ℂ (Fin n × Fin g) m) ≫ jetPt _ hq m := by
  obtain ⟨h2, e2⟩ := ((GlobalTheory.AnVal.jetPts_jetMap E H Dw l Xo c y g ty el Φ n m).2.2.1 b d Λb Λd hb hd).2
  obtain ⟨h1, e1⟩ := ha
  exact lift_jet _ _ y.x a (lift b d) _ _ h1 h2 e1 e2
end GlobalTheory.AnValPh1
