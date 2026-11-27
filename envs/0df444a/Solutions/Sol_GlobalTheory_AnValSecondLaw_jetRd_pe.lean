-- Prove2me | solution 1 for GlobalTheory.AnValSecondLaw.jetRd_pe
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T06:20:39.128845+00:00
-- url     : https://prove2.me/submissions/2d033c01-e25a-4010-bfe4-e860c5c915b5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaValues_ThConst
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ThExprUniqOfChartIndep2
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_IsHolFamPullbackLiftOfCommonBase
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_CubicalReadingOneAnalyticFrame
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_JetRdMulInvPow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_CorrOfJetsOfAnalyticFrameProducts
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_AppLESpMapJetPt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_CmFrameJetPointsAreExponentialJets
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_JetReadingLinearSubstitutionPoints
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_AnalyticFrameSecondPartialLawTrivial
import Theorems.Thm_GlobalTheory_AnValSecondLaw_subst_X
import Theorems.Thm_GlobalTheory_JetLinSub_jetRd_linSubst


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
open GlobalTheory GlobalTheory.AnValSecondLaw
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal
attribute [local instance] Over.cartesianMonoidalCategory
open scoped ContDiff
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} [Algebra c.F ℂ] {y : FrPt Xo c ℂ} {g : ℕ} {ty : Fin g → (E →+* ℂ)}
  {el : Fin g ≃ Lt1 Dw} (Φ : AnPt y g ty el)
namespace GlobalTheory.AnValSecondLaw
theorem _root_.solution (e : ∀ m, FrTy y g Φ.jx m) (he : Φ.IsAnE e) (m : ℕ) {n' : ℕ}
    (φ : Fin 2 → Fin g → MvPolynomial (Fin n' × Fin g) ℂ)
    (B : Fin 2 → (Fin n' → Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ))
    (h : ∀ i j, (Ideal.Quotient.mk _ (φ i j - MvPolynomial.C (MvPolynomial.constantCoeff (φ i j))) :
      Jet ℂ (Fin n' × Fin g) m) = jetN m (fun w => B i w j)) :
    Φ.toAnFr.JetRd m _ _ (pe y g Φ.jx e m φ) (fun k => psumL 2 g k ∘ₗ LinearMap.pi B) :=
  GlobalTheory.JetLinSub.jetRd_linSubst _ _ _ _ g Φ.toAnFr 2 n' m (LinearMap.pi B) (fun p => φ p.1 p.2)
    (fun p => (subst_X m _ p).trans (h p.1 p.2)) _ _ _ _ _ (he m).2
end GlobalTheory.AnValSecondLaw
