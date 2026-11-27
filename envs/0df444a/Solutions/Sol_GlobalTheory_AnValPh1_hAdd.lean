-- Prove2me | solution 1 for GlobalTheory.AnValPh1.hAdd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T05:35:57.948262+00:00
-- url     : https://prove2.me/submissions/5483d17b-680d-4dfc-bcc2-482ba0b7b158

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
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_FBIdJet_mk_trunc_coe
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_FBIdJet_psTrunc_eq
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_GermD_jetMap_mk


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
namespace GlobalTheory.AnValPh1
theorem _root_.solution {n g : ℕ} (m : ℕ) (a b : Fin n) (hab : a ≠ b) (j : Fin g) :
    Ideal.Quotient.mk (orig ℂ (Fin n × Fin g) ^ (m + 1))
      (psIn g m ![a, b] (addF ℂ g j) -
        MvPolynomial.C (MvPolynomial.constantCoeff (psIn g m ![a, b] (addF ℂ g j)))) =
      Ideal.Quotient.mk _ (∑ i ∈ ({a, b} : Finset (Fin n)), MvPolynomial.X (i, j)) := by
  have hc : MvPolynomial.constantCoeff (psTrunc m (addF ℂ g j)) = 0 := by
    rw [FBIdJet.psTrunc_eq, MvPolynomial.constantCoeff_eq, MvPowerSeries.coeff_truncTotal _ (by simp),
      MvPowerSeries.coeff_zero_eq_constantCoeff_apply]
    simp [addF]
  have ha : (addF ℂ g j : MvPowerSeries (Fin 2 × Fin g) ℂ) =
      ((MvPolynomial.X ((0 : Fin 2), j) + MvPolynomial.X ((1 : Fin 2), j) : MvPolynomial (Fin 2 × Fin g) ℂ) :
        MvPowerSeries (Fin 2 × Fin g) ℂ) := by simp [addF]
  rw [psIn, MvPolynomial.constantCoeff_rename, hc, map_zero, sub_zero, Finset.sum_pair hab]
  have h1 := GermD.jetMap_mk (m := m) (fun p : Fin 2 × Fin g => (MvPolynomial.X (![a, b] p.1, p.2) :
    MvPolynomial (Fin n × Fin g) ℂ)) (fun _ => X_mem_orig _)
  have h2 : ∀ P : MvPolynomial (Fin 2 × Fin g) ℂ, MvPolynomial.rename (fun p : Fin 2 × Fin g => (![a, b] p.1, p.2)) P =
      MvPolynomial.aeval (fun p : Fin 2 × Fin g => (MvPolynomial.X (![a, b] p.1, p.2) :
        MvPolynomial (Fin n × Fin g) ℂ)) P := fun P => by
    rw [MvPolynomial.rename_eq_aeval]; rfl
  rw [h2, ← h1, ha, FBIdJet.psTrunc_eq, FBIdJet.mk_trunc_coe, h1]
  simp
end GlobalTheory.AnValPh1
