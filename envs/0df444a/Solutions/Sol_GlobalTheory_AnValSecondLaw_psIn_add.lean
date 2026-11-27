-- Prove2me | solution 1 for GlobalTheory.AnValSecondLaw.psIn_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T05:34:39.923804+00:00
-- url     : https://prove2.me/submissions/8e527645-5d9c-4a9f-b601-c5e0b2d3eb3e

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
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_FBIdJet_mk_trunc_coe
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_FBIdJet_psTrunc_eq


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
namespace GlobalTheory.AnValSecondLaw
theorem _root_.solution {g n' : ℕ} (m : ℕ) (r : Fin 2 → Fin n') (j : Fin g) :
    (Ideal.Quotient.mk _ (psIn g m r (addF ℂ g j) - MvPolynomial.C (MvPolynomial.constantCoeff (psIn g m r (addF ℂ g j)))) :
      Jet ℂ (Fin n' × Fin g) m) =
      Ideal.Quotient.mk _ (MvPolynomial.X (r 0, j) + MvPolynomial.X (r 1, j)) := by
  have hc : MvPolynomial.constantCoeff (psTrunc m (addF ℂ g j)) = 0 := by
    rw [FBIdJet.psTrunc_eq, MvPolynomial.constantCoeff_eq, MvPowerSeries.coeff_truncTotal _ (by simp),
      MvPowerSeries.coeff_zero_eq_constantCoeff_apply]
    simp [addF]
  have ha : (addF ℂ g j : MvPowerSeries (Fin 2 × Fin g) ℂ) =
      ((MvPolynomial.X ((0 : Fin 2), j) + MvPolynomial.X ((1 : Fin 2), j) : MvPolynomial (Fin 2 × Fin g) ℂ) :
        MvPowerSeries (Fin 2 × Fin g) ℂ) := by simp [addF]
  rw [psIn, MvPolynomial.constantCoeff_rename, hc, map_zero, sub_zero]
  have key : ∀ P : MvPolynomial (Fin 2 × Fin g) ℂ,
      (Ideal.Quotient.mk _ (MvPolynomial.rename (fun p : Fin 2 × Fin g => (r p.1, p.2)) P) : Jet ℂ (Fin n' × Fin g) m) =
      jetMap (m := m) (fun p : Fin 2 × Fin g => MvPolynomial.X (r p.1, p.2)) (fun _ => X_mem_orig _)
        (Ideal.Quotient.mk _ P) := by
    intro P
    show _ = Ideal.Quotient.mk _ (MvPolynomial.aeval _ _)
    rw [MvPolynomial.rename_eq_aeval]
    rfl
  rw [key, ha, FBIdJet.psTrunc_eq, FBIdJet.mk_trunc_coe, ← key]
  simp
end GlobalTheory.AnValSecondLaw
