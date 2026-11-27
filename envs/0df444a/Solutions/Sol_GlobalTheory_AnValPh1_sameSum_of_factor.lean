-- Prove2me | solution 1 for GlobalTheory.AnValPh1.sameSum_of_factor
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T05:39:15.295801+00:00
-- url     : https://prove2.me/submissions/cd71f90c-1379-449d-b485-1bf390d45de7

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
theorem _root_.solution {X Y : Scheme.{0}} {K K' J : Type} [Fintype K] [Fintype K'] [Fintype J] [DecidableEq J]
    (φ : K → (Y ⟶ X)) (ε : K → ℤ) (φ' : K' → (Y ⟶ X)) (ε' : K' → ℤ) (F : J → (Y ⟶ X)) (σ : K → J) (σ' : K' → J)
    (h : ∀ k, φ k = F (σ k)) (h' : ∀ k, φ' k = F (σ' k))
    (hc : ∀ I, (∑ k, if σ k = I then ε k else 0) = ∑ k, if σ' k = I then ε' k else 0) :
    LB.SameSum φ ε φ' ε' := by
  classical
  have key : ∀ {K : Type} [Fintype K] (φ : K → (Y ⟶ X)) (ε : K → ℤ) (σ : K → J) (_ : ∀ k, φ k = F (σ k)) (ψ : Y ⟶ X),
      (∑ k, if φ k = ψ then ε k else 0) = ∑ I, if F I = ψ then (∑ k, if σ k = I then ε k else 0) else 0 := by
    intro K _ φ ε σ h ψ
    have : ∀ I, (if F I = ψ then (∑ k, if σ k = I then ε k else 0) else 0) =
        ∑ k, if σ k = I then (if φ k = ψ then ε k else 0) else 0 := by
      intro I
      split_ifs with hI
      · refine Finset.sum_congr rfl fun k _ => ?_
        split_ifs with h1 h2
        · rfl
        · exact absurd (by rw [h, h1, hI]) h2
        · rfl
      · refine (Finset.sum_eq_zero fun k _ => ?_).symm
        split_ifs with h1 h2
        · exact absurd (by rw [← h1, ← h, h2]) hI
        · rfl
        · rfl
    simp only [this]
    rw [Finset.sum_comm]
    simp
  intro ψ
  have a := key φ ε σ h ψ
  have b := key φ' ε' σ' h' ψ
  simp only [hc] at a
  convert a.trans b.symm
end GlobalTheory.AnValPh1
