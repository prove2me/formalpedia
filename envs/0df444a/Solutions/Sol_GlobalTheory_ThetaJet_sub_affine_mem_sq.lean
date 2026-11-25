-- Prove2me | solution 1 for GlobalTheory.ThetaJet.sub_affine_mem_sq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T16:15:27.361873+00:00
-- url     : https://prove2.me/submissions/c146bfc9-f39b-4796-90a7-ceb72c91f075

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_TBNFinal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_LevelThreeSeparatesTangents
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaValues_MemAnalyticAtZeroOfEventuallyDifferentiableAt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_PredMulSumPadicValNatFactorialAddCardLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ExistsTranslateJetNeZero
import Theorems.Thm_GlobalTheory_constDerivEval_X
import Theorems.Thm_GlobalTheory_lineDerivList_nil
import Theorems.Thm_GlobalTheory_lineDerivList_zero
import Theorems.Thm_GlobalTheory_mem_germIdeal_pow_iff
import Theorems.Thm_GlobalTheory_pderivEval_X
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.constDerivEval_X
attribute [local simp] GlobalTheory.lineDerivList_nil
attribute [local simp] GlobalTheory.lineDerivList_zero
attribute [local simp] GlobalTheory.pderivEval_X



set_option autoImplicit false
open Complex ReciprocityTheory.ChartRestriction.G.I2 Filter Topology
open GlobalTheory
open GlobalTheory.ThetaJet
variable {ι : Type} [Fintype ι]
namespace GlobalTheory.ThetaJet
theorem _root_.solution {σ : Type*} [Fintype σ] (x : MvPowerSeries σ ℂ) :
    x - (MvPowerSeries.constantCoeff x • (1 : MvPowerSeries σ ℂ) +
      ∑ i, MvPowerSeries.coeff (Finsupp.single i 1) x • (MvPowerSeries.X i : MvPowerSeries σ ℂ))
      ∈ germIdeal σ ℂ ^ 2 := by
  classical
  refine mem_germIdeal_pow_iff.2 fun d hd => ?_
  by_cases h : d = 0
  · subst h
    simp
  · obtain ⟨j, rfl⟩ : ∃ j, d = Finsupp.single j 1 := by
      have h1 : d.degree = 1 := by
        have : d.degree ≠ 0 := by rwa [Ne, Finsupp.degree_eq_zero_iff]
        omega
      have : d ∈ Set.range fun a => Finsupp.single a 1 := by
        rw [Finsupp.range_single_one]; exact h1
      obtain ⟨j, hj⟩ := this
      exact ⟨j, hj.symm⟩
    simp [MvPowerSeries.coeff_one, MvPowerSeries.coeff_X, Finsupp.single_left_inj]
end GlobalTheory.ThetaJet
