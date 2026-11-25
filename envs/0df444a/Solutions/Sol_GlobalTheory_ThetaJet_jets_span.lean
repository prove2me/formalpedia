-- Prove2me | solution 1 for GlobalTheory.ThetaJet.jets_span
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T16:50:33.890089+00:00
-- url     : https://prove2.me/submissions/6c540712-5819-4d22-b287-f3729654b0a2

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_TBNFinal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_LevelThreeSeparatesTangents
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaValues_MemAnalyticAtZeroOfEventuallyDifferentiableAt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_PredMulSumPadicValNatFactorialAddCardLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ExistsTranslateJetNeZero
import Theorems.Thm_GlobalTheory_ThetaJet_spans_mod_pow_succ
import Theorems.Thm_GlobalTheory_ThetaJet_exists_sec_ne_zero
import Theorems.Thm_GlobalTheory_ThetaJet_mul_mem_jets
import Theorems.Thm_GlobalTheory_ThetaJet_jets_three
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
theorem _root_.solution {Y : GT ι} {θ : EuclideanSpace ℂ ι → ℂ} (hθ : θ ∈ Y.Sec 1) (h0 : θ ≠ 0)
    {r : ℕ} (hr : 2 ≤ r) (D : ℕ) (x : MvPowerSeries ι ℂ) :
    ∃ s ∈ jets Y (r + 3 * D), x - s ∈ germIdeal ι ℂ ^ (D + 1) := by
  induction D generalizing x with
  | zero =>
    obtain ⟨F, hF, hF0⟩ := exists_sec_ne_zero hθ h0 hr
    refine ⟨(MvPowerSeries.constantCoeff x / F 0) • _, Submodule.smul_mem _ _ ⟨F, hF, rfl⟩, ?_⟩
    refine mem_germIdeal_pow_iff.2 fun d hd => ?_
    obtain rfl : d = 0 := by simpa [Finsupp.degree_eq_zero_iff] using hd
    simp [MvPowerSeries.smul_eq_C_mul, hF0]
  | succ D ih =>
    exact spans_mod_pow_succ _ (jets Y 3) _ _ D (jets_three hθ h0) ih
      (fun a ha s hs => mul_mem_jets ha hs) x
end GlobalTheory.ThetaJet
