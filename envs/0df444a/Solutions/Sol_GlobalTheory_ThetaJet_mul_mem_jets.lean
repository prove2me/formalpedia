-- Prove2me | solution 1 for GlobalTheory.ThetaJet.mul_mem_jets
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T16:32:40.56674+00:00
-- url     : https://prove2.me/submissions/3549d78b-ff99-4ac5-b277-d100b539f044

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_TBNFinal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_LevelThreeSeparatesTangents
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaValues_MemAnalyticAtZeroOfEventuallyDifferentiableAt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_PredMulSumPadicValNatFactorialAddCardLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ExistsTranslateJetNeZero
import Theorems.Thm_GlobalTheory_ThetaJet_twistedLaw_zero_iff
import Theorems.Thm_GlobalTheory_ThetaJet_TwistedLaw_mul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex ReciprocityTheory.ChartRestriction.G.I2 Filter Topology
open GlobalTheory
open GlobalTheory.ThetaJet
variable {ι : Type} [Fintype ι]
namespace GlobalTheory.ThetaJet
theorem _root_.solution {Y : GT ι} {k l : ℕ} {x y : MvPowerSeries ι ℂ} (hx : x ∈ jets Y k)
    (hy : y ∈ jets Y l) : x * y ∈ jets Y (k + l) := by
  obtain ⟨F, hF, rfl⟩ := hx
  obtain ⟨G, hG, rfl⟩ := hy
  have h := ((twistedLaw_zero_iff Y k F).2 hF).mul ((twistedLaw_zero_iff Y l G).2 hG)
  rw [add_zero, twistedLaw_zero_iff] at h
  exact ⟨_, h, taylorDir_mul _ (analyticAt_of_differentiable hF.1 0)
      (analyticAt_of_differentiable hG.1 0)⟩
end GlobalTheory.ThetaJet
