-- Prove2me | solution 1 for GlobalTheory.ThetaJet.TwistedLaw.mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T16:15:11.140731+00:00
-- url     : https://prove2.me/submissions/215db760-3145-4a2c-9944-a5f5ee0c7f56

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_TBNFinal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_LevelThreeSeparatesTangents
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaValues_MemAnalyticAtZeroOfEventuallyDifferentiableAt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_PredMulSumPadicValNatFactorialAddCardLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ExistsTranslateJetNeZero
import Theorems.Thm_GlobalTheory_ThetaJet_Hf_add_left
import Theorems.Thm_GlobalTheory_constDerivEval_X
import Theorems.Thm_GlobalTheory_lineDerivList_nil
import Theorems.Thm_GlobalTheory_lineDerivList_zero
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
namespace TwistedLaw
theorem _root_.solution {Y : GT ι} {k l : ℕ} {c d : EuclideanSpace ℂ ι}
    {F G : EuclideanSpace ℂ ι → ℂ} (hF : TwistedLaw Y k c F) (hG : TwistedLaw Y l d G) :
    TwistedLaw Y (k + l) (c + d) (F * G) := by
  refine ⟨hF.1.mul hG.1, fun γ hγ v => ?_⟩
  simp only [Pi.mul_apply]
  rw [hF.2 γ hγ, hG.2 γ hγ, Hf_add_left]
  have e : ((k + l : ℕ) : ℂ) * Real.pi * Hf v γ + Real.pi * (Hf c γ + Hf d γ)
      + ((k + l : ℕ) : ℂ) * Real.pi * Hf γ γ / 2 =
      (k * Real.pi * Hf v γ + Real.pi * Hf c γ + k * Real.pi * Hf γ γ / 2) +
      (l * Real.pi * Hf v γ + Real.pi * Hf d γ + l * Real.pi * Hf γ γ / 2) := by
    push_cast; ring
  rw [e, Complex.exp_add (k * Real.pi * Hf v γ + Real.pi * Hf c γ + k * Real.pi * Hf γ γ / 2)]
  ring
end TwistedLaw
end GlobalTheory.ThetaJet
