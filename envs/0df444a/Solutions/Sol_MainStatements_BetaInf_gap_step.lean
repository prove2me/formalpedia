-- Prove2me | solution 1 for MainStatements.BetaInf.gap_step
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T04:10:04.910719+00:00
-- url     : https://prove2.me/submissions/13817092-9ac5-4da9-956e-125ebb4531ae

import Definitions.Def_CompanionTheory_AutomorphicTheory_SchurLimitBounds_ZuckermanDuality_ZuckDualTOfZuckDual
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ContinuousMulMt
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_NormDiagonalEntryDilationGeneratorLeOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LowerSmoothStability_ExistsFinStableOfMemSSup
import Definitions.Def_CompanionTheory_AutomorphicTheory_KFiniteVectors_KDecay

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MainStatements MainStatements.BetaInf
open Formalism.FourierDecayAlt PI.UpqRep Matrix CompanionTheory.LimBd.Main
open scoped InnerProductSpace
noncomputable section
namespace MainStatements.BetaInf
theorem _root_.solution {n : ℕ} {ε : Fin n → Bool} {μ : Fin n → ℝ} {h : ℝ} (hg : PI.ZuckTensor.GapAtLeast ε μ h)
    (s : Fin n) : PI.ZuckTensor.GapAtLeast ε (μ + Pi.single s 1) (h - 1) := by
  intro a b hab
  have h1 := hg a b hab
  have h2 : |(Pi.single s 1 : Fin n → ℝ) a - (Pi.single s 1 : Fin n → ℝ) b| ≤ 1 := by
    simp only [Pi.single_apply]
    split_ifs <;> simp
  have e : μ a - μ b = ((μ + Pi.single s 1 : Fin n → ℝ) a - (μ + Pi.single s 1 : Fin n → ℝ) b) -
      ((Pi.single s 1 : Fin n → ℝ) a - (Pi.single s 1 : Fin n → ℝ) b) := by
    simp only [Pi.add_apply]; ring
  rw [e] at h1
  linarith [abs_sub ((μ + Pi.single s 1 : Fin n → ℝ) a - (μ + Pi.single s 1 : Fin n → ℝ) b)
    ((Pi.single s 1 : Fin n → ℝ) a - (Pi.single s 1 : Fin n → ℝ) b)]
end MainStatements.BetaInf
