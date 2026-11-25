-- Prove2me | solution 1 for MainStatements.BetaInf.gN_le_sN
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T04:10:04.269911+00:00
-- url     : https://prove2.me/submissions/38a5d100-de52-4886-8d7e-67b897dfa14a

import Definitions.Def_CompanionTheory_AutomorphicTheory_SchurLimitBounds_ZuckermanDuality_ZuckDualTOfZuckDual
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ContinuousMulMt
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_NormDiagonalEntryDilationGeneratorLeOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LowerSmoothStability_ExistsFinStableOfMemSSup
import Definitions.Def_CompanionTheory_AutomorphicTheory_KFiniteVectors_KDecay
import Theorems.Thm_MainStatements_BetaInf_sN_nonneg

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
theorem _root_.solution {k r : ℕ} (g : B.Mat k r) : B.gN g ≤ sN g := by
  unfold B.gN
  rw [Real.sqrt_le_left (sN_nonneg g)]
  unfold sN
  simp only [Complex.normSq_eq_norm_sq]
  calc ∑ i, ∑ j, ‖g i j‖ ^ 2 ≤ ∑ i, (∑ j, ‖g i j‖) ^ 2 :=
        Finset.sum_le_sum fun i _ => Finset.sum_sq_le_sq_sum_of_nonneg fun j _ => norm_nonneg _
    _ ≤ (∑ i, ∑ j, ‖g i j‖) ^ 2 :=
        Finset.sum_sq_le_sq_sum_of_nonneg fun i _ => Finset.sum_nonneg fun j _ => norm_nonneg _
end MainStatements.BetaInf
