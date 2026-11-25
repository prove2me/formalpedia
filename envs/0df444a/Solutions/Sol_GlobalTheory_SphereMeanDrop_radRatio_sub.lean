-- Prove2me | solution 1 for GlobalTheory.SphereMeanDrop.radRatio_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T16:43:56.744327+00:00
-- url     : https://prove2.me/submissions/67237c08-4e80-4975-9211-800750854cb6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_PointHeight
import Definitions.Def_ReciprocityTheory_SemistableReduction_TorusL2CauchyInequality
import Definitions.Def_ReciprocityTheory_SemistableReduction_SJCoreA
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousFirstCoords
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MeasurePreservingPolarGaussianProbabilityComplexStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_GaussianRadialLawProbabilityLogIntegrableMeanStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_GaussianFirstCoordsMeasurePreservingStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_BlockSphereProbZeroSetEqZeroStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsMultiHomogeneousRenameCastLE
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_radRatio_odd


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.SphereMeanDrop
open MeasureTheory Set MvPolynomial ReciprocityTheory.MultiplicativeHeights
namespace GlobalTheory.SphereMeanDrop
theorem _root_.solution {N n : ℕ} (hN : 0 < N) (hn : 0 < n) :
    radK (2 * N - 1) / radJ (2 * N - 1) - radK (2 * n - 1) / radJ (2 * n - 1) =
      ((harmonic (N - 1) : ℝ) - (harmonic (n - 1) : ℝ)) / 2 := by
  obtain ⟨a, rfl⟩ : ∃ a, N = a + 1 := ⟨N - 1, by omega⟩
  obtain ⟨b, rfl⟩ : ∃ b, n = b + 1 := ⟨n - 1, by omega⟩
  have e1 : 2 * (a + 1) - 1 = 2 * a + 1 := by omega
  have e2 : 2 * (b + 1) - 1 = 2 * b + 1 := by omega
  rw [e1, e2, radRatio_odd, radRatio_odd]
  simp only [Nat.add_sub_cancel]
  ring
end GlobalTheory.SphereMeanDrop
