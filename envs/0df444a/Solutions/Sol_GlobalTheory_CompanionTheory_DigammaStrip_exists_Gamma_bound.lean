-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.DigammaStrip.exists_Gamma_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T12:26:28.257798+00:00
-- url     : https://prove2.me/submissions/18562056-5561-4045-8cb9-f949c4a419ab

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_LogDerivLFunctionStrip
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_LGrowthGamma
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_DigammaBoundVerticalStrip

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.DigammaStrip
namespace GlobalTheory.CompanionTheory.DigammaStrip
theorem _root_.solution :
    ∃ K : ℝ, 0 < K ∧ ∀ x : ℝ, 1 / 2 ≤ x → x ≤ 5 / 2 → Real.Gamma x ≤ K := by
  have hc : ContinuousOn Real.Gamma (Set.Icc (1 / 2) (5 / 2)) := fun x hx =>
    (Real.differentiableAt_Gamma (fun m h => by
      have h1 := hx.1
      have h2 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
      linarith)).continuousAt.continuousWithinAt
  obtain ⟨K, hK⟩ := isCompact_Icc.bddAbove_image hc
  exact ⟨max K 1, lt_max_of_lt_right one_pos,
    fun x h1 h2 => (hK ⟨x, ⟨h1, h2⟩, rfl⟩).trans (le_max_left _ _)⟩
end GlobalTheory.CompanionTheory.DigammaStrip
