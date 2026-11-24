-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SiegelND.Integ.Weyl.norm_ee
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T13:38:46.512678+00:00
-- url     : https://prove2.me/submissions/ec24f757-016c-483c-a352-bd18f8a9ab65

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SecondCountableHermC
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ContinuousSeminormDiffSLe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SiegelND GlobalTheory.CompanionTheory.SiegelND.Integ GlobalTheory.CompanionTheory.SiegelND.Integ.Weyl
open MeasureTheory
open scoped ComplexConjugate FourierTransform
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]
namespace GlobalTheory.CompanionTheory.SiegelND.Integ.Weyl
theorem _root_.solution (t : ℝ) : ‖ee t‖ = 1 := by
  have : 2 * (Real.pi : ℂ) * Complex.I * ((t : ℝ) : ℂ) = ((2 * Real.pi * t : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [ee, this, Complex.norm_exp_ofReal_mul_I]
end GlobalTheory.CompanionTheory.SiegelND.Integ.Weyl
