-- Prove2me | solution 1 for GlobalTheory.T.zlattice_tsum_dilate_sub_integral_le_rapid
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:23:42.923848+00:00
-- url     : https://prove2.me/submissions/eeaa8076-a2c2-460d-855a-defdc66e1871

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ZlatticeTsumDilateSubIntegralLeRapid
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ZlatticeTsumDilateSubIntegralLeRapidStatement
import Theorems.Thm_GlobalTheory_latticeSum_dilate_sub_integral_le


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain NumberField.mixedEmbedding MeasureTheory Complex Classical
open scoped ContDiff nonZeroDivisors
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] (L : Submodule ℤ V) [DiscreteTopology L] [IsZLattice ℝ L] (f : V → ℂ), ContDiff ℝ ∞ f → HasCompactSupport f → ∀ A : ℕ, ∃ C : ℝ, ∀ (x₀ : V) (t : ℝ), 0 < t → t ≤ 1 → ‖∑' l : L, f (t • ((l : V) + x₀)) - (∫ x, f x) / ((ZLattice.covolume L * t ^ Module.finrank ℝ V : ℝ) : ℂ)‖ ≤ C * t ^ A := by
  first | exact @GlobalTheory.latticeSum_dilate_sub_integral_le | exact GlobalTheory.latticeSum_dilate_sub_integral_le | (intros; apply GlobalTheory.latticeSum_dilate_sub_integral_le <;> assumption)
end _root_.GlobalTheory.T
