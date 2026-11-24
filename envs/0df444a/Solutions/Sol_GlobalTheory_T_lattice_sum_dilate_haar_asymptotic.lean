-- Prove2me | solution 1 for GlobalTheory.T.lattice_sum_dilate_haar_asymptotic
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:36:10.378963+00:00
-- url     : https://prove2.me/submissions/6a0e6054-ddb9-40f3-9cb9-4a9f47d21a59

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_LatticeSumDilateHaarAsymptotic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_LatticeSumDilateHaarAsymptoticStatement
import Theorems.Thm_GlobalTheory_lattice_sum_dilate_haar


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
theorem _root_.solution : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] (μ : Measure V) [μ.IsAddHaarMeasure] (L : Submodule ℤ V) [DiscreteTopology L] [IsZLattice ℝ L] (f : V → ℂ), ContDiff ℝ ∞ f → HasCompactSupport f → ∀ A : ℕ, ∃ C : ℝ, ∀ (x₀ : V) (t : ℝ), 0 < t → t ≤ 1 → ‖∑' l : L, f (t • ((l : V) + x₀)) - (∫ x, f x ∂μ) / ((ZLattice.covolume L μ * t ^ Module.finrank ℝ V : ℝ) : ℂ)‖ ≤ C * t ^ A := by
  first | exact @GlobalTheory.lattice_sum_dilate_haar | exact GlobalTheory.lattice_sum_dilate_haar | (intros; apply GlobalTheory.lattice_sum_dilate_haar <;> assumption)
end _root_.GlobalTheory.T
