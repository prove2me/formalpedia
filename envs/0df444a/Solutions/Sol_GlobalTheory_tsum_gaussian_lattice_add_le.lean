-- Prove2me | solution 1 for GlobalTheory.tsum_gaussian_lattice_add_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T04:42:36.243985+00:00
-- url     : https://prove2.me/submissions/97201c57-89f5-425c-8c29-e1d7c945ba32

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_ExistsLinearIndependentNormLeSuccMin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_LatticeFourierOfContDiffFiniteDimensional
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_SummableLatticeExpNegPiMulNormSqDiv
import Theorems.Thm_GlobalTheory_summable_lattice_exp_neg_pi_mul_norm_sq_div
import Theorems.Thm_GlobalTheory_poisson_gaussian_lattice_cos
import Theorems.Thm_GlobalTheory_tsum_gaussian_lattice_eq_dualLattice

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Module Set
open scoped RealInnerProductSpace Real FourierTransform
noncomputable section
open GlobalTheory
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
  (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
local notation "e[" t "]" => Complex.exp (2 * (π : ℂ) * Complex.I * ((t : ℝ) : ℂ))
namespace GlobalTheory
theorem _root_.solution {t : ℝ} (ht : 0 < t) (u : E) :
    ∑' x : L, Real.exp (-π * t * ‖(x : E) + u‖ ^ 2) ≤
      ∑' x : L, Real.exp (-π * t * ‖(x : E)‖ ^ 2) := by
  obtain ⟨h1, h2⟩ := poisson_gaussian_lattice_cos L ht u
  have hpos := ZLattice.covolume_pos L volume
  rw [h2, tsum_gaussian_lattice_eq_dualLattice L ht]
  refine mul_le_mul_of_nonneg_left (h1.tsum_le_tsum (fun y ↦ ?_)
    (summable_lattice_exp_neg_pi_mul_norm_sq_div _ ht)) (by positivity)
  exact mul_le_of_le_one_right (Real.exp_pos _).le (Real.cos_le_one _)
end GlobalTheory
