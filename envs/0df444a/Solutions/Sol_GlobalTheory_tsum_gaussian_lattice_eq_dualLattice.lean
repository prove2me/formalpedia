-- Prove2me | solution 1 for GlobalTheory.tsum_gaussian_lattice_eq_dualLattice
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:13:32.465914+00:00
-- url     : https://prove2.me/submissions/f1862165-2204-424a-afd4-8d0729f3d8d5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_ExistsLinearIndependentNormLeSuccMin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_LatticeFourierOfContDiffFiniteDimensional
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_SummableLatticeExpNegPiMulNormSqDiv
import Theorems.Thm_GlobalTheory_poisson_gaussian_lattice_cos

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
theorem _root_.solution {t : ℝ} (ht : 0 < t) :
    ∑' x : L, Real.exp (-π * t * ‖(x : E)‖ ^ 2) =
      (ZLattice.covolume L)⁻¹ * t ^ (-(finrank ℝ E / 2 : ℝ)) *
        ∑' y : dualLattice L, Real.exp (-π * ‖(y : E)‖ ^ 2 / t) := by
  simpa only [add_zero, inner_zero_right, mul_zero, Real.cos_zero, mul_one] using
    (poisson_gaussian_lattice_cos L ht 0).2
end GlobalTheory
