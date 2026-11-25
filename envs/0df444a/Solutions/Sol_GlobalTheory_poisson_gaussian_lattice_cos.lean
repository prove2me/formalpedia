-- Prove2me | solution 1 for GlobalTheory.poisson_gaussian_lattice_cos
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:06:44.389807+00:00
-- url     : https://prove2.me/submissions/67fc9bf1-705d-46dd-8991-d0fb9135ee21

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_ExistsLinearIndependentNormLeSuccMin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_LatticeFourierOfContDiffFiniteDimensional
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_SummableLatticeExpNegPiMulNormSqDiv
import Theorems.Thm_GlobalTheory_poisson_gaussian_lattice

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
    (Summable fun y : dualLattice L ↦
      Real.exp (-π * ‖(y : E)‖ ^ 2 / t) * Real.cos (2 * π * ⟪(y : E), u⟫)) ∧
    ∑' x : L, Real.exp (-π * t * ‖(x : E) + u‖ ^ 2) =
      (ZLattice.covolume L)⁻¹ * t ^ (-(finrank ℝ E / 2 : ℝ)) *
        ∑' y : dualLattice L,
          Real.exp (-π * ‖(y : E)‖ ^ 2 / t) * Real.cos (2 * π * ⟪(y : E), u⟫) := by
  obtain ⟨-, h2, h3⟩ := poisson_gaussian_lattice L ht u
  have hre : ∀ y : dualLattice L, ((Real.exp (-π * ‖(y : E)‖ ^ 2 / t) : ℂ) *
      Complex.exp (2 * π * Complex.I * ⟪(y : E), u⟫)).re =
      Real.exp (-π * ‖(y : E)‖ ^ 2 / t) * Real.cos (2 * π * ⟪(y : E), u⟫) := fun y ↦ by
    rw [Complex.re_ofReal_mul, ← Complex.exp_ofReal_mul_I_re]
    congr 3
    push_cast
    ring
  have h4 := Complex.hasSum_re h2.of_norm.hasSum
  simp only [hre] at h4
  refine ⟨h4.summable, ?_⟩
  rw [h4.tsum_eq, ← Complex.re_ofReal_mul, ← h3, Complex.ofReal_re]
end GlobalTheory
