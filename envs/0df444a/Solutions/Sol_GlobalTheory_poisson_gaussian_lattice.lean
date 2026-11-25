-- Prove2me | solution 1 for GlobalTheory.poisson_gaussian_lattice
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:01:17.808802+00:00
-- url     : https://prove2.me/submissions/e3ff0347-9e0b-40c9-b256-801b91a2ee11

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_ExistsLinearIndependentNormLeSuccMin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_LatticeFourierOfContDiffFiniteDimensional
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_SummableLatticeExpNegPiMulNormSqDiv
import Theorems.Thm_GlobalTheory_summable_lattice_exp_neg_mul_norm_add_sq
import Theorems.Thm_GlobalTheory_poisson_cexp_gaussian_lattice

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
    (Summable fun x : L ↦ Real.exp (-π * t * ‖(x : E) + u‖ ^ 2)) ∧
    (Summable fun y : dualLattice L ↦ ‖(Real.exp (-π * ‖(y : E)‖ ^ 2 / t) : ℂ) *
      Complex.exp (2 * π * Complex.I * ⟪(y : E), u⟫)‖) ∧
    ((∑' x : L, Real.exp (-π * t * ‖(x : E) + u‖ ^ 2) : ℝ) : ℂ) =
      (((ZLattice.covolume L)⁻¹ * t ^ (-(finrank ℝ E / 2 : ℝ)) : ℝ) : ℂ) *
        ∑' y : dualLattice L, (Real.exp (-π * ‖(y : E)‖ ^ 2 / t) : ℂ) *
          Complex.exp (2 * π * Complex.I * ⟪(y : E), u⟫) := by
  obtain ⟨-, h2, h3⟩ := poisson_cexp_gaussian_lattice L (b := t) (by simpa using ht) 0 u
  refine ⟨?_, ?_, ?_⟩
  · simpa only [neg_mul] using
      summable_lattice_exp_neg_mul_norm_add_sq L (mul_pos Real.pi_pos ht) u
  · simpa only [sub_zero, Complex.ofReal_exp, Complex.ofReal_div, Complex.ofReal_mul,
      Complex.ofReal_neg, Complex.ofReal_pow] using h2
  · rw [Complex.ofReal_mul, Complex.ofReal_cpow ht.le, Complex.ofReal_tsum]
    simp only [inner_zero_left, Complex.ofReal_zero, mul_zero, add_zero, sub_zero] at h3
    push_cast
    exact h3
end GlobalTheory
