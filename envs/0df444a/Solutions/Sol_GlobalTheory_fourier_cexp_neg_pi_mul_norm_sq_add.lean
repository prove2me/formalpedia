-- Prove2me | solution 1 for GlobalTheory.fourier_cexp_neg_pi_mul_norm_sq_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:57:44.950363+00:00
-- url     : https://prove2.me/submissions/6de97759-847b-4efb-89dc-4c58f5f2d8af

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_ExistsLinearIndependentNormLeSuccMin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_LatticeFourierOfContDiffFiniteDimensional
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_SummableLatticeExpNegPiMulNormSqDiv

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
theorem _root_.solution {b : ℂ} (hb : 0 < b.re) (w y : E) :
    𝓕 (fun v : E ↦ Complex.exp (-π * b * ‖v‖ ^ 2 + 2 * π * Complex.I * ⟪w, v⟫)) y =
      b ^ (-(finrank ℝ E / 2 : ℂ)) * Complex.exp (-π * ‖y - w‖ ^ 2 / b) := by
  have hb0 : b ≠ 0 := by rintro rfl; simp at hb
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have h := fourier_gaussian_innerProductSpace' (b := π * b)
    (by simpa using mul_pos Real.pi_pos hb) w y
  simp only [← neg_mul] at h
  rw [h, norm_sub_rev w y]
  congr 1
  · rw [div_mul_cancel_left₀ hπ, Complex.inv_cpow _ _ ?_, Complex.cpow_neg]
    intro harg
    exact absurd (Complex.arg_eq_pi_iff.1 harg).1 hb.le.not_gt
  · congr 1
    field_simp
end GlobalTheory
