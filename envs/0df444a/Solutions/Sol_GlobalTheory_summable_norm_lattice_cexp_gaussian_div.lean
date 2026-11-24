-- Prove2me | solution 1 for GlobalTheory.summable_norm_lattice_cexp_gaussian_div
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:36:55.01038+00:00
-- url     : https://prove2.me/submissions/14bac201-357c-49a1-8aa3-4dd5fb26259d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_ExistsLinearIndependentNormLeSuccMin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_LatticeFourierOfContDiffFiniteDimensional
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_SummableLatticeExpNegPiMulNormSqDiv
import Theorems.Thm_GlobalTheory_summable_lattice_exp_neg_mul_norm_add_sq
import Theorems.Thm_GlobalTheory_norm_cexp_neg_pi_mul_norm_sq_div

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
omit [MeasurableSpace E] [BorelSpace E] [IsZLattice ℝ L]
namespace GlobalTheory
theorem _root_.solution {b : ℂ} (hb : 0 < b.re) (w : E) :
    Summable fun y : L ↦ ‖Complex.exp (-π * ‖(y : E) - w‖ ^ 2 / b)‖ := by
  have hb0 : b ≠ 0 := by rintro rfl; simp at hb
  have hb' : 0 < b⁻¹.re := by
    rw [Complex.inv_re]; exact div_pos hb (Complex.normSq_pos.2 hb0)
  simp only [norm_cexp_neg_pi_mul_norm_sq_div, sub_eq_add_neg]
  exact summable_lattice_exp_neg_mul_norm_add_sq L (mul_pos Real.pi_pos hb') (-w)
end GlobalTheory
