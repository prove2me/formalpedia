-- Prove2me | solution 1 for GlobalTheory.summable_norm_lattice_cexp_gaussian
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:36:54.151443+00:00
-- url     : https://prove2.me/submissions/c735fc17-9d3e-4f53-b430-2c740143ca28

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_ExistsLinearIndependentNormLeSuccMin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_LatticeFourierOfContDiffFiniteDimensional
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_SummableLatticeExpNegPiMulNormSqDiv
import Theorems.Thm_GlobalTheory_summable_lattice_exp_neg_mul_norm_add_sq
import Theorems.Thm_GlobalTheory_norm_cexp_neg_pi_mul_norm_sq_add

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
theorem _root_.solution {b : ℂ} (hb : 0 < b.re) (w u : E) :
    Summable fun x : L ↦ ‖Complex.exp (-π * b * ‖(x : E) + u‖ ^ 2 +
      2 * π * Complex.I * ⟪w, (x : E) + u⟫)‖ := by
  simp only [norm_cexp_neg_pi_mul_norm_sq_add]
  exact summable_lattice_exp_neg_mul_norm_add_sq L (mul_pos Real.pi_pos hb) u
end GlobalTheory
