-- Prove2me | solution 1 for GlobalTheory.IsSiegel.integral_cexp_quadratic
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:12:42.917861+00:00
-- url     : https://prove2.me/submissions/bc4fc3f7-4f45-4d0b-a409-29e6b20a1d2c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_ExistsEventuallyNormRiemannThetaTermLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_SummableLatticeExpNegPiMulNormSqDiv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsEqTransposeMulDiagonalMul
import Theorems.Thm_GlobalTheory_IsSiegel_exists_integral_cexp_quadratic

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Matrix MeasureTheory
open scoped Real
noncomputable section
open GlobalTheory
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
namespace GlobalTheory
namespace IsSiegel
theorem _root_.solution {σ : Matrix ι ι ℂ} (h : IsSiegel σ) (w : ι → ℂ) :
    ∫ x : ι → ℝ, cexp (2 * π * I * (((fun i => (x i : ℂ)) ⬝ᵥ (σ *ᵥ fun i => (x i : ℂ))) / 2 +
        (fun i => (x i : ℂ)) ⬝ᵥ w)) =
      siegelGaussIntegral σ * cexp (-(π * I) * (w ⬝ᵥ (σ⁻¹ *ᵥ w))) := by
  obtain ⟨s, -, hs⟩ := h.exists_integral_cexp_quadratic
  have h0 := hs 0
  simp only [dotProduct_zero, zero_dotProduct, add_zero, mul_zero, Complex.exp_zero,
    mul_one] at h0
  rw [hs, ← h0, siegelGaussIntegral]
  congr 2 with x
  ring_nf
end IsSiegel
end GlobalTheory
