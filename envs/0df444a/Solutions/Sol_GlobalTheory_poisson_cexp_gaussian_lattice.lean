-- Prove2me | solution 1 for GlobalTheory.poisson_cexp_gaussian_lattice
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:55:29.67379+00:00
-- url     : https://prove2.me/submissions/0be016ac-faa0-4423-a382-69626277bd51

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_ExistsLinearIndependentNormLeSuccMin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_LatticeFourierOfContDiffFiniteDimensional
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_SummableLatticeExpNegPiMulNormSqDiv
import Theorems.Thm_GlobalTheory_summable_lattice_exp_neg_mul_norm_sq
import Theorems.Thm_GlobalTheory_exp_neg_mul_norm_add_sq_le
import Theorems.Thm_GlobalTheory_tsum_poisson_lattice
import Theorems.Thm_GlobalTheory_norm_cexp_neg_pi_mul_norm_sq_add
import Theorems.Thm_GlobalTheory_fourier_cexp_neg_pi_mul_norm_sq_add
import Theorems.Thm_GlobalTheory_summable_norm_lattice_cexp_gaussian
import Theorems.Thm_GlobalTheory_summable_norm_lattice_cexp_gaussian_div
import Theorems.Thm_GlobalTheory_norm_cexp_two_pi_I


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
theorem _root_.solution {b : ℂ} (hb : 0 < b.re) (w u : E) :
    (Summable fun x : L ↦ ‖Complex.exp (-π * b * ‖(x : E) + u‖ ^ 2 +
      2 * π * Complex.I * ⟪w, (x : E) + u⟫)‖) ∧
    (Summable fun y : dualLattice L ↦ ‖Complex.exp (-π * ‖(y : E) - w‖ ^ 2 / b) *
      Complex.exp (2 * π * Complex.I * ⟪(y : E), u⟫)‖) ∧
    ∑' x : L, Complex.exp (-π * b * ‖(x : E) + u‖ ^ 2 + 2 * π * Complex.I * ⟪w, (x : E) + u⟫) =
      (ZLattice.covolume L : ℂ)⁻¹ * b ^ (-(finrank ℝ E / 2 : ℂ)) *
        ∑' y : dualLattice L, Complex.exp (-π * ‖(y : E) - w‖ ^ 2 / b) *
          Complex.exp (2 * π * Complex.I * ⟪(y : E), u⟫) := by
  have hs := summable_norm_lattice_cexp_gaussian_div (dualLattice L) hb w
  refine ⟨summable_norm_lattice_cexp_gaussian L hb w u, ?_, ?_⟩
  · simpa only [norm_mul, norm_cexp_two_pi_I, mul_one] using hs
  have ha : 0 < π * b.re := mul_pos Real.pi_pos hb
  refine (tsum_poisson_lattice L
    (f := fun v : E ↦ Complex.exp (-π * b * ‖v‖ ^ 2 + 2 * π * Complex.I * ⟪w, v⟫)) (by fun_prop)
    (fun R ↦ ⟨_, (summable_lattice_exp_neg_mul_norm_sq L (half_pos ha)).mul_left
      (Real.exp (π * b.re * R ^ 2)), fun x v hv ↦ by
        rw [norm_cexp_neg_pi_mul_norm_sq_add]
        exact exp_neg_mul_norm_add_sq_le ha.le (x : E) hv⟩)
    (by simpa only [fourier_cexp_neg_pi_mul_norm_sq_add hb, norm_mul] using hs.mul_left _)
    u).trans ?_
  rw [Complex.real_smul, Complex.ofReal_inv,
    mul_assoc ((ZLattice.covolume L volume : ℝ) : ℂ)⁻¹]
  congr 1
  refine Eq.trans (tsum_congr fun y ↦ ?_) tsum_mul_left
  rw [fourier_cexp_neg_pi_mul_norm_sq_add hb, smul_eq_mul]
  ring
end GlobalTheory
