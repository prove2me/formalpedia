-- Prove2me | solution 1 for GlobalTheory.HeckeMellinProd.coord
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T17:32:23.361385+00:00
-- url     : https://prove2.me/submissions/5c0152f5-a2ec-4479-affa-478eda08d505

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_CompletedLStripBounds
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormWt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_GaussZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousTerm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_GammaIntegralExpSubstitutionRealLineStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IntegralHeckeMellinGaussIntegrandEqProdGamma
import Theorems.Thm_GlobalTheory_HeckeMellinProd_hmon_real_mul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField MeasureTheory
noncomputable section
open GlobalTheory GlobalTheory.HeckeMellinProd
namespace GlobalTheory.HeckeMellinProd
theorem _root_.solution (n : ℤ) (s : ℂ) (v : ℂ) (y : ℝ) :
    GlobalTheory.HeckeTheta.hmon n ((Real.exp (y / 2) : ℂ) * v) *
      Complex.exp ((-2 * Real.pi * ‖(Real.exp (y / 2) : ℂ) * v‖ ^ 2 : ℝ) : ℂ) * Complex.exp (s * (y : ℂ)) =
    GlobalTheory.HeckeTheta.hmon n v * fac (s + ((|n| : ℤ) : ℂ) / 2) (‖v‖ ^ 2) y := by
  rw [hmon_real_mul, fac]
  have h1 : ((Real.exp (y / 2) : ℝ) : ℂ) ^ n.natAbs = Complex.exp ((n.natAbs : ℂ) * (y / 2)) := by
    rw [Complex.ofReal_exp, ← Complex.exp_nat_mul]; push_cast; rfl
  have h2 : ‖(Real.exp (y / 2) : ℂ) * v‖ ^ 2 = Real.exp y * ‖v‖ ^ 2 := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), mul_pow,
      ← Real.exp_nat_mul]; congr 2; push_cast; ring
  have h3 : ((|n| : ℤ) : ℂ) = (n.natAbs : ℂ) := by
    rw [← Int.natCast_natAbs, Int.cast_natCast]
  rw [h1, h2, h3]
  have e1 : ((-2 * Real.pi * (Real.exp y * ‖v‖ ^ 2) : ℝ) : ℂ) = -(((2 * Real.pi * ‖v‖ ^ 2 * Real.exp y) : ℝ) : ℂ) := by
    push_cast; ring
  rw [e1]
  calc _ = GlobalTheory.HeckeTheta.hmon n v * (Complex.exp ((n.natAbs : ℂ) * (y / 2)) * Complex.exp (s * (y : ℂ))) *
        Complex.exp (-(((2 * Real.pi * ‖v‖ ^ 2 * Real.exp y) : ℝ) : ℂ)) := by ring
    _ = _ := by rw [← Complex.exp_add, mul_assoc]; congr 3; ring
end GlobalTheory.HeckeMellinProd
