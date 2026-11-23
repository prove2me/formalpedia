-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.DigammaLeft.sq_norm_cos
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:30:19.702633+00:00
-- url     : https://prove2.me/submissions/f2fd05d7-0db2-4811-a7a9-3ba0c3bf6ce0

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_DigammaLogBoundRightHalfPlaneStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_DigammaLogBoundLeftRegion

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.DigammaLeft
namespace GlobalTheory.CompanionTheory.DigammaLeft
theorem _root_.solution (z : ℂ) :
    ‖Complex.cos z‖ ^ 2 = Real.cos z.re ^ 2 + Real.sinh z.im ^ 2 := by
  rw [Complex.sq_norm, Complex.cos_eq, Complex.normSq_apply]
  simp only [← Complex.ofReal_sin, ← Complex.ofReal_cos, ← Complex.ofReal_sinh,
    ← Complex.ofReal_cosh, ← Complex.ofReal_mul]
  simp [Complex.sin_ofReal_re, Complex.cos_ofReal_re, Complex.sinh_ofReal_re]
  have h1 := Real.sin_sq_add_cos_sq z.re
  have h2 := Real.cosh_sq z.im
  linear_combination Real.cos z.re ^ 2 * h2 + Real.sinh z.im ^ 2 * h1
end GlobalTheory.CompanionTheory.DigammaLeft
