-- Prove2me | solution 1 for LandauExplore.theta_error_of_psi_error
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-11-01T00:28:54.274694+00:00
-- url     : https://prove2.me/submissions/a0a774ce-5b1b-425e-925c-69f8a1ca8507

/- Proof of the platform problem LandauExplore.theta_error_of_psi_error:
theta-error from a psi-error hypothesis (Landau step (B) conditional bridge).
Published with the user's explicit per-item tap on Oct 31, 2026.
The hypothesis psiError is the platform definition LandauExplore_psiError,
imported here; the statement is conditional and is not claimed unconditionally.
Proof body identical to the locally verified Sol_theta_error.lean, with the
in-file definition replaced by the platform import.
-/
import Mathlib.NumberTheory.Chebyshev
import Definitions.Def_LandauExplore_psiError

open LandauExplore

theorem solution {C : ℝ} (hψ : psiError C)
    {x : ℝ} (hx : 2 ≤ x) :
    |Chebyshev.theta x - x| ≤ (C * (Real.log x) ^ 2 + 2 * Real.log x) * Real.sqrt x := by
  have h1 : |Chebyshev.psi x - Chebyshev.theta x| ≤ 2 * Real.sqrt x * Real.log x :=
    Chebyshev.abs_psi_sub_theta_le_sqrt_mul_log (by linarith)
  have h2 : Chebyshev.theta x - x
      = (Chebyshev.theta x - Chebyshev.psi x) + (Chebyshev.psi x - x) := by ring
  have h3 : |Chebyshev.theta x - Chebyshev.psi x|
      = |Chebyshev.psi x - Chebyshev.theta x| := abs_sub_comm _ _
  calc |Chebyshev.theta x - x|
      ≤ |Chebyshev.theta x - Chebyshev.psi x| + |Chebyshev.psi x - x| := by
        rw [h2]; exact abs_add_le _ _
    _ ≤ 2 * Real.sqrt x * Real.log x + C * Real.sqrt x * (Real.log x) ^ 2 := by
        rw [h3]; exact add_le_add h1 (hψ x hx)
    _ = (C * (Real.log x) ^ 2 + 2 * Real.log x) * Real.sqrt x := by ring
