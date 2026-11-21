-- Prove2me | solution 1 for NewtonianLipschitz.lateralRowNumerator_le_dominant
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T03:31:34.541189+00:00
-- url     : https://prove2.me/submissions/ff7b21bc-49db-406e-bc55-92d0d7768f43

module
public import Mathlib
public import Definitions.Def_NewtonianLipschitz_JacobianRows

set_option autoImplicit true
@[expose] public section
public section
open NewtonianLipschitz
namespace NewtonianLipschitz
theorem _root_.solution
    (u v : ℝ) (hu0 : 0 ≤ u) (hu1 : u ≤ 1)
    (hv0 : 0 ≤ v) (hv1 : v ≤ 1) :
    lateralRowNumerator u v ≤ dominantRowNumerator u v := by
  have hleft : 0 ≤ (1 - v) * (1 + u ^ 2) :=
    mul_nonneg (by linarith) (by positivity)
  have hmiddle : 0 ≤ v * ((1 - u) * (2 - u)) :=
    mul_nonneg hv0 (mul_nonneg (by linarith) (by linarith))
  have hright : 0 ≤ v * (1 - v) :=
    mul_nonneg hv0 (by linarith)
  have hother : 0 ≤ (1 - u) * (1 + u + v) :=
    mul_nonneg (by linarith) (by linarith)
  have habs :
      |2 * u ^ 2 - 1 - v ^ 2| ≤
        2 - u ^ 2 - v ^ 2 + 3 * (u + v) - 3 * u * (1 + v) := by
    apply abs_le.mpr
    constructor
    · nlinarith [hleft, hmiddle, hright]
    · nlinarith [hother]
  unfold dominantRowNumerator lateralRowNumerator
  linarith
end NewtonianLipschitz
