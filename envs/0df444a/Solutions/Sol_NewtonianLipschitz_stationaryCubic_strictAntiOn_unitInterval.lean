-- Prove2me | solution 1 for NewtonianLipschitz.stationaryCubic_strictAntiOn_unitInterval
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T03:25:43.645822+00:00
-- url     : https://prove2.me/submissions/a4960a14-8164-4225-b115-717a9734e631

module
public import Mathlib
public import Definitions.Def_NewtonianLipschitz_CubicCandidate

set_option autoImplicit true
@[expose] public section
public section
open NewtonianLipschitz
namespace NewtonianLipschitz
theorem _root_.solution :
    StrictAntiOn stationaryCubic (Set.Icc (0 : ℝ) 1) := by
  intro x hx y hy hxy
  have hx0 : 0 ≤ x := hx.1
  have hx1 : x ≤ 1 := hx.2
  have hy0 : 0 ≤ y := hy.1
  have hy1 : y ≤ 1 := hy.2
  have hxx : 0 ≤ x * (1 - x) :=
    mul_nonneg hx0 (by linarith)
  have hyy : 0 ≤ y * (1 - y) :=
    mul_nonneg hy0 (by linarith)
  have hxy' : 0 ≤ x * (1 - y) :=
    mul_nonneg hx0 (by linarith)
  have hfactor :
      0 < 4 + 8 * (x + y) -
        2 * (x ^ 2 + x * y + y ^ 2) := by
    nlinarith [hxx, hyy, hxy']
  have hidentity :
      stationaryCubic x - stationaryCubic y =
        (y - x) *
          (4 + 8 * (x + y) -
            2 * (x ^ 2 + x * y + y ^ 2)) := by
    unfold stationaryCubic
    ring
  have hpositive : 0 < stationaryCubic x - stationaryCubic y := by
    rw [hidentity]
    exact mul_pos (sub_pos.mpr hxy) hfactor
  exact sub_pos.mp hpositive
end NewtonianLipschitz
