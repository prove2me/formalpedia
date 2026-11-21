-- Prove2me | solution 1 for NewtonianLipschitz.candidateCoefficient_hasDerivAt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T03:39:58.914112+00:00
-- url     : https://prove2.me/submissions/caa1502f-ee1d-4eec-aca4-5783487e6f4b

module
public import Definitions.Def_NewtonianLipschitz_CubicCandidate
public import Definitions.Def_NewtonianLipschitz_ScalarMaximum
public import Theorems.Thm_NewtonianLipschitz_candidateCoefficient_eq
public import Theorems.Thm_NewtonianLipschitz_stationaryCubic_eq


set_option autoImplicit true
@[expose] public section
public section
open NewtonianLipschitz
namespace NewtonianLipschitz
theorem _root_.solution (x : ℝ) :
    HasDerivAt candidateCoefficient
      (6 * stationaryCubic x / (Real.sqrt (1 + 2 * x ^ 2)) ^ 7) x := by
  let r : ℝ := Real.sqrt (1 + 2 * x ^ 2)
  have hp : 0 < (1 : ℝ) + 2 * x ^ 2 := by positivity
  have hr : r ≠ 0 := by
    dsimp [r]
    exact ne_of_gt (Real.sqrt_pos.mpr hp)
  have hrsq : r ^ 2 = 1 + 2 * x ^ 2 := by
    dsimp [r]
    exact Real.sq_sqrt hp.le
  have hn :
      HasDerivAt (fun y : ℝ => 2 + 6 * y - 2 * y ^ 2)
        (6 - 4 * x) x := by
    convert
      (((hasDerivAt_id x).const_mul (6 : ℝ)).sub
        (((hasDerivAt_id x).pow 2).const_mul (2 : ℝ))).const_add
        (2 : ℝ) using 1 <;> first | rfl | (dsimp; ring) | (funext y; dsimp; ring)
  have hb :
      HasDerivAt (fun y : ℝ => 1 + 2 * y ^ 2)
        (4 * x) x := by
    convert
      (((hasDerivAt_id x).pow 2).const_mul (2 : ℝ)).const_add
        (1 : ℝ) using 1 <;> first | rfl | (dsimp; ring) | (funext y; dsimp; ring)
  have hs :
      HasDerivAt (fun y : ℝ => Real.sqrt (1 + 2 * y ^ 2))
        (4 * x / (2 * r)) x := by
    exact hb.sqrt (by positivity)
  have hd :
      HasDerivAt (fun y : ℝ =>
        (Real.sqrt (1 + 2 * y ^ 2)) ^ 5)
        (5 * r ^ 4 * (4 * x / (2 * r))) x := by
    convert! hs.pow 5 using 1 <;> ring
  have hf :
      candidateCoefficient =
        (fun y : ℝ => (2 + 6 * y - 2 * y ^ 2) /
          (Real.sqrt (1 + 2 * y ^ 2)) ^ 5) := by
    funext y
    exact candidateCoefficient_eq y
  have hquot :
      HasDerivAt candidateCoefficient
        (((6 - 4 * x) * r ^ 5 -
          (2 + 6 * x - 2 * x ^ 2) *
            (5 * r ^ 4 * (4 * x / (2 * r)))) /
          (r ^ 5) ^ 2) x := by
    rw [hf]
    convert! hn.div hd (pow_ne_zero 5 hr) using 1 <;> ring
  have hfrac :
      (((6 - 4 * x) * r ^ 5 -
        (2 + 6 * x - 2 * x ^ 2) *
          (5 * r ^ 4 * (4 * x / (2 * r)))) /
        (r ^ 5) ^ 2) =
      (((6 - 4 * x) * r ^ 2 -
        (2 + 6 * x - 2 * x ^ 2) * (10 * x)) / r ^ 7) := by
    field_simp [hr]
    ring
  have hpoly :
      (6 - 4 * x) * r ^ 2 -
        (2 + 6 * x - 2 * x ^ 2) * (10 * x) =
        6 * stationaryCubic x := by
    rw [hrsq, stationaryCubic_eq]
    ring
  rw [hfrac, hpoly] at hquot
  exact hquot
end NewtonianLipschitz
