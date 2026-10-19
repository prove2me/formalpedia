-- Prove2me | solution 1 for MetricCodes.Boolean.addChannel_isometry
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:27.702855+00:00
-- url     : https://prove2.me/submissions/7c3b8357-08d0-4835-a331-e41ed1cf71ea

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open MetricCodes
noncomputable section
open scoped BigOperators Matrix
open MetricCodes.Boolean
variable {n : ℕ}
namespace MetricCodes.Boolean
theorem _root_.solution {i : ℕ} (hi : i < n)
    (f g : Function n) (hf : IsLevel i f) :
    coordinateDot (addChannel i f) (addChannel i g) = dot f g := by
  classical
  have hi' : (i : ℝ) < (n : ℝ) := by exact_mod_cast hi
  have hpos : 0 < (n : ℝ) - (i : ℝ) := sub_pos.mpr hi'
  have hs : Real.sqrt ((n : ℝ) - (i : ℝ)) ≠ 0 :=
    (Real.sqrt_pos.2 hpos).ne'
  have hsqr :
      Real.sqrt ((n : ℝ) - (i : ℝ)) *
          Real.sqrt ((n : ℝ) - (i : ℝ)) = (n : ℝ) - (i : ℝ) :=
    Real.mul_self_sqrt hpos.le
  have hscalar :
      (Real.sqrt ((n : ℝ) - (i : ℝ)))⁻¹ *
          (Real.sqrt ((n : ℝ) - (i : ℝ)))⁻¹ *
            ((n : ℝ) - (i : ℝ)) = 1 := by
    calc
      (Real.sqrt ((n : ℝ) - (i : ℝ)))⁻¹ *
          (Real.sqrt ((n : ℝ) - (i : ℝ)))⁻¹ *
            ((n : ℝ) - (i : ℝ)) =
        (Real.sqrt ((n : ℝ) - (i : ℝ)))⁻¹ *
          (Real.sqrt ((n : ℝ) - (i : ℝ)))⁻¹ *
            (Real.sqrt ((n : ℝ) - (i : ℝ)) *
              Real.sqrt ((n : ℝ) - (i : ℝ))) := by rw [hsqr]
      _ = 1 := by field_simp [hs]
  calc
    coordinateDot (addChannel i f) (addChannel i g) =
        ((Real.sqrt ((n : ℝ) - (i : ℝ)))⁻¹ *
          (Real.sqrt ((n : ℝ) - (i : ℝ)))⁻¹) *
            (∑ a : Fin n, dot (raiseAt a f) (raiseAt a g)) := by
      simp only [coordinateDot, addChannel, dot_smul_left,
        dot_smul_right, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      ring
    _ = ((Real.sqrt ((n : ℝ) - (i : ℝ)))⁻¹ *
          (Real.sqrt ((n : ℝ) - (i : ℝ)))⁻¹) *
            (((n : ℝ) - (i : ℝ)) * dot f g) := by
      rw [sum_dot_raiseAt_of_level f g hf]
    _ = ((Real.sqrt ((n : ℝ) - (i : ℝ)))⁻¹ *
          (Real.sqrt ((n : ℝ) - (i : ℝ)))⁻¹ *
            ((n : ℝ) - (i : ℝ))) * dot f g := by ring
    _ = dot f g := by rw [hscalar, one_mul]
end MetricCodes.Boolean
