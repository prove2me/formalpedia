-- Prove2me | solution 1 for Kyprianou.Ch04.kw48_grid_gain_uniform_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T00:37:33.714955+00:00
-- url     : https://prove2.me/submissions/7c03ca36-3966-4067-8c4f-761fdf4bbcbc

import Mathlib
import Definitions.Def_Kyprianou_Ch04_KW48Processes
import Theorems.Thm_Kyprianou_Ch04_kw48_correction_grid_norm_bound
import Theorems.Thm_Kyprianou_Ch04_kw48_discrete_product_summation
import Theorems.Thm_Kyprianou_Ch04_kw48_exp_product
import Theorems.Thm_Kyprianou_Ch04_kw48_norm_Z
import Theorems.Thm_AvramDividend_Classical_runningSup_monotone_and_path_le
open MeasureTheory ProbabilityTheory AvramDividend.Classical Kyprianou.Ch04.KW48
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Every finite predictable grid gain is dominated by twice the common
integrable envelope, regardless of its mesh or number of cells. -/
theorem solution {Ω : Type} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {F : Filtration NNReal mΩ}
    (L : SpectrallyNegativeLevy P F) (Psi : Real → Complex)
    (alpha beta : Real) (T : NNReal) (u : Nat → NNReal) (N : Nat)
    (hu : Monotone u) (hT : ∀ i, u i ≤ T) (w : Ω) :
    ‖Q L Psi alpha beta u N w‖ ≤ 2*envelope L Psi alpha beta T w := by
  let K := ‖Psi alpha‖*(T:Real)
  let V := |beta-alpha| * runningSup L T w+K
  have hK : 0 ≤ K := by positivity
  have hU0 : 0 ≤ runningSup L 0 w := by
    simpa only [L.X_zero] using (runningSup_monotone_and_path_le L w).2 0
  have hUT := hU0.trans ((runningSup_monotone_and_path_le L w).1 (show 0 ≤ T from zero_le))
  have hV : 0 ≤ V := add_nonneg (mul_nonneg (abs_nonneg _) hUT) hK
  have h := Kyprianou.Ch04.kw48_discrete_product_summation
    (fun i => E L Psi alpha (u i) w)
    (fun i => H L Psi alpha beta (u i) w) N
  rw [Kyprianou.Ch04.kw48_exp_product,Kyprianou.Ch04.kw48_exp_product] at h
  change Q L Psi alpha beta u N w+C L Psi alpha beta u N w =
    Z L alpha beta (u N) w-Z L alpha beta (u 0) w at h
  have hEq : Q L Psi alpha beta u N w =
      Z L alpha beta (u N) w-Z L alpha beta (u 0) w-C L Psi alpha beta u N w := by
    linear_combination h
  have hC : ‖C L Psi alpha beta u N w‖ ≤ 2*Real.exp K*V :=
    Kyprianou.Ch04.kw48_correction_grid_norm_bound L Psi alpha beta T u N hu hT w
  rw [hEq]
  calc
    _ ≤ ‖Z L alpha beta (u N) w-Z L alpha beta (u 0) w‖+
        ‖C L Psi alpha beta u N w‖ := norm_sub_le _ _
    _ ≤ ‖Z L alpha beta (u N) w‖+‖Z L alpha beta (u 0) w‖+
        2*Real.exp K*V := add_le_add (norm_sub_le _ _) hC
    _ ≤ 2*envelope L Psi alpha beta T w := by
      rw [Kyprianou.Ch04.kw48_norm_Z,Kyprianou.Ch04.kw48_norm_Z]
      have hExp : Real.exp K ≤ Real.exp (2*K) := Real.exp_le_exp.mpr (by linarith)
      have hMul := mul_le_mul_of_nonneg_right hExp hV
      change (1:Real)+1+2*Real.exp K*V ≤
        2*(2+Real.exp (2*‖Psi alpha‖*(T:Real))*V)
      rw [show 2*‖Psi alpha‖*(T:Real) = 2*K by dsimp [K]; ring]
      linarith
